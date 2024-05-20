module Hacl.Spec.NTT.CT

open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod
module Fermat = FStar.Math.Fermat
module Euclid = FStar.Math.Euclid
module ML = FStar.Math.Lemmas
open Hacl.Spec.MLkem.Poly
open Hacl.Spec.MLkem.Zq
open Hacl.Spec.MLkem.Sums
open Hacl.Spec.MLkem.PowModInt
open Hacl.Spec.MLkem.Unity

open Hacl.Spec.MLkem.NTT

(* 
In Cooley-Tukey, we compute the NTT of a n element polynomial by taking 
the NTT of the even and odd parts of the polynomial, and then combining 
them. This proof shows that splitting and recombining as Cooley-Tukey 
specifies matches the specification of the NTT that we have proven correct.
*)

val poly_even:
    #n:size_nat
  -> f:lpoly n
  -> lpoly (n / 2)
let even #n f = createi (n / 2) (fun i -> poly_index #n f (2 * i))

val poly_odd:
    #n:size_nat
  -> f:lpoly n
  -> lpoly (n / 2)
let odd #n f = createi (n / 2) (fun i -> poly_index #n f (2 * i + 1))

let power_of_two_div_two (n:power_of_two): Lemma (requires n >= 2) (ensures is_power_of_two (n / 2)) = admit()
  // Classical.exists_elim (is_power_of_two (n / 2)) () (fun x -> ())

// The kth term of the NTT can be computed as a sum of two n/2 NTTs
// The same two n/2 NTTs can be used to compute the k+n/2th term
val ntt_ct_kth_term:
    #n:power_of_two
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> zq
let rec ntt_ct_kth_term #n #psi f k =
  if n = 1 then poly_index #n f k
  else if k < 0 || k >= n then 0 
  else if k < n / 2 then begin
    power_of_two_div_two n;
    ntt_ct_kth_term #(n / 2) #(pow psi 2) (even f) k
      +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow psi 2) (odd f) k
  end else begin
    power_of_two_div_two n;
    let k' = k - n / 2 in  
    ntt_ct_kth_term #(n / 2) #(pow psi 2) (even f) k'
      +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow psi 2) (odd f) k'
  end

// val ntt_ct_kth_term:
//     #n:power_of_two
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int
//   -> zq
// let ntt_ct_kth_term #n #psi f k = 
//   if k < 0 || k >= n then 0 
//   else if k < n / 2 then begin
//     sum_of_zqs 0 (n / 2) (fun i -> pow_mod_int #q psi (4 * i * k + 2 * i) %* poly_index f (2 * i))
//       +% pow_mod_int #q psi (2 * k + 1) %* sum_of_zqs 0 (n/2) (fun i -> pow_mod_int #q psi (4 * i * k + 2 * i) %* poly_index f (2 * i + 1)) 
//   end else begin
//     let k' = k - n / 2 in  
//     sum_of_zqs 0 (n / 2) (fun i -> pow_mod_int #q psi (4 * i * k' + 2 * i) %* poly_index f (2 * i))
//       -% pow_mod_int #q psi (2 * k' + 1) %* sum_of_zqs 0 (n/2) (fun i -> pow_mod_int #q psi (4 * i * k' + 2 * i) %* poly_index f (2 * i + 1)) 
//   end

let ntt_ct (#n:power_of_two) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) =
  createi n (fun k -> ntt_ct_kth_term #n #psi f k)


val ntt_ct_lemma (#n:power_of_two) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (i:int): 
  Lemma (poly_index (ntt_ct #n #psi f) i == ntt_ct_kth_term #n #psi f i)
  [SMTPat (poly_index (ntt_ct #n #psi f) i)]
let ntt_ct_lemma #n f i = ()

val cooley_tukey_ok:
    #n:power_of_two
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> Lemma (ntt #n #psi f = ntt_ct #n #psi f)
