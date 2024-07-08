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
let poly_even #n f = createi (n / 2) (fun i -> poly_index #n f (2 * i))

val poly_even_to_poly_idx:
    #n:size_nat
  -> f:lpoly n
  -> i:nat{i < n / 2}
  -> Lemma (poly_index #n f (2 * i) == poly_index (poly_even #n f) i)
let poly_even_to_poly_idx #n f i = ()

val poly_odd:
    #n:size_nat
  -> f:lpoly n
  -> lpoly (n / 2)
let poly_odd #n f = createi (n / 2) (fun i -> poly_index #n f (2 * i + 1))

val poly_odd_to_poly_idx:
    #n:size_nat 
  -> f:lpoly n 
  -> i:nat{i < n / 2}
  -> Lemma (forall i. poly_index #n f (2 * i + 1) == poly_index (poly_odd #n f) i)
let poly_odd_to_poly_idx #n f i = ()

let power_of_two_div_two (n:power_of_two): Lemma (requires n >= 2) (ensures is_power_of_two (n / 2)) = admit()
let power_of_two_even (n:power_of_two): Lemma (requires n >= 2) (ensures n % 2 == 0) = ()

// The kth term of the NTT can be computed as a sum of two n/2 NTTs
// The same two n/2 NTTs can be used to compute the k+n/2th term
val ntt_ct_kth_term:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> zq
let rec ntt_ct_kth_term #n #psi f k =
  if n = 1 then poly_index #n f k
  else if k < 0 || k >= n then 0 
  else if k < n / 2 then begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k
      +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k
  end else begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    let k' = k - n / 2 in  
    ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
      -% pow_mod_int #q psi (2 * k' + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k'
  end

let ntt_ct (#n:power_of_two{2 * n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) =
  createi n (fun k -> ntt_ct_kth_term #n #psi f k)

val ntt_ct_lemma (#n:power_of_two{2 * n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (i:int): 
  Lemma (poly_index (ntt_ct #n #psi f) i == ntt_ct_kth_term #n #psi f i)
  [SMTPat (poly_index (ntt_ct #n #psi f) i)]
let ntt_ct_lemma #n f i = ()

val cooley_tukey_kth_term_ok_base:
    #n:power_of_two{n = 1}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k >= 0 && k < n}
  -> Lemma (ntt_kth_term #n #psi f k == ntt_ct_kth_term #n #psi f k)
let cooley_tukey_kth_term_ok_base #n #psi f k = 
  calc (==) {
    ntt_kth_term #n #psi f k;
    (==) {}
    sum_of_zqs 0 1 (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))));
    (==) {unfold_sum 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1)))); 
          lemma_sum_none 0 (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))))}
    (poly_index f 0) %* (pow_mod_int #q psi (0 * (2 * k + 1)));
    (==) {}
    (poly_index f 0) %* (pow_mod_int #q psi 0);
    (==) {lemma_pow_mod_int_pow0 psi}
    poly_index f 0;
    (==) {}
    ntt_ct_kth_term #n #psi f k;
  }

val cooley_tukey_kth_term_rewrite:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
            == sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))))
let cooley_tukey_kth_term_rewrite #n #psi f k = 
  let aux (j:nat{j < n / 2}): Lemma ((poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))) == 
                          ((poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))) = 
    poly_even_to_poly_idx f j in
  Classical.forall_intro (aux)

val cooley_tukey_kth_term_rewrite_odd:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1))))
            == sum_of_zqs 0 (n/2) (fun j -> (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))))
let cooley_tukey_kth_term_rewrite_odd #n #psi f k = 
  let aux (j:nat{j < n / 2}): Lemma ((poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1))) == 
                          (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))) = 
    calc (==) {
      (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1)));
      (==) {poly_odd_to_poly_idx f j}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1)));
      (==) {ML.distributivity_add_left (2 * j) 1 (2 * k + 1)}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1) + (2 * k + 1)));
      (==) {lemma_pow_mod_int_add #q psi ((2 * j) * (2 * k + 1)) (2 * k + 1)}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)) %* pow_mod_int #q psi (2 * k + 1));
      (==) {lemma_mul_mod_comm (pow_mod_int #q psi ((2 * j) * (2 * k + 1))) (pow_mod_int #q psi (2 * k + 1))}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi (2 * k + 1) %* pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
      (==) {lemma_mul_mod_assoc (poly_index (poly_odd f) j) (pow_mod_int #q psi (2 * k + 1)) (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))}
      (poly_index (poly_odd f) j) %* pow_mod_int #q psi (2 * k + 1) %* pow_mod_int #q psi ((2 * j) * (2 * k + 1));
    } in
  Classical.forall_intro (aux)

val cooley_tukey_kth_term_rewrite_odd_mul:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (sum_of_zqs 0 (n/2) (fun j -> (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
            == (pow_mod_int #q psi (2 * k + 1)) %* sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))))
let cooley_tukey_kth_term_rewrite_odd_mul #n #psi f k =
  sum_mul_lemma (pow_mod_int #q psi (2 * k + 1)) 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))

val lemma_collapse_ntt_half_even:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
        == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k)
let lemma_collapse_ntt_half_even #n #psi f k =
  let aux (j:nat{j < n/2}): Lemma ((poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))
                                == (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)))) =
    calc (==) {
      (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
      (==) {ML.paren_mul_right 2 j (2 * k +1)}
      (poly_index (poly_even f) j) %* (pow_mod_int #q psi (2 * (j * (2 * k + 1))));
      (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
      (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
    } in
  Classical.forall_intro (aux)
  
val lemma_collapse_ntt_half_odd:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
        == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let lemma_collapse_ntt_half_odd #n #psi f k =
  let aux (j:nat{j < n/2}): Lemma ((poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))
                                == (poly_index (poly_odd f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)))) =
    calc (==) {
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
      (==) {ML.paren_mul_right 2 j (2 * k +1)}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi (2 * (j * (2 * k + 1))));
      (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
    } in
  Classical.forall_intro (aux)

val cooley_tukey_kth_term_ok_rewrite:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures ntt_kth_term #n #psi f k == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
                                            +% pow_mod_int #q psi (2 * k + 1) 
                                              %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let cooley_tukey_kth_term_ok_rewrite #n #psi f k = 
  power_of_two_even n;
  calc (==) {
    ntt_kth_term #n #psi f k;
    (==) {}
    sum_of_zqs 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))));
    (==) {lemma_sum_split_parity n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))))}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
      +% sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1))));
    (==) {cooley_tukey_kth_term_rewrite #n #psi f k;
          cooley_tukey_kth_term_rewrite_odd #n #psi f k}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
      +% sum_of_zqs 0 (n/2) (fun j -> (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
    (==) {cooley_tukey_kth_term_rewrite_odd_mul #n #psi f k}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
      +% (pow_mod_int #q psi (2 * k + 1)) %* sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
    (==) {lemma_collapse_ntt_half_even #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% (pow_mod_int #q psi (2 * k + 1)) %* sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
    (==) {lemma_collapse_ntt_half_odd #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
  }

val ct_second_half_psi_sym_rearr_exp1:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma ((2 * j) * (2 * (k + n / 2) + 1)
          == (n * (2 * j)) + (2 * j * 2 * k) + (2 * j))
let ct_second_half_psi_sym_rearr_exp1 #n #psi k j = 
  calc (==) {
    ((2 * j) * (2 * (k + n / 2) + 1));
    (==) {}
    ((2 * j) * (2 * k + n + 1));
    (==) {ML.distributivity_add_right (2 * j) (2 * k + n) 1}
    ((2 * j) * (2 * k + n) + (2 * j));
    (==) {ML.distributivity_add_right (2 * j) (2 * k) n}
    ((2 * j) * (2 * k) + (2 * j) * n + (2 * j));
    (==) {ML.paren_mul_right (2 * j) 2 k}
    ((2 * j * 2 * k) + (2 * j * n) + (2 * j));
    (==) {ML.swap_mul (2 * j) n}
    ((2 * j * 2 * k) + (n * (2 * j)) + (2 * j));
    (==) {}
    ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j));
  }

#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
val ct_second_half_psi_sym_rearr_base:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma (pow_mod_int #q psi ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j))
            == (pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j))))
let ct_second_half_psi_sym_rearr_base #n #psi k j = 
  assert ((-1) % q = q - 1);
  calc (==) {
    pow_mod_int #q psi ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_add #q psi (n * (2 * j)) ((2 * j * 2 * k) + (2 * j))}
    pow_mod_int #q psi (n * (2 * j)) %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_mul #q psi n (2 * j)}
    pow_mod_int #q (pow_mod_int #q psi n) (2 * j) %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
    pow_mod_int #q ((-1) % q) (2 * j) %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_mul #q ((-1) % q) 2 j}
    pow_mod_int #q (pow_mod_int #q (q - 1) 2) j %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q 2}
    pow_mod_int #q (pow_mod_int_neg_one #q 2) j %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {}
    pow_mod_int #q (1) j %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_one #q j}
    1 %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {}
    1 * pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j)) % q;
  }
  
// Symmetry of root of unity
#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
val ct_second_half_psi_sym:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))
         == pow_mod_int #q psi ((2 * j) * (2 * k + 1)))
let ct_second_half_psi_sym #n #psi k j = 
  calc (==) {
    pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1));
    (==) {ct_second_half_psi_sym_rearr_exp1 #n #psi k j}
    pow_mod_int #q psi ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j));
    (==) {ct_second_half_psi_sym_rearr_base #n #psi k j}
    pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {ML.paren_mul_right (2 * j) 2 k}
    pow_mod_int #q psi ((2 * j * (2 * k)) + (2 * j));
    (==) {ML.distributivity_add_right (2 * j) (2 * k) 1}
    pow_mod_int #q psi ((2 * j) * (2 * k + 1));
  }
  
val cooley_tukey_kth_term_ok_rewrite_second_half_t1_aux:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma ((poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)))
          == (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t1_aux #n #psi f k j = 
  ct_second_half_psi_sym #n #psi k j;
  poly_even_to_poly_idx #n f j;
  assert ((poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)))
        == (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
  calc (==) {
    (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
    (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
    (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t1':
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))))
            == sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int (pow_mod_int #q psi 2) (j * (2 * k + 1)))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t1' #n #psi f k =
  Classical.forall_intro (cooley_tukey_kth_term_ok_rewrite_second_half_t1_aux #n #psi f k)

val cooley_tukey_kth_term_ok_rewrite_second_half_t1:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))))
            == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k)
let cooley_tukey_kth_term_ok_rewrite_second_half_t1 #n #psi f k =
  power_of_two_div_two n;
  nth_root_squared_is_primitive_root #q (2 * n) psi;
  calc (==) {
    sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))));
    (==) {cooley_tukey_kth_term_ok_rewrite_second_half_t1' #n #psi f k}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int (pow_mod_int #q psi 2) (j * (2 * k + 1))));
    (==) {}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k;
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t2_aux:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1)))
             == pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t2_aux #n #psi f k j = 
  assert (2 * (k + n / 2) = 2 * k + n);
  calc (==) {
    (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1)));
    (==) {ML.distributivity_add_left (2 * j) 1 (2 * k + n + 1)}
    (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1) + (2 * (k + n / 2) + 1)));
    (==) {lemma_pow_mod_int_add #q psi ((2 * j) * (2 * (k + n / 2) + 1)) (2 * (k + n / 2) + 1)}
    (pow_mod_int #q psi (2 * j * (2 * (k + n / 2) + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1));
  };
  assert ((poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1)))
        == (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1)));
  calc (==) {
    (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1));
    (==) {lemma_mul_mod_comm (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))) (pow_mod_int #q psi (2 * (k + n / 2) + 1))}
    (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))));
    (==) {lemma_mul_mod_assoc (poly_index f (2 * j + 1)) (pow_mod_int #q psi (2 * (k + n / 2) + 1)) (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)))}
    (poly_index f (2 * j + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)));
    (==) {lemma_mul_mod_comm (poly_index f (2 * j + 1)) (pow_mod_int #q psi (2 * (k + n / 2) + 1))}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)));
    (==) {ct_second_half_psi_sym #n #psi k j}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
    (==) {ML.paren_mul_right 2 j (2 * k + 1)}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi (2 * (j * (2 * k + 1))));
    (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t2':
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))))
            == pow_mod_int #q psi (2 * (k + n / 2) + 1) 
            %* sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t2' #n #psi f k =
  Classical.forall_intro (Classical.move_requires (cooley_tukey_kth_term_ok_rewrite_second_half_t2_aux #n #psi f k));
  sum_mul_lemma (pow_mod_int #q psi (2 * (k + n / 2) + 1)) 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1))))

val psi_symmetry_negates:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> Lemma (pow_mod_int #q psi (2 * k + n + 1) == ((-1) % q) %* pow_mod_int #q psi (2 * k + 1))
let psi_symmetry_negates #n #psi k =
  calc (==) {
    pow_mod_int #q psi (2 * k + n + 1);
    (==) {}
    pow_mod_int #q psi (n + 2 * k + 1);
    (==) {lemma_pow_mod_int_add #q psi n (2 * k + 1)}
    pow_mod_int #q psi n %* pow_mod_int #q psi (2 * k + 1);
    (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
    ((-1) % q) %* pow_mod_int #q psi (2 * k + 1);
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t2:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))))
            == ((-1) % q) %* (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let cooley_tukey_kth_term_ok_rewrite_second_half_t2 #n #psi f k =
  cooley_tukey_kth_term_ok_rewrite_second_half_t2' #n #psi f k;
  psi_symmetry_negates #n #psi k

val neg_to_minus:
    a:zq
  -> b:zq
  -> Lemma (a +% ((-1) % q) %* b == a -% b)
let neg_to_minus a b = ()

#reset-options "--z3rlimit 10 --fuel 1 --ifuel 0"
val cooley_tukey_kth_term_ok_rewrite_second_half:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures ntt_kth_term #n #psi f (k + n / 2) == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
                                                      -% pow_mod_int #q psi (2 * k + 1)
                                                          %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let cooley_tukey_kth_term_ok_rewrite_second_half #n #psi f k = 
  power_of_two_even n;
  calc (==) {
    ntt_kth_term #n #psi f (k + n / 2);
    (==) {}
    sum_of_zqs 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * (k + n / 2) + 1))));
    (==) {lemma_sum_split_parity n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * (k + n / 2) + 1))))}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))))
      +% sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))));
    (==) {cooley_tukey_kth_term_ok_rewrite_second_half_t1 #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))));
    (==) {cooley_tukey_kth_term_ok_rewrite_second_half_t2 #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% ((-1) % q) %* (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
    (==) {neg_to_minus (ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k)
                       ((pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      -% pow_mod_int #q psi (2 * k + 1) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
  }


val cooley_tukey_kth_term_ok:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (ntt_kth_term #n #psi f k == ntt_ct_kth_term #n #psi f k)
let rec cooley_tukey_kth_term_ok #n #psi f k =
  if k < 0 || k >= n then ()
  else if n = 1 then cooley_tukey_kth_term_ok_base #n #psi f k
  else if k < n / 2 then begin 
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    calc (==) {
      ntt_ct_kth_term #n #psi f k;
      (==) {}
      ntt_ct_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
        +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_even f) k}
      ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
        +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_odd f) k}
      ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
        +% (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
      (==) {cooley_tukey_kth_term_ok_rewrite #n #psi f k}
      ntt_kth_term #n #psi f k;
    }
  end else begin 
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    let k' = k - n / 2 in
    calc (==) {
      ntt_ct_kth_term #n #psi f k;
      (==) {}
      ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
        -% pow_mod_int #q psi (2 * k' + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k';
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_even f) k'}
      ntt_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
        -% pow_mod_int #q psi (2 * k' + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k';
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_odd f) k'}
      ntt_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
        -% pow_mod_int #q psi (2 * k' + 1) %* ntt_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k';
      (==) {cooley_tukey_kth_term_ok_rewrite_second_half #n #psi f k'}
      ntt_kth_term #n #psi f k;
    }
  end

val cooley_tukey_ok:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> Lemma (equal (ntt #n #psi f) (ntt_ct #n #psi f))
let cooley_tukey_ok #n #psi f = 
  Classical.forall_intro (cooley_tukey_kth_term_ok #n #psi f)
