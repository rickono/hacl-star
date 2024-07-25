module Hacl.Spec.MLkem.NTT
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

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"

// let bit7 = lseq bool 7

// let bitrev7 (bits:bit7): bit7 =
//   createi 7 (fun i -> index bits (6 - i))

// let bit (b:bool): b:nat{b = 0 || b = 1} = if b then 1 else 0

// let bit7_v (bits:bit7): r:nat{r < 128} =
//   let r0 = bit (index bits 0) in 
//   let r1 = bit (index bits 1) in
//   let r2 = bit (index bits 2) in
//   let r3 = bit (index bits 3) in
//   let r4 = bit (index bits 4) in
//   let r5 = bit (index bits 5) in
//   let r6 = bit (index bits 6) in
//   r0 + 2 * r1 + 4 * r2 + 8 * r3 + 16 * r4 + 32 * r5 + 64 * r6

// let bitrev_ok (bits:bit7): Lemma 
//   (requires True) 
//   (ensures (
//     let rev = bitrev7 bits in
//     forall (i:nat{ i < 7 }). (index bits i = index rev (6 - i))
//   )) = ()

// let get_bit (bits:nat{ bits < 128}) (i:nat{i < 7}): b:nat{b = 0 || b = 1 } =
//   bits / (pow2 i) % 2

// let bitsequence (i:nat{ i < 128}): bit7 =
//   createi 7 (fun j -> (get_bit i j) = 1)

// let bitrev7_int (bits:nat{bits < 128}): result:nat{result < 128} =
//   bit7_v (bitrev7 (bitsequence bits))

// Types specifying the possible values of the length and start parameters
// type len_t = l:nat{l = 2 || l = 4 || l = 8 || l = 16 || l = 32 || l = 64 || l = 128}
// type start_t (len:len_t) = s:nat{s % (2*len) = 0 && s < 256}
let is_power_of_two (n:size_nat) = exists x. pow2 x = n
type power_of_two = n:size_nat{is_power_of_two n}

val mul_quotient_ring_kth_term:
    #n:power_of_two
  -> f:lpoly n
  -> g:lpoly n
  -> k:int
  -> zq
let mul_quotient_ring_kth_term #n f g k =
  if k < 0 || k >= n then 0
  else sum_of_zqs 0 n (fun j -> (pow_mod_int_neg_one ((k - j) / n)) %* ((poly_index f j) %* poly_index g ((k - j) % n)))

val mul_quotient_ring:
    #n:power_of_two
  -> f:lpoly n
  -> g:lpoly n
  -> lpoly n
let mul_quotient_ring #n f g = 
  createi n (fun k -> mul_quotient_ring_kth_term #n f g k)

val mul_quotient_ring_lemma:
    #n:power_of_two
  -> f:lpoly n
  -> g:lpoly n
  -> k:int
  -> Lemma (poly_index (mul_quotient_ring f g) k == mul_quotient_ring_kth_term f g k)
let mul_quotient_ring_lemma f g k = ()

val ntt_kth_term:
    #n:power_of_two
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> zq
let ntt_kth_term #n #psi f k = 
  if k < 0 || k >= n then 0 
  else sum_of_zqs 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))))

val ntt_kth_term_lemma:
    #n:power_of_two
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma ((ntt_kth_term #n #psi f k) == sum_of_zqs 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1)))))
  [SMTPat (ntt_kth_term #n #psi f k)] 
let ntt_kth_term_lemma #n f k = ()

let ntt (#n:power_of_two) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) =
  createi n (fun k -> ntt_kth_term #n #psi f k)

val ntt_lemma (#n:power_of_two) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (i:int): 
  Lemma (poly_index (ntt #n #psi f) i == ntt_kth_term #n #psi f i)
  [SMTPat (poly_index (ntt #n #psi f) i)]
let ntt_lemma #n f i = ()


val intt_kth_term:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> zq
let intt_kth_term #n #psi f k =
  if k < 0 || k >= n then 0
  else pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))

let intt (#n:power_of_two{n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) = createi n (fun k -> intt_kth_term #n #psi f k)

val intt_lemma (#n:power_of_two{n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (i:int): 
  Lemma (poly_index (intt #n #psi f) i == intt_kth_term #n #psi f i)
  [SMTPat (poly_index (intt #n #psi f) i)]
let intt_lemma f i = ()

// INTT(NTT(f))_k
val intt_ntt_kth_term:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> zq
let intt_ntt_kth_term #n #psi f k = (intt #n #psi (ntt #n #psi f)).[k]

val intt_ntt_is_id_kth_term_0_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> Lemma 
       (mul_zq (ntt_kth_term #n #psi f i) (pow_mod_int #q psi (-k * (2 * i + 1)))
       == mul_zq (sum_of_zqs 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * i + 1))))) (pow_mod_int #q psi (-k * (2 * i + 1))))
let intt_ntt_is_id_kth_term_0_aux f k i = ()

val intt_ntt_is_id_kth_term_0:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))))) %* (pow_mod_int #q psi (-k * (2 * i + 1)))))
let intt_ntt_is_id_kth_term_0 #n #psi f k =
  Classical.forall_intro (intt_ntt_is_id_kth_term_0_aux #n #psi f k)

val intt_ntt_is_id_kth_term_1_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> Lemma 
      ((sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))))) %* (pow_mod_int #q psi (-k * (2 * i + 1)))
    == (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))) %* (pow_mod_int #q psi (-k * (2 * i + 1))))))
let intt_ntt_is_id_kth_term_1_aux #n #psi f k i =
  sum_mul_lemma (pow_mod_int #q psi (-k * (2 * i + 1))) 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))))

val intt_ntt_is_id_kth_term_1:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))) %* (pow_mod_int #q psi (-k * (2 * i + 1)))))))
let intt_ntt_is_id_kth_term_1 #n #psi f k = Classical.forall_intro (intt_ntt_is_id_kth_term_1_aux #n #psi f k)

val intt_ntt_is_id_kth_term_2_inner_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> j:int{0 <= j && j < n}
  -> Lemma ((poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))) %* (pow_mod_int #q psi (-k * (2 * i + 1)))
          == (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i + 1))))
let intt_ntt_is_id_kth_term_2_inner_aux #n #psi f k i j =
  calc (==) {
    (poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))) %* (pow_mod_int #q psi (-k * (2 * i + 1)));
    (==) {}
    (poly_index f j) %* ((pow_mod_int #q psi (j * (2 * i + 1))) %* (pow_mod_int #q psi (-k * (2 * i + 1))));
    (==) {lemma_pow_mod_int_add #q psi (j * (2 * i + 1)) (-k * (2 * i + 1))}
    (poly_index f j) %* (pow_mod_int #q psi ((j * (2 * i + 1)) + (-k * (2 * i + 1))));
    (==) {}
    (poly_index f j) %* (pow_mod_int #q psi (((j - k) * (2 * i + 1))));
  }

val intt_ntt_is_id_kth_term_2_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> Lemma ((sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j * (2 * i + 1))) %* (pow_mod_int #q psi (-k * (2 * i + 1))))) 
         == (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i + 1))))))
let intt_ntt_is_id_kth_term_2_aux #n #psi f k i = 
  Classical.forall_intro (intt_ntt_is_id_kth_term_2_inner_aux #n #psi f k i)

val intt_ntt_is_id_kth_term_2:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i + 1)))))))
let intt_ntt_is_id_kth_term_2 #n #psi f k = 
  intt_ntt_is_id_kth_term_1 #n #psi f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_2_aux #n #psi f k)

val intt_ntt_is_id_kth_term_3_inner_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> i:int{i < n}
  -> j:int{j < n}
  -> Lemma ((poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i + 1)))
          == (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k)))
let intt_ntt_is_id_kth_term_3_inner_aux #n #psi f k i j =
  calc (==) {
    (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i + 1)));
    (==) {lemma_pow_mod_int_add #q psi ((j - k) * (2 * i)) (j - k)}
    (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i)) %* pow_mod_int #q psi (j - k));
  }

val intt_ntt_is_id_kth_term_3_inner:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> i:int{i < n}
  -> Lemma ((sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i + 1)))))
        == (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k)))))
let intt_ntt_is_id_kth_term_3_inner #n #psi f k i = Classical.forall_intro (intt_ntt_is_id_kth_term_3_inner_aux #n #psi f k i)

val intt_ntt_is_id_kth_term_3:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k))))))
let intt_ntt_is_id_kth_term_3 #n #psi f k =
  intt_ntt_is_id_kth_term_2 #n #psi f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_3_inner #n #psi f k)

val intt_ntt_is_id_kth_term_4:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k))))))
let intt_ntt_is_id_kth_term_4 #n #psi f k = 
  intt_ntt_is_id_kth_term_3 #n #psi f k;
  swap_sum_order 0 n 0 n (fun i j -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k)))

val intt_ntt_is_id_kth_term_5_aux_rewrite_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> i:int{i < n}
  -> Lemma ((poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k))
         == (poly_index f j %* (pow_mod_int #q psi (j - k))) %* (pow_mod_int #q psi ((j - k) * (2 * i))))
let intt_ntt_is_id_kth_term_5_aux_rewrite_aux #n #psi f k j i =
  calc (==) {
    (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k));
    (==) {}
    (poly_index f j) %* ((pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k)));
    (==) {}
    (poly_index f j) %* ((pow_mod_int #q psi (j - k)) %* (pow_mod_int #q psi ((j - k) * (2 * i))));
    (==) {}
    (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (pow_mod_int #q psi ((j - k) * (2 * i)));
  }

val intt_ntt_is_id_kth_term_5_aux_rewrite:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k))))
         == (sum_of_zqs 0 n (fun i -> (poly_index f j %* (pow_mod_int #q psi (j - k))) %* (pow_mod_int #q psi ((j - k) * (2 * i))))))
let intt_ntt_is_id_kth_term_5_aux_rewrite #n #psi f k j = Classical.forall_intro (intt_ntt_is_id_kth_term_5_aux_rewrite_aux #n #psi f k j)

val intt_ntt_is_id_kth_term_5_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (poly_index f j) %* (pow_mod_int #q psi ((j - k) * (2 * i))) %* (pow_mod_int #q psi (j - k))))
        == poly_index f j %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q psi ((j - k) * (2 * i))))))
let intt_ntt_is_id_kth_term_5_aux #n #psi f k j =
  intt_ntt_is_id_kth_term_5_aux_rewrite #n #psi f k j;
  sum_mul_lemma (poly_index f j %* (pow_mod_int #q psi (j - k))) 0 n (fun i -> (pow_mod_int #q psi ((j - k) * (2 * i))))

val intt_ntt_is_id_kth_term_5:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun j -> poly_index f j %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q psi ((j - k) * (2 * i)))))))
let intt_ntt_is_id_kth_term_5 #n #psi f k =
  intt_ntt_is_id_kth_term_4 #n #psi f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_5_aux #n #psi f k)


val intt_ntt_is_id_kth_term_6_inner_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> i:int{i < n}
  -> Lemma ((pow_mod_int #q psi ((j - k) * (2 * i)))
          == (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))
let intt_ntt_is_id_kth_term_6_inner_aux #n #psi f k j i =
  calc (==) {
    (pow_mod_int #q psi ((j - k) * (2 * i)));
    (==) {lemma_pow_mod_int_mul #q psi (2 * (j - k)) i}
    (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i);
  }

val intt_ntt_is_id_kth_term_6_inner:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (pow_mod_int #q psi ((j - k) * (2 * i))))
        == (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_6_inner #n #psi f k j = Classical.forall_intro (intt_ntt_is_id_kth_term_6_inner_aux #n #psi f k j)

val intt_ntt_is_id_kth_term_6_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma (((poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q psi ((j - k) * (2 * i))))))
         == ((poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_6_aux #n #psi f k j =
  intt_ntt_is_id_kth_term_6_inner #n #psi f k j

val intt_ntt_is_id_kth_term_6:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_6 #n #psi f k =
  intt_ntt_is_id_kth_term_5 #n #psi f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_6_aux #n #psi f k)

val intt_ntt_is_id_kth_term_7_split_sum:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))
         == sum_of_zqs 0 (k+1) (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))
            +% sum_of_zqs (k+1) n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_7_split_sum #n #psi f k =
  lemma_sum_join 0 (k+1) n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))

val intt_ntt_is_id_kth_term_7_unfold_sum:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (sum_of_zqs 0 (k+1) (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))
         == sum_of_zqs 0 k (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))
            +% f.[k] %* (pow_mod_int #q psi (k - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (k - k))) i))))
let intt_ntt_is_id_kth_term_7_unfold_sum #n #psi f k =
  unfold_sum 0 (k+1) (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0 --split_queries always"
val intt_ntt_is_id_kth_term_7_split_and_unfold_sum:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (sum_of_zqs 0 n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))
         == sum_of_zqs 0 k (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))
            +% f.[k] %* (pow_mod_int #q psi (k - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (k - k))) i)))
            +% sum_of_zqs (k+1) n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_7_split_and_unfold_sum #n #psi f k =
  intt_ntt_is_id_kth_term_7_split_sum #n #psi f k;
  intt_ntt_is_id_kth_term_7_unfold_sum #n #psi f k

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"
val intt_ntt_is_id_kth_term_7:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* (
                sum_of_zqs 0 k (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))
                +% f.[k] %* (pow_mod_int #q psi (k - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (k - k))) i)))
                +% sum_of_zqs (k+1) n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i))))))
let intt_ntt_is_id_kth_term_7 #n #psi f k =
  intt_ntt_is_id_kth_term_6 #n #psi f k;
  intt_ntt_is_id_kth_term_7_split_and_unfold_sum #n #psi f k

(* By contradiction: if = psi^-x = 1 that means that psi^x = 1*)
val lemma_pow_psi_not_one_neg:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> x:nat{x < 2 * n && x <> 0}
  -> Lemma (pow_mod_int #q psi (-x) <> 1)
let lemma_pow_psi_not_one_neg #n #psi x =
  if pow_mod_int #q psi (-x) = 1 then begin
    calc (==) {
      1;
      (==) {lemma_pow_mod_inv_def #q psi x}
      pow_mod_int #q psi x %* pow_mod_int #q psi (-x);
      (==) {}
      pow_mod_int #q psi x;
    };
    assert (False)
  end

val lemma_pow_psi_not_one:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> x:int{x < 2 * n && x <> 0 && x > -2 * n}
  -> Lemma (pow_mod_int #q psi x <> 1)
let lemma_pow_psi_not_one #n #psi x = 
  if x < 0 then lemma_pow_psi_not_one_neg #n #psi (-x)

val intt_ntt_is_id_kth_term_8_outside_terms:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i)))
          == ((pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_mod_int #q psi (2 * (j - k)) - 1) % q) (-1)))
let intt_ntt_is_id_kth_term_8_outside_terms #n #psi f k j = 
  lemma_pow_psi_not_one #n #psi (2 * (j - k));
  lemma_geometric_sum n (pow_mod_int #q psi (2 * (j - k)))

val intt_ntt_is_id_kth_term_8_outside_terms_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma ((poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) i)))
         == (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (((pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_mod_int #q psi (2 * (j - k)) - 1) % q) (-1))))
let intt_ntt_is_id_kth_term_8_outside_terms_aux #n #psi f k j =
  intt_ntt_is_id_kth_term_8_outside_terms #n #psi f k j

val intt_ntt_is_id_kth_term_8_inside_term_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> i:int
  -> Lemma (pow_mod_int #q (pow_mod_int #q psi (2 * (k - k))) i
         == pow_mod_int #q 1 i)
let intt_ntt_is_id_kth_term_8_inside_term_aux #n #psi f k i =
  calc (==) {
    pow_mod_int #q (pow_mod_int #q psi (2 * (k - k))) i;
    (==) {}
    pow_mod_int #q (pow_mod_int #q psi (0)) i;
    (==) {lemma_pow_mod_int_pow0 #q psi}
    pow_mod_int #q 1 i;
  }

val intt_ntt_is_id_kth_term_8_inside_term_rewrite:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (k - k))) i)))
        == n)
let intt_ntt_is_id_kth_term_8_inside_term_rewrite #n #psi f k =
  Classical.forall_intro (intt_ntt_is_id_kth_term_8_inside_term_aux #n #psi f k);
  lemma_geometric_sum_ones n 1

val intt_ntt_is_id_kth_term_8_inside_term:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (f.[k] %* (pow_mod_int #q psi (k - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_mod_int #q psi (2 * (k - k))) i)))
         == f.[k] %* n)
let intt_ntt_is_id_kth_term_8_inside_term #n #psi f k =
  lemma_pow_mod_int_pow0 #q psi;
  intt_ntt_is_id_kth_term_8_inside_term_rewrite #n #psi f k

val intt_ntt_is_id_kth_term_8:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* (
                sum_of_zqs 0 k (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (((pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_mod_int #q psi (2 * (j - k)) - 1) % q) (-1))))
                +% f.[k] %* n
                +% sum_of_zqs (k+1) n (fun j -> (poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (((pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_mod_int #q psi (2 * (j - k)) - 1) % q) (-1))))))
let intt_ntt_is_id_kth_term_8 #n #psi f k =
  intt_ntt_is_id_kth_term_7 #n #psi f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_8_outside_terms_aux #n #psi f k);
  intt_ntt_is_id_kth_term_8_inside_term #n #psi f k


val intt_ntt_id_kth_term_9_sum_cancels:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma ((pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) n) -% 1 == 0)
let intt_ntt_id_kth_term_9_sum_cancels #n #psi f k j =
  calc (==) {
    (pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) n) -% 1;
    (==) {lemma_pow_mod_int_mul #q psi (2 * (j - k)) n}
    ((pow_mod_int #q psi (2 * n * (j - k)))) -% 1;
    (==) {lemma_pow_mod_int_mul #q psi (2 * n) (j - k)}
    (pow_mod_int #q (pow_mod_int #q psi (2 * n)) (j - k) -% 1);
    (==) {}
    (pow_mod_int #q 1 (j - k) -% 1);
    (==) {lemma_pow_mod_int_one #q (j - k)}
    (1 -% 1);
  }

val intt_ntt_id_kth_term_9_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma ((poly_index f j) %* (pow_mod_int #q psi (j - k)) %* (((pow_mod_int #q (pow_mod_int #q psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_mod_int #q psi (2 * (j - k)) - 1) % q) (-1)))
         == 0)
let intt_ntt_id_kth_term_9_aux #n #psi f k j =
  intt_ntt_id_kth_term_9_sum_cancels #n #psi f k j

val intt_ntt_is_id_kth_term_9:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term #n #psi f k)
            == pow_mod_int #q n (-1) %* f.[k] %* n)
let intt_ntt_is_id_kth_term_9 #n #psi f k =
  intt_ntt_is_id_kth_term_8 #n #psi f k;
  Classical.forall_intro (intt_ntt_id_kth_term_9_aux #n #psi f k);
  lemma_sum_zeros 0 k;
  lemma_sum_zeros (k+1) n

val intt_ntt_is_id_kth_term: 
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> (f:lpoly n) 
  -> (k:nat{k < n}) 
  -> Lemma (ensures (f.[k]) == ((intt #n #psi (ntt #n #psi f)).[k]))
let intt_ntt_is_id_kth_term #n #psi f k =
  intt_ntt_is_id_kth_term_9 #n #psi f k;
  calc (==) {
    pow_mod_int #q n (-1) %* f.[k] %* n;
    (==) {}
    f.[k] %* pow_mod_int #q n (-1) %* n;
    (==) {}
    f.[k] %* (pow_mod_int #q n (-1) %* n);
    (==) {lemma_pow_mod_int_pow1 #q n}
    f.[k] %* (pow_mod_int #q n (-1) %* pow_mod_int #q n 1);
    (==) {lemma_pow_mod_inv_def #q n 1}
    f.[k] %* 1;
  }

val intt_ntt_is_id:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> Lemma (ensures equal f (intt #n #psi (ntt #n #psi f)))
let intt_ntt_is_id #n #psi f =
  Classical.forall_intro (intt_ntt_is_id_kth_term #n #psi f)

// val ntt_intt_is_id:
//     f:lpoly n
//   -> Lemma (requires True) (ensures Seq.equal f (ntt #n #psi (intt f)))
// let ntt_intt_is_id f =
//   admit()


let mul_componentwise (#n:power_of_two) (f g:lpoly n) = createi n (fun i -> poly_index f i %* poly_index g i)

val convolution_theorem_kth_term_ok_1:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k 
            == sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index f j) %* poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_1 #n #psi f g k =
  ntt_kth_term_lemma #n #psi (mul_quotient_ring f g) k;
  let lhs_inner_f = (fun i -> poly_index (mul_quotient_ring f g) i %* pow_mod_int #q psi (i * (2 * k + 1))) in
  let lhs_inner_f' = (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (sum_of_zqs 0 n (fun j -> (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index f j) %* (poly_index g ((i - j) % n)))))) in
  let f_i = fun i -> pow_mod_int #q psi (i * (2 * k + 1)) in
  let f_j = fun i j -> (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index f j) %* (poly_index g ((i - j) % n))) in
  sum_rewrite_lemma 0 n lhs_inner_f lhs_inner_f';
  double_sum_mul_lemma 0 n 0 n f_i f_j

val convolution_theorem_kth_term_ok_2:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index f j) %* (poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_2 #n #psi f g k =
  convolution_theorem_kth_term_ok_1 #n #psi f g k;
  swap_sum_order 0 n 0 n (fun i j -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index f j) %* (poly_index g ((i - j) % n))))

#reset-options "--z3rlimit 20 --fuel 0 --ifuel 0"
val convolution_theorem_kth_term_ok_3_:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> (poly_index f j) %* pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_3_ #n #psi f g k =
  convolution_theorem_kth_term_ok_2 #n #psi f g k;
  // First step is to rearrange the terms in the inner sum so that we can apply our sum multiplication lemma
  let original = (fun j -> (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index f j) %* (poly_index g ((i - j) % n))))) in
  let original' = (fun j -> (sum_of_zqs 0 n (fun i -> (poly_index f j) %* pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))))) in
  let lemma_aux (j:int): Lemma (ensures (original j == original' j)) =
    let first = (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index f j) %* (poly_index g ((i - j) % n))) in
    let second = (fun i -> (poly_index f j) %* pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))) in
    let lemma_aux' (i:int): Lemma (ensures (first i == second i)) =
      lemma_mul_rearrange (pow_mod_int #q psi (i * (2 * k + 1))) (pow_mod_int_neg_one ((i - j) / n)) (poly_index f j) (poly_index g ((i - j) % n)) in
    Classical.forall_intro (lemma_aux') in
  Classical.forall_intro (lemma_aux);
  sum_rewrite_lemma 0 n original original'

val convolution_theorem_kth_term_ok_3:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (poly_index f j) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_3 #n #psi f g k =
  convolution_theorem_kth_term_ok_3_ #n #psi f g k;
  // First step is to rearrange the terms in the inner sum so that we can apply our sum multiplication lemma
  let original' = (fun j -> (sum_of_zqs 0 n (fun i -> (poly_index f j) %* pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))))) in
  // Next step is to apply the sum multiplication lemma, and then we need to do an additional small step to remove the parenthesization
  let goal = (fun j -> (poly_index f j) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))))) in
  let lemma_aux2 (j:int): Lemma (ensures original' j == goal j) =
    sum_mul_lemma (poly_index f j) 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n)));
    let parenthesized = (fun i -> (poly_index f j) %* (pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n)))) in
    let unparenthesized = (fun i -> (poly_index f j) %* pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))) in
    let lemma_aux2' (i:int): Lemma (ensures (parenthesized i == unparenthesized i)) =
      lemma_mul_assoc_big (poly_index f j) (pow_mod_int #q psi (i * (2 * k + 1))) (pow_mod_int_neg_one ((i - j) / n)) (poly_index g ((i - j) % n)) in
    Classical.forall_intro (lemma_aux2') in
  Classical.forall_intro (lemma_aux2);
  sum_rewrite_lemma 0 n original' goal

#push-options "--split_queries always"
val convolution_theorem_kth_term_ok_4_:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> i:int
  -> Lemma 
      (requires True) 
      (ensures pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))
            == pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n)))
let convolution_theorem_kth_term_ok_4_ #n #psi f g k j i =
  calc (==) {
    pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n));
    (==) {}
    pow_mod_int #q psi (i * (2 * k + 1)) %* 1 %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n));
    (==) {lemma_pow_mod_inv_def #q psi (j * (2 * k + 1))}
    pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1))) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n));
    (==) {}
    pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n));
    (==) {}
    pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n));
  }
#pop-options

val convolution_theorem_kth_term_ok_4_aux_:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma 
      (requires True) 
      (ensures (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))))
            == (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n)))))
let convolution_theorem_kth_term_ok_4_aux_ #n #psi f g k j =
  let original = (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))) in
  let goal = (fun i -> pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))) in
  Classical.forall_intro (convolution_theorem_kth_term_ok_4_ #n #psi f g k j)

val convolution_theorem_kth_term_ok_4_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma 
      (requires True) 
      (ensures (poly_index f j) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n))))
            == (poly_index f j) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (poly_index g ((i - j) % n)))))
let convolution_theorem_kth_term_ok_4_aux #n #psi f g k j =
  convolution_theorem_kth_term_ok_4_aux_ #n #psi f g k j

// Adds pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) = 1 into the inner sum
val convolution_theorem_kth_term_ok_4:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (poly_index f j) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))))
let convolution_theorem_kth_term_ok_4 #n #psi f g k =
  convolution_theorem_kth_term_ok_3 #n #psi f g k;
  Classical.forall_intro (convolution_theorem_kth_term_ok_4_aux #n #psi f g k)

val convolution_theorem_kth_term_ok_5_aux_:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma 
      (requires True) 
      (ensures (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))
            == pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_5_aux_ #n #psi f g k j =
  let lemma_aux (i:int): Lemma (pow_mod_int #q psi (j * (2 * k + 1)) %* (pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n))))
                             == pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))) = 
    lemma_mul_assoc_bigger (pow_mod_int #q psi (j * (2 * k + 1))) (pow_mod_int #q psi (i * (2 * k + 1))) (pow_mod_int #q psi (-j * (2 * k + 1))) (pow_mod_int_neg_one ((i - j) / n)) ((poly_index g ((i - j) % n))) in
  Classical.forall_intro lemma_aux;
  sum_mul_lemma (pow_mod_int #q psi (j * (2 * k + 1))) 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n))))

val convolution_theorem_kth_term_ok_5_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma 
      (ensures (poly_index f j) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))
            == (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_5_aux #n #psi f g k j =
  convolution_theorem_kth_term_ok_5_aux_ #n #psi f g k j

#reset-options "--z3rlimit 15 --fuel 0 --ifuel 0 --split_queries always"
// Moves pow_mod_int #q psi (j * (2 * k + 1)) out of the inner sum
val convolution_theorem_kth_term_ok_5:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))))
let convolution_theorem_kth_term_ok_5 #n #psi f g k =
  convolution_theorem_kth_term_ok_4 #n #psi f g k;
  assert (ntt_kth_term #n #psi (mul_quotient_ring f g) k == sum_of_zqs 0 n (fun j -> (poly_index f j) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (j * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))));
  Classical.forall_intro (convolution_theorem_kth_term_ok_5_aux #n #psi f g k);
  assert (ntt_kth_term #n #psi (mul_quotient_ring f g) k == sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))))

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
val convolution_theorem_kth_term_ok_6_aux_aux_rewrite:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat
  -> j:int
  -> i:int
  -> Lemma (pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))
         == pow_mod_int #q psi ((i - j) * (2*k+1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n))))
let convolution_theorem_kth_term_ok_6_aux_aux_rewrite #n #psi f g k j i =
  assert (i * (2 * k + 1) + (-j * (2 * k + 1)) == ((i - j) * (2 * k + 1)));
  calc (==) {
    pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)));
    (==) {}
    (pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1))) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)));
    (==) {lemma_pow_mod_int_add #q psi (i * (2 * k + 1)) (-j * (2 * k + 1))}
    (pow_mod_int #q psi (i * (2 * k + 1) + (-j * (2 * k + 1)))) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)));
    (==) {}
    (pow_mod_int #q psi ((i - j) * (2 * k + 1))) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)));
  }

val rearrange_6_aux_aux:
  a:int 
  -> b:int 
  -> c:int
  -> Lemma ((a * b) * c == b * (c * a))
let rearrange_6_aux_aux a b c = ()

val convolution_theorem_kth_term_ok_6_rewrite:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat
  -> j:int
  -> i:int
  -> Lemma (pow_mod_int #q psi ((i - j) * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n))
         == pow_mod_int #q psi (((i - j) % n) * (2 * k + 1)))
let convolution_theorem_kth_term_ok_6_rewrite #n #psi f g k j i = 
  let quot = (i - j) / n in 
  let r = (i - j) % n in 
  assert (i - j == quot * n + r);
  calc (==) {
    pow_mod_int #q psi ((quot * n + r) * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {ML.distributivity_add_left (quot * n) r (2 * k + 1)}
    pow_mod_int #q psi ((quot * n) * (2 * k + 1) + r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_int_add #q psi (quot * n * (2 * k + 1)) (r * (2 * k + 1))}
    pow_mod_int #q psi ((quot * n) * (2 * k + 1)) %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {rearrange_6_aux_aux quot n (2 * k + 1)}
    pow_mod_int #q psi (n * ((2 * k + 1) * quot)) %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_int_mul #q psi n ((2 * k + 1) * quot)}
    pow_mod_int #q (pow_mod_int #q psi n) ((2 * k + 1) * quot) %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
    pow_mod_int #q ((-1) % q) ((2 * k + 1) * quot) %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_int_mul #q ((-1) % q) (2 * k + 1) quot}
    pow_mod_int #q (pow_mod_int #q ((-1) % q) (2 * k + 1)) quot %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod_pos #q (2 * k + 1)}
    pow_mod_int #q (pow_mod_int_neg_one #q (2 * k + 1)) quot %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {}
    pow_mod_int #q ((-1) % q) quot %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q quot}
    pow_mod_int #q ((-1) % q) quot %* pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int #q ((-1) % q) quot);
    (==) {lemma_mul_zq_comm (pow_mod_int #q ((-1) % q) quot) (pow_mod_int #q psi (r * (2 * k + 1)))}
    pow_mod_int #q psi (r * (2 * k + 1)) %* pow_mod_int #q ((-1) % q) (quot) %* pow_mod_int #q ((-1) % q) (quot);
    (==) {lemma_mul_zq_assoc (pow_mod_int #q psi (r * (2 * k + 1))) (pow_mod_int #q ((-1) % q) (quot)) (pow_mod_int #q ((-1) % q) (quot))}
    pow_mod_int #q psi (r * (2 * k + 1)) %* (pow_mod_int #q ((-1) % q) (quot) %* pow_mod_int #q ((-1) % q) (quot));
    (==) {lemma_pow_mod_int_add #q ((-1) % q) quot quot}
    pow_mod_int #q psi (r * (2 * k + 1)) %* pow_mod_int #q ((-1) % q) (quot + quot);
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q (quot + quot)}
    pow_mod_int #q psi (r * (2 * k + 1)) %* pow_mod_int_neg_one (quot + quot);
    (==) {}
    pow_mod_int #q psi (r * (2 * k + 1));
  }

val convolution_theorem_kth_term_ok_6_inner_sum_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n 
  -> k:nat{k < n}
  -> j:int
  -> i:int 
  -> Lemma
      (pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))
    == pow_mod_int #q psi (((i - j) % n) * (2 * k + 1)) %* ((poly_index g ((i - j) % n))))
let convolution_theorem_kth_term_ok_6_inner_sum_aux #n #psi f g k j i =
  calc (==) {
    pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)));
    (==) {convolution_theorem_kth_term_ok_6_aux_aux_rewrite #n #psi f g k j i}
    pow_mod_int #q psi ((i - j) * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)));
    (==) {}
    (pow_mod_int #q psi ((i - j) * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n))) %* ((poly_index g ((i - j) % n)));
    (==) {convolution_theorem_kth_term_ok_6_rewrite #n #psi f g k j i}
    (pow_mod_int #q psi (((i - j) % n) * (2 * k + 1))) %* ((poly_index g ((i - j) % n)));
  }

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
val convolution_theorem_kth_term_ok_6_outer_sum_aux_helper:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      ((sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))
    == (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (((i - j) % n) * (2 * k + 1)) %* ((poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_6_outer_sum_aux_helper #n #psi f g k j =
  let original = (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))) in
  let goal = (fun i -> pow_mod_int #q psi (((i - j) % n) * (2 * k + 1)) %* ((poly_index g ((i - j) % n)))) in
  Classical.forall_intro (convolution_theorem_kth_term_ok_6_inner_sum_aux #n #psi f g k j)


val convolution_theorem_kth_term_ok_6_outer_sum_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2 * k + 1)) %* pow_mod_int #q psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* ((poly_index g ((i - j) % n)))))
    == (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (((i - j) % n) * (2*k+1)) %* ((poly_index g ((i - j) % n))))))
let convolution_theorem_kth_term_ok_6_outer_sum_aux #n #psi f g k j =
  convolution_theorem_kth_term_ok_6_outer_sum_aux_helper #n #psi f g k j

#reset-options "--z3rlimit 15 --fuel 0 --ifuel 0"
val convolution_theorem_kth_term_ok_6:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (((i - j) % n) * (2*k+1)) %* ((poly_index g ((i - j) % n)))))))
let convolution_theorem_kth_term_ok_6 #n #psi f g k =
  convolution_theorem_kth_term_ok_5 #n #psi f g k;
  Classical.forall_intro (convolution_theorem_kth_term_ok_6_outer_sum_aux #n #psi f g k)

val convolution_theorem_kth_term_ok_7_inner_sum_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (((i - j) % n) * (2*k+1)) %* ((poly_index g ((i - j) % n))))
    == sum_of_zqs 0 n (fun i' -> pow_mod_int #q psi (i' * (2*k+1)) %* (poly_index g i')))
let convolution_theorem_kth_term_ok_7_inner_sum_aux #n #psi f g k j =
  let original = (fun i -> pow_mod_int #q psi (((i - j) % n) * (2*k+1)) %* ((poly_index g ((i - j) % n)))) in
  let goal = (fun i' -> pow_mod_int #q psi (i' * (2*k+1)) %* (poly_index g i')) in 
  lemma_sum_shift_mod n j goal


val convolution_theorem_kth_term_ok_7_outer_sum_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (((i - j) % n) * (2*k+1)) %* ((poly_index g ((i - j) % n)))))
    == (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))))
let convolution_theorem_kth_term_ok_7_outer_sum_aux #n #psi f g k j =
  convolution_theorem_kth_term_ok_7_inner_sum_aux #n #psi f g k j

val convolution_theorem_kth_term_ok_7:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i)))))
let convolution_theorem_kth_term_ok_7 #n #psi f g k =
  convolution_theorem_kth_term_ok_6 #n #psi f g k;
  Classical.forall_intro (convolution_theorem_kth_term_ok_7_outer_sum_aux #n #psi f g k)

val convolution_theorem_kth_term_ok_8_rewrite7_aux:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i)))
    == (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))) %* ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1))))
let convolution_theorem_kth_term_ok_8_rewrite7_aux #n #psi f g k j = 
  calc (==) {
    (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i)));
    (==) {lemma_mul_mod_comm ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1))) (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i)))}
    (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))) %* ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)));
  }

val convolution_theorem_kth_term_ok_8_rewrite7:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma
       (sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))))
     == sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))) %* ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)))))
let convolution_theorem_kth_term_ok_8_rewrite7 #n #psi f g k =
  Classical.forall_intro (convolution_theorem_kth_term_ok_8_rewrite7_aux #n #psi f g k)

val convolution_theorem_kth_term_ok_8_apply_mul:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n  
  -> k:nat{k < n}
  -> Lemma
      (sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))) %* ((poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1))))
   == (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))) %* (sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)))))
let convolution_theorem_kth_term_ok_8_apply_mul #n #psi f g k =
  sum_mul_lemma (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))) 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)))

val convolution_theorem_kth_term_ok_8_comm:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n  
  -> k:nat{k < n}
  -> Lemma
      ((sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))) %* (sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1))))
    == (sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)))) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))))
let convolution_theorem_kth_term_ok_8_comm f g k = ()

val convolution_theorem_kth_term_ok_8:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == (sum_of_zqs 0 n (fun j -> (poly_index f j) %* pow_mod_int #q psi (j * (2 * k + 1)))) %* (sum_of_zqs 0 n (fun i -> pow_mod_int #q psi (i * (2*k+1)) %* (poly_index g i))))
let convolution_theorem_kth_term_ok_8 #n #psi f g k =
  convolution_theorem_kth_term_ok_7 #n #psi f g k;
  convolution_theorem_kth_term_ok_8_rewrite7 #n #psi f g k;
  convolution_theorem_kth_term_ok_8_apply_mul #n #psi f g k;
  convolution_theorem_kth_term_ok_8_comm #n #psi f g k

val convolution_theorem_kth_term_ok_9:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n 
  -> g:lpoly n
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term #n #psi (mul_quotient_ring f g) k
            == ntt_kth_term #n #psi f k %* ntt_kth_term #n #psi g k)
let convolution_theorem_kth_term_ok_9 #n #psi f g k =
  convolution_theorem_kth_term_ok_8 #n #psi f g k

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"
val convolution_theorem_kth_term_ok:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> k:nat
  -> Lemma 
      (requires True) 
      (ensures (ntt_kth_term #n #psi (mul_quotient_ring f g) k == ntt_kth_term #n #psi f k %* ntt_kth_term #n #psi g k))
let convolution_theorem_kth_term_ok #n #psi f g k =
  if 0 <= k && k < n then 
    convolution_theorem_kth_term_ok_9 #n #psi f g k
  else ()

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0 --split_queries always"
val convolution_theorem:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> Lemma 
      (requires True) 
      (ensures equal 
        (ntt #n #psi (mul_quotient_ring f g))
        (mul_componentwise (ntt #n #psi f) (ntt #n #psi g)))
let convolution_theorem #n #psi f g =
  Classical.forall_intro (convolution_theorem_kth_term_ok #n #psi f g);
  let lhs = ntt #n #psi (mul_quotient_ring f g) in
  let rhs = mul_componentwise (ntt #n #psi f) (ntt #n #psi g) in
  assert (forall (i:nat{i < n}).{:pattern (lhs.[i]); (rhs.[i])} (lhs.[i] == rhs.[i]))

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"
val mul_ntt_ok:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> g:lpoly n
  -> Lemma 
      (ensures Seq.equal 
        (mul_quotient_ring f g) 
        (intt #n #psi (mul_componentwise (ntt #n #psi f) (ntt #n #psi g))))
let mul_ntt_ok #n #psi f g =
  convolution_theorem #n #psi f g;
  assert (Seq.equal
            (intt #n #psi (ntt #n #psi (mul_quotient_ring f g))) 
            (intt #n #psi (mul_componentwise (ntt #n #psi f) (ntt #n #psi g))));
  intt_ntt_is_id #n #psi (mul_quotient_ring f g);
  assert (mul_quotient_ring f g == intt #n #psi (mul_componentwise (ntt #n #psi f) (ntt #n #psi g)))
  
