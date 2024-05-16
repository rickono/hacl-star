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
type len_t = l:nat{l = 2 || l = 4 || l = 8 || l = 16 || l = 32 || l = 64 || l = 128}
type start_t (len:len_t) = s:nat{s % (2*len) = 0 && s < 256}

let psi: primitive_nth_root_of_unity_mod #q 512 =
  assume (pow_mod #q 799 512 == 1);
  assume (is_primitive #q #512 799);
  799

val pow_psi: (n:int) -> zq
let pow_psi n = pow_mod_int #q psi n

// Lemma: psi^-n, where n is positive, can be rewritten as (psi^(-1))^n (or the modular inverse raised to n)
val pow_psi_mod_inverse_lemma:
    n:int{n < 0}
  -> Lemma (pow_psi n == pow_mod #q (pow_psi (-1)) (-n))
let pow_psi_mod_inverse_lemma n =
  assert (pow_psi (-1) == pow_mod #q psi (q - 2));
  calc (==) {
    pow_psi n;
    (==) {}
    pow_mod #q psi ((-n) * (q - 2));
    (==) {lemma_pow_mod #q psi ((-n) * (q - 2))}
    pow psi ((-n) * (q - 2)) % q;
    (==) {lemma_pow_mul psi (q - 2) (-n)}
    pow (pow psi (q - 2)) (-n) % q;
    (==) {lemma_pow_mod_base (pow psi (q - 2)) (-n) q}
    pow (pow psi (q - 2) % q) (-n) % q;
    (==) {lemma_pow_mod #q psi (q - 2)}
    pow (pow_mod #q psi (q - 2)) (-n) % q;
    (==) {}
    pow (pow_psi (-1)) (-n) % q;
    (==) {lemma_pow_mod (pow_psi (-1)) (-n)}
    pow_mod #q (pow_psi (-1)) (-n);
  }
  
val lemma_pow_psi_identity_: (n:nat) -> Lemma (requires True) (ensures (pow_psi n %* pow_psi (-n) == 1))
let lemma_pow_psi_identity_ n = 
  Fermat.fermat_alt q psi;
  calc (==) {
    pow_psi n %* pow_psi (-n);
    (==) {}
    pow_mod #q psi n %* pow_mod #q psi (n * (q - 2));
    (==) {lemma_pow_mod #q psi n; lemma_pow_mod #q psi (n * (q - 2))}
    (pow psi n % q) %* (pow psi (n * (q - 2)) % q);
    (==) {}
    (pow psi n % q) * (pow psi (n * (q - 2)) % q) % q;
    (==) {ML.lemma_mod_mul_distr_r (pow psi n) (pow psi (n * (q - 2))) q;
          ML.lemma_mod_mul_distr_l (pow psi n) (pow psi (n * (q - 2)) % q) q}
    (pow psi n) * (pow psi (n * (q - 2))) % q;
    (==) {lemma_pow_add psi n (n * (q - 2))}
    (pow psi (n + n * (q - 2))) % q;
    (==) {}
    (pow psi ((q - 1) * n)) % q;
    (==) {lemma_pow_mul psi (q - 1) n; lemma_pow_eq_fermat_pow psi (q - 1)}
    (pow (Fermat.pow psi (q - 1)) n) % q;
    (==) {lemma_pow_mod_base (Fermat.pow psi (q-1)) n q}
    (pow 1 n) % q;
    (==) {lemma_pow_one n}
    1 % q;
  }

val lemma_pow_psi_identity: (n:int) -> Lemma (requires True) (ensures (pow_psi n %* pow_psi (-n) == 1))
let lemma_pow_psi_identity n =
  if n >= 0 then 
    lemma_pow_psi_identity_ n
  else
    lemma_pow_psi_identity_ (-n)

val mul_quotient_ring_kth_term:
    f:rq
  -> g:rq
  -> k:int
  -> zq
let mul_quotient_ring_kth_term f g k =
  if k < 0 || k >= n then 0
  else sum_of_zqs 0 n (fun j -> (pow_mod_int_neg_one ((k - j) / n)) %* (f.[j] %* g.[(k - j) % n]))

val mul_quotient_ring:
    f:rq
  -> g:rq
  -> rq
let mul_quotient_ring f g = 
  createi n (fun k -> mul_quotient_ring_kth_term f g k)

val mul_quotient_ring_lemma:
    f:rq
  -> g:rq
  -> k:int
  -> Lemma ((mul_quotient_ring f g).[k] == mul_quotient_ring_kth_term f g k)
let mul_quotient_ring_lemma f g k = ()

val ntt_kth_term:
    f:lpoly n
  -> k:int
  -> zq
let ntt_kth_term f k = 
  if k < 0 || k >= n then 0 
  else sum_of_zqs 0 n (fun j -> mul_zq (f.[j]) (pow_psi (j * (2 * k + 1))))

val ntt_kth_term_lemma:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma ((ntt_kth_term f k) == sum_of_zqs 0 n (fun j -> mul_zq (f.[j]) (pow_psi (j * (2 * k + 1)))))
  [SMTPat (ntt_kth_term f k)] 
let ntt_kth_term_lemma f k = ()

let ntt (f:lpoly n) =
  createi n (fun k -> ntt_kth_term f k)

val ntt_lemma (f:lpoly n) (i:int): 
  Lemma ((ntt f).[i] == ntt_kth_term f i)
  [SMTPat ((ntt f).[i])]
let ntt_lemma f i = ()


val intt_kth_term:
    f:lpoly n
  -> k:int
  -> zq
let intt_kth_term f k =
  if k < 0 || k >= n then 0
  else pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> mul_zq (f.[i]) (pow_psi (-k * (2 * i + 1))))

let intt (f:lpoly n) = createi n (fun k -> intt_kth_term f k)

val intt_lemma (f:lpoly n) (i:int): 
  Lemma ((intt f).[i] == intt_kth_term f i)
  [SMTPat (index (intt f) i)]
let intt_lemma f i = ()

// INTT(NTT(f))_k
val intt_ntt_kth_term:
    f:lpoly n
  -> k:nat{k < n}
  -> zq
let intt_ntt_kth_term f k = (intt (ntt f)).[k]

val intt_ntt_is_id_kth_term_0_aux:
    f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> Lemma 
       (mul_zq (ntt_kth_term f i) (pow_psi (-k * (2 * i + 1)))
       == mul_zq (sum_of_zqs 0 n (fun j -> mul_zq (f.[j]) (pow_psi (j * (2 * i + 1))))) (pow_psi (-k * (2 * i + 1))))
let intt_ntt_is_id_kth_term_0_aux f k i = ()

val intt_ntt_is_id_kth_term_0:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi (j * (2 * i + 1))))) %* (pow_psi (-k * (2 * i + 1)))))
let intt_ntt_is_id_kth_term_0 f k =
  Classical.forall_intro (intt_ntt_is_id_kth_term_0_aux f k)

val intt_ntt_is_id_kth_term_1_aux:
    f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> Lemma 
      ((sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi (j * (2 * i + 1))))) %* (pow_psi (-k * (2 * i + 1)))
    == (sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi (j * (2 * i + 1))) %* (pow_psi (-k * (2 * i + 1))))))
let intt_ntt_is_id_kth_term_1_aux f k i =
  sum_mul_lemma (pow_psi (-k * (2 * i + 1))) 0 n (fun j -> (f.[j]) %* (pow_psi (j * (2 * i + 1))))

val intt_ntt_is_id_kth_term_1:
    f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi (j * (2 * i + 1))) %* (pow_psi (-k * (2 * i + 1)))))))
let intt_ntt_is_id_kth_term_1 f k = Classical.forall_intro (intt_ntt_is_id_kth_term_1_aux f k)

val intt_ntt_is_id_kth_term_2_inner_aux:
    f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> j:int{0 <= j && j < n}
  -> Lemma ((f.[j]) %* (pow_psi (j * (2 * i + 1))) %* (pow_psi (-k * (2 * i + 1)))
          == (f.[j]) %* (pow_psi ((j - k) * (2 * i + 1))))
let intt_ntt_is_id_kth_term_2_inner_aux f k i j =
  calc (==) {
    (f.[j]) %* (pow_psi (j * (2 * i + 1))) %* (pow_psi (-k * (2 * i + 1)));
    (==) {}
    (f.[j]) %* ((pow_psi (j * (2 * i + 1))) %* (pow_psi (-k * (2 * i + 1))));
    (==) {lemma_pow_mod_int_add #q psi (j * (2 * i + 1)) (-k * (2 * i + 1))}
    (f.[j]) %* (pow_psi ((j * (2 * i + 1)) + (-k * (2 * i + 1))));
    (==) {}
    (f.[j]) %* (pow_psi (((j - k) * (2 * i + 1))));
  }

val intt_ntt_is_id_kth_term_2_aux:
    f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> i:int{0 <= i && i < n}
  -> Lemma ((sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi (j * (2 * i + 1))) %* (pow_psi (-k * (2 * i + 1))))) 
         == (sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi ((j - k) * (2 * i + 1))))))
let intt_ntt_is_id_kth_term_2_aux f k i = 
  Classical.forall_intro (intt_ntt_is_id_kth_term_2_inner_aux f k i)

val intt_ntt_is_id_kth_term_2:
    f:lpoly n
  -> k:nat{0 <= k && k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi ((j - k) * (2 * i + 1)))))))
let intt_ntt_is_id_kth_term_2 f k = 
  intt_ntt_is_id_kth_term_1 f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_2_aux f k)

val intt_ntt_is_id_kth_term_3_inner_aux:
    f:lpoly n
  -> k:nat{k < n}
  -> i:int{i < n}
  -> j:int{j < n}
  -> Lemma ((f.[j]) %* (pow_psi ((j - k) * (2 * i + 1)))
          == (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k)))
let intt_ntt_is_id_kth_term_3_inner_aux f k i j =
  calc (==) {
    (f.[j]) %* (pow_psi ((j - k) * (2 * i + 1)));
    (==) {lemma_pow_mod_int_add #q psi ((j - k) * (2 * i)) (j - k)}
    (f.[j]) %* (pow_psi ((j - k) * (2 * i)) %* pow_psi (j - k));
  }

val intt_ntt_is_id_kth_term_3_inner:
    f:lpoly n
  -> k:nat{k < n}
  -> i:int{i < n}
  -> Lemma ((sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi ((j - k) * (2 * i + 1)))))
        == (sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k)))))
let intt_ntt_is_id_kth_term_3_inner f k i = Classical.forall_intro (intt_ntt_is_id_kth_term_3_inner_aux f k i)

val intt_ntt_is_id_kth_term_3:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k))))))
let intt_ntt_is_id_kth_term_3 f k =
  intt_ntt_is_id_kth_term_2 f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_3_inner f k)

val intt_ntt_is_id_kth_term_4:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k))))))
let intt_ntt_is_id_kth_term_4 f k = 
  intt_ntt_is_id_kth_term_3 f k;
  swap_sum_order 0 n 0 n (fun i j -> (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k)))

val intt_ntt_is_id_kth_term_5_aux_rewrite_aux:
    f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> i:int{i < n}
  -> Lemma ((f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k))
         == (f.[j] %* (pow_psi (j - k))) %* (pow_psi ((j - k) * (2 * i))))
let intt_ntt_is_id_kth_term_5_aux_rewrite_aux f k j i =
  calc (==) {
    (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k));
    (==) {}
    (f.[j]) %* ((pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k)));
    (==) {}
    (f.[j]) %* ((pow_psi (j - k)) %* (pow_psi ((j - k) * (2 * i))));
    (==) {}
    (f.[j]) %* (pow_psi (j - k)) %* (pow_psi ((j - k) * (2 * i)));
  }

val intt_ntt_is_id_kth_term_5_aux_rewrite:
    f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k))))
         == (sum_of_zqs 0 n (fun i -> (f.[j] %* (pow_psi (j - k))) %* (pow_psi ((j - k) * (2 * i))))))
let intt_ntt_is_id_kth_term_5_aux_rewrite f k j = Classical.forall_intro (intt_ntt_is_id_kth_term_5_aux_rewrite_aux f k j)

val intt_ntt_is_id_kth_term_5_aux:
    f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (f.[j]) %* (pow_psi ((j - k) * (2 * i))) %* (pow_psi (j - k))))
        == f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_psi ((j - k) * (2 * i))))))
let intt_ntt_is_id_kth_term_5_aux f k j =
  intt_ntt_is_id_kth_term_5_aux_rewrite f k j;
  sum_mul_lemma (f.[j] %* (pow_psi (j - k))) 0 n (fun i -> (pow_psi ((j - k) * (2 * i))))

val intt_ntt_is_id_kth_term_5:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_psi ((j - k) * (2 * i)))))))
let intt_ntt_is_id_kth_term_5 f k =
  intt_ntt_is_id_kth_term_4 f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_5_aux f k)


val intt_ntt_is_id_kth_term_6_inner_aux:
    f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> i:int{i < n}
  -> Lemma ((pow_psi ((j - k) * (2 * i)))
          == (pow_mod_int #q (pow_psi (2 * (j - k))) i))
let intt_ntt_is_id_kth_term_6_inner_aux f k j i =
  calc (==) {
    (pow_psi ((j - k) * (2 * i)));
    (==) {lemma_pow_mod_int_mul #q psi (2 * (j - k)) i}
    (pow_mod_int #q (pow_psi (2 * (j - k))) i);
  }

val intt_ntt_is_id_kth_term_6_inner:
    f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (pow_psi ((j - k) * (2 * i))))
        == (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_6_inner f k j = Classical.forall_intro (intt_ntt_is_id_kth_term_6_inner_aux f k j)

val intt_ntt_is_id_kth_term_6_aux:
    f:lpoly n
  -> k:nat{k < n}
  -> j:int{j < n}
  -> Lemma ((f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_psi ((j - k) * (2 * i))))))
         == (f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_6_aux f k j =
  intt_ntt_is_id_kth_term_6_inner f k j

val intt_ntt_is_id_kth_term_6:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* sum_of_zqs 0 n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_6 f k =
  intt_ntt_is_id_kth_term_5 f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_6_aux f k)

val intt_ntt_is_id_kth_term_7_split_sum:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (sum_of_zqs 0 n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))
         == sum_of_zqs 0 (k+1) (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))
            +% sum_of_zqs (k+1) n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_7_split_sum f k =
  lemma_sum_join 0 (k+1) n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0 --split_queries always"
val intt_ntt_is_id_kth_term_7_unfold_sum:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (sum_of_zqs 0 n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))
         == sum_of_zqs 0 k (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))
            +% f.[k] %* (pow_psi (k - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (k - k))) i)))
            +% sum_of_zqs (k+1) n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i)))))
let intt_ntt_is_id_kth_term_7_unfold_sum f k =
  intt_ntt_is_id_kth_term_7_split_sum f k;
  unfold_sum 0 (k+1) (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"
val intt_ntt_is_id_kth_term_7:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* (
                sum_of_zqs 0 k (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))
                +% f.[k] %* (pow_psi (k - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (k - k))) i)))
                +% sum_of_zqs (k+1) n (fun j -> f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i))))))
let intt_ntt_is_id_kth_term_7 f k =
  intt_ntt_is_id_kth_term_6 f k;
  intt_ntt_is_id_kth_term_7_unfold_sum f k

(* By contradiction: if = psi^-x = 1 that means that psi^x = 1*)
val lemma_pow_psi_not_one_neg:
    x:nat{x < 2 * n && x <> 0}
  -> Lemma (pow_psi (-x) <> 1)
let lemma_pow_psi_not_one_neg x =
  if pow_psi (-x) = 1 then begin
    calc (==) {
      1;
      (==) {lemma_pow_mod_inv_def #q psi x}
      pow_psi x %* pow_psi (-x);
      (==) {}
      pow_psi x;
    };
    assert (False)
  end

val lemma_pow_psi_not_one:
    x:int{x < 2 * n && x <> 0 && x > -2 * n}
  -> Lemma (pow_psi x <> 1)
let lemma_pow_psi_not_one x = 
  if x < 0 then lemma_pow_psi_not_one_neg (-x)

val intt_ntt_is_id_kth_term_8_outside_terms:
    f:lpoly n
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i)))
          == ((pow_mod_int #q (pow_psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_psi (2 * (j - k)) - 1) % q) (-1)))
let intt_ntt_is_id_kth_term_8_outside_terms f k j = 
  lemma_pow_psi_not_one (2 * (j - k));
  lemma_geometric_sum n (pow_psi (2 * (j - k)))

val intt_ntt_is_id_kth_term_8_outside_terms_aux:
    f:lpoly n 
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma (f.[j] %* (pow_psi (j - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (j - k))) i)))
         == f.[j] %* (pow_psi (j - k)) %* (((pow_mod_int #q (pow_psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_psi (2 * (j - k)) - 1) % q) (-1))))
let intt_ntt_is_id_kth_term_8_outside_terms_aux f k j =
  intt_ntt_is_id_kth_term_8_outside_terms f k j

val intt_ntt_is_id_kth_term_8_inside_term_aux:
    f:lpoly n
  -> k:nat{k < n}
  -> i:int
  -> Lemma (pow_mod_int #q (pow_psi (2 * (k - k))) i
         == pow_mod_int #q 1 i)
let intt_ntt_is_id_kth_term_8_inside_term_aux f k i =
  calc (==) {
    pow_mod_int #q (pow_psi (2 * (k - k))) i;
    (==) {}
    pow_mod_int #q (pow_psi (0)) i;
    (==) {lemma_pow_mod_int_pow0 #q psi}
    pow_mod_int #q 1 i;
  }

val intt_ntt_is_id_kth_term_8_inside_term_rewrite:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma ((sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (k - k))) i)))
        == n)
let intt_ntt_is_id_kth_term_8_inside_term_rewrite f k =
  Classical.forall_intro (intt_ntt_is_id_kth_term_8_inside_term_aux f k);
  lemma_geometric_sum_ones n 1

val intt_ntt_is_id_kth_term_8_inside_term:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (f.[k] %* (pow_psi (k - k)) %* (sum_of_zqs 0 n (fun i -> (pow_mod_int #q (pow_psi (2 * (k - k))) i)))
         == f.[k] %* n)
let intt_ntt_is_id_kth_term_8_inside_term f k =
  lemma_pow_mod_int_pow0 #q psi;
  intt_ntt_is_id_kth_term_8_inside_term_rewrite f k

val intt_ntt_is_id_kth_term_8:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* (
                sum_of_zqs 0 k (fun j -> f.[j] %* (pow_psi (j - k)) %* (((pow_mod_int #q (pow_psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_psi (2 * (j - k)) - 1) % q) (-1))))
                +% f.[k] %* n
                +% sum_of_zqs (k+1) n (fun j -> f.[j] %* (pow_psi (j - k)) %* (((pow_mod_int #q (pow_psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_psi (2 * (j - k)) - 1) % q) (-1))))))
let intt_ntt_is_id_kth_term_8 f k =
  intt_ntt_is_id_kth_term_7 f k;
  Classical.forall_intro (intt_ntt_is_id_kth_term_8_outside_terms_aux f k);
  intt_ntt_is_id_kth_term_8_inside_term f k


val intt_ntt_id_kth_term_9_sum_cancels:
    f:lpoly n
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma ((pow_mod_int #q (pow_psi (2 * (j - k))) n) -% 1 == 0)
let intt_ntt_id_kth_term_9_sum_cancels f k j =
  calc (==) {
    (pow_mod_int #q (pow_psi (2 * (j - k))) n) -% 1;
    (==) {lemma_pow_mod_int_mul #q psi (2 * (j - k)) n}
    ((pow_psi (2 * n * (j - k)))) -% 1;
    (==) {lemma_pow_mod_int_mul #q psi (2 * n) (j - k)}
    (pow_mod_int #q (pow_psi (2 * n)) (j - k) -% 1);
    (==) {}
    (pow_mod_int #q 1 (j - k) -% 1);
    (==) {lemma_pow_mod_int_one #q (j - k)}
    (1 -% 1);
  }

val intt_ntt_id_kth_term_9_aux:
    f:lpoly n
  -> k:nat{k < n}
  -> j:nat{j < n && j <> k}
  -> Lemma (f.[j] %* (pow_psi (j - k)) %* (((pow_mod_int #q (pow_psi (2 * (j - k))) n) -% 1) %* (pow_mod_int #q ((pow_psi (2 * (j - k)) - 1) % q) (-1)))
         == 0)
let intt_ntt_id_kth_term_9_aux f k j =
  intt_ntt_id_kth_term_9_sum_cancels f k j

val intt_ntt_is_id_kth_term_9:
    f:lpoly n
  -> k:nat{k < n}
  -> Lemma (ensures (intt_ntt_kth_term f k)
            == pow_mod_int #q n (-1) %* f.[k] %* n)
let intt_ntt_is_id_kth_term_9 f k =
  intt_ntt_is_id_kth_term_8 f k;
  Classical.forall_intro (intt_ntt_id_kth_term_9_aux f k);
  lemma_sum_zeros 0 k;
  lemma_sum_zeros (k+1) n

val intt_ntt_is_id_kth_term: 
    (f:lpoly n) 
  -> (k:nat{k < n}) 
  -> Lemma (ensures (f.[k]) == ((intt (ntt f)).[k]))
let intt_ntt_is_id_kth_term f k =
  intt_ntt_is_id_kth_term_9 f k;
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
    f:rq
  -> Lemma (requires True) (ensures equal f (intt (ntt f)))
let intt_ntt_is_id f =
  Classical.forall_intro (intt_ntt_is_id_kth_term f)

// val ntt_intt_is_id:
//     f:rq
//   -> Lemma (requires True) (ensures Seq.equal f (ntt (intt f)))
// let ntt_intt_is_id f =
//   admit()


let mul_componentwise (f g:rq) = createi n (fun i -> f.[i] %* g.[i])

val convolution_theorem_kth_term_ok_1:
    f:rq
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k 
            == sum_of_zqs 0 n (fun i -> (sum_of_zqs 0 n (fun j -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (f.[j] %* g.[(i - j) % n])))))
let convolution_theorem_kth_term_ok_1 f g k =
  ntt_kth_term_lemma (mul_quotient_ring f g) k;
  let lhs_inner_f = (fun i -> (mul_quotient_ring f g).[i] %* pow_psi (i * (2 * k + 1))) in
  let lhs_inner_f' = (fun i -> pow_psi (i * (2 * k + 1)) %* (sum_of_zqs 0 n (fun j -> (pow_mod_int_neg_one ((i - j) / n)) %* (f.[j] %* g.[(i - j) % n])))) in
  let f_i = fun i -> pow_psi (i * (2 * k + 1)) in
  let f_j = fun i j -> (pow_mod_int_neg_one ((i - j) / n)) %* (f.[j] %* g.[(i - j) % n]) in
  sum_rewrite_lemma 0 n lhs_inner_f lhs_inner_f';
  double_sum_mul_lemma 0 n 0 n f_i f_j
  
val convolution_theorem_kth_term_ok_2:
    f:rq
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* f.[j] %* g.[(i - j) % n]))))
let convolution_theorem_kth_term_ok_2 f g k =
  convolution_theorem_kth_term_ok_1 f g k;
  swap_sum_order 0 n 0 n (fun i j -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (f.[j] %* g.[(i - j) % n]))

#reset-options "--z3rlimit 20 --fuel 0 --ifuel 0"
val convolution_theorem_kth_term_ok_3_:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> f.[j] %* pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n])))
      )
let convolution_theorem_kth_term_ok_3_ f g k =
  convolution_theorem_kth_term_ok_2 f g k;
  // First step is to rearrange the terms in the inner sum so that we can apply our sum multiplication lemma
  let original = (fun j -> (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* f.[j] %* g.[(i - j) % n]))) in
  let original' = (fun j -> (sum_of_zqs 0 n (fun i -> f.[j] %* pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]))) in
  let lemma_aux (j:int): Lemma (ensures (original j == original' j)) =
    let first = (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* f.[j] %* g.[(i - j) % n]) in
    let second = (fun i -> f.[j] %* pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]) in
    let lemma_aux' (i:int): Lemma (ensures (first i == second i)) =
      lemma_mul_rearrange (pow_psi (i * (2 * k + 1))) (pow_mod_int_neg_one ((i - j) / n)) f.[j] g.[(i - j) % n] in
    Classical.forall_intro (lemma_aux') in
  Classical.forall_intro (lemma_aux);
  sum_rewrite_lemma 0 n original original'

val convolution_theorem_kth_term_ok_3:
  f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> f.[j] %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]))))
let convolution_theorem_kth_term_ok_3 f g k =
  convolution_theorem_kth_term_ok_3_ f g k;
  // First step is to rearrange the terms in the inner sum so that we can apply our sum multiplication lemma
  let original' = (fun j -> (sum_of_zqs 0 n (fun i -> f.[j] %* pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]))) in
  // Next step is to apply the sum multiplication lemma, and then we need to do an additional small step to remove the parenthesization
  let goal = (fun j -> f.[j] %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]))) in
  let lemma_aux2 (j:int): Lemma (ensures original' j == goal j) =
    sum_mul_lemma f.[j] 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]);
    let parenthesized = (fun i -> f.[j] %* (pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n])) in
    let unparenthesized = (fun i -> f.[j] %* pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]) in
    let lemma_aux2' (i:int): Lemma (ensures (parenthesized i == unparenthesized i)) =
      lemma_mul_assoc_big f.[j] (pow_psi (i * (2 * k + 1))) (pow_mod_int_neg_one ((i - j) / n)) g.[(i - j) % n] in
    Classical.forall_intro (lemma_aux2') in
  Classical.forall_intro (lemma_aux2);
  sum_rewrite_lemma 0 n original' goal


val convolution_theorem_kth_term_ok_4_:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> i:int
  -> Lemma 
      (requires True) 
      (ensures pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]
            == pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]
      )
let convolution_theorem_kth_term_ok_4_ f g k j i =
  lemma_pow_psi_identity (j * (2 * k + 1));
  assert (pow_psi (j * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) == 1);
  calc (==) {
    pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n];
    (==) {}
    pow_psi (i * (2 * k + 1)) %* 1 %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n];
    (==) {}
    pow_psi (i * (2 * k + 1)) %* (pow_psi (j * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1))) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n];
    (==) {}
    pow_psi (i * (2 * k + 1)) %* pow_psi (j * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n];
    (==) {}
    pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n];
  }

val convolution_theorem_kth_term_ok_4_aux_:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma 
      (requires True) 
      (ensures (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]))
            == (sum_of_zqs 0 n (fun i -> pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n])))
let convolution_theorem_kth_term_ok_4_aux_ f g k j =
  let original = (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]) in
  let goal = (fun i -> pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]) in
  Classical.forall_intro (convolution_theorem_kth_term_ok_4_ f g k j)

val convolution_theorem_kth_term_ok_4_aux:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma 
      (requires True) 
      (ensures f.[j] %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n]))
            == f.[j] %* (sum_of_zqs 0 n (fun i -> pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* g.[(i - j) % n])))
let convolution_theorem_kth_term_ok_4_aux f g k j =
  convolution_theorem_kth_term_ok_4_aux_ f g k j

// Adds pow_psi (j * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) = 1 into the inner sum
val convolution_theorem_kth_term_ok_4:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> f.[j] %* (sum_of_zqs 0 n (fun i -> pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))))
let convolution_theorem_kth_term_ok_4 f g k =
  convolution_theorem_kth_term_ok_3 f g k;
  Classical.forall_intro (convolution_theorem_kth_term_ok_4_aux f g k)

val convolution_theorem_kth_term_ok_5_aux_:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int

  -> Lemma 
      (requires True) 
      (ensures (sum_of_zqs 0 n (fun i -> pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))
            == pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]))))
let convolution_theorem_kth_term_ok_5_aux_ f g k j =
  let lemma_aux (i:int): Lemma (pow_psi (j * (2 * k + 1)) %* (pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]))
                             == pow_psi (j * (2 * k + 1)) %* pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])) = 
    lemma_mul_assoc_bigger (pow_psi (j * (2 * k + 1))) (pow_psi (i * (2 * k + 1))) (pow_psi (-j * (2 * k + 1))) (pow_mod_int_neg_one ((i - j) / n)) (g.[(i - j) % n]) in
  Classical.forall_intro lemma_aux;
  sum_mul_lemma (pow_psi (j * (2 * k + 1))) 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]))

val convolution_theorem_kth_term_ok_5_aux:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma 
      (requires True) 
      (ensures f.[j] %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (j * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))
            == f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]))))
let convolution_theorem_kth_term_ok_5_aux f g k j =
  convolution_theorem_kth_term_ok_5_aux_ f g k j

#reset-options "--z3rlimit 15 --fuel 0 --ifuel 0 --split_queries always"
// Moves pow_psi (j * (2 * k + 1)) out of the inner sum
val convolution_theorem_kth_term_ok_5:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))))
let convolution_theorem_kth_term_ok_5 f g k =
  convolution_theorem_kth_term_ok_4 f g k;
  assert (ntt_kth_term (mul_quotient_ring f g) k == sum_of_zqs 0 n (fun j -> f.[j] %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (j * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))));
  Classical.forall_intro (convolution_theorem_kth_term_ok_5_aux f g k);
  assert (ntt_kth_term (mul_quotient_ring f g) k == sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))))

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
val convolution_theorem_kth_term_ok_6_aux_aux_rewrite:
    f:rq 
  -> g:rq
  -> k:nat
  -> j:int
  -> i:int
  -> Lemma (pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])
         == pow_psi ((i - j) * (2*k+1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]))
let convolution_theorem_kth_term_ok_6_aux_aux_rewrite f g k j i =
  calc (==) {
    pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]);
    (==) {}
    (pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1))) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]);
    (==) {lemma_pow_mod_int_add #q psi (i * (2 * k + 1)) (-j * (2 * k + 1))}
    (pow_psi ((i - j) * (2 * k + 1))) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]);
    (==) {}
    (pow_psi ((i - j) * (2 * k + 1))) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]);
  }

val rearrange_6_aux_aux:
  a:int 
  -> b:int 
  -> c:int
  -> Lemma ((a * b) * c == b * (c * a))
let rearrange_6_aux_aux a b c = ()

val convolution_theorem_kth_term_ok_6_rewrite:
    f:rq 
  -> g:rq
  -> k:nat
  -> j:int
  -> i:int
  -> Lemma (pow_psi ((i - j) * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n))
         == pow_psi (((i - j) % n) * (2 * k + 1)))
let convolution_theorem_kth_term_ok_6_rewrite f g k j i = 
  let quot = (i - j) / n in 
  let r = (i - j) % n in 
  assert (i - j == quot * n + r);
  calc (==) {
    pow_psi ((quot * n + r) * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {ML.distributivity_add_left (quot * n) r (2 * k + 1)}
    pow_psi ((quot * n) * (2 * k + 1) + r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_int_add #q psi (quot * n * (2 * k + 1)) (r * (2 * k + 1))}
    pow_psi ((quot * n) * (2 * k + 1)) %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {rearrange_6_aux_aux quot n (2 * k + 1)}
    pow_psi (n * ((2 * k + 1) * quot)) %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_int_mul #q psi n ((2 * k + 1) * quot)}
    pow_mod_int #q (pow_psi n) ((2 * k + 1) * quot) %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
    pow_mod_int #q ((-1) % q) ((2 * k + 1) * quot) %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_int_mul #q ((-1) % q) (2 * k + 1) quot}
    pow_mod_int #q (pow_mod_int #q ((-1) % q) (2 * k + 1)) quot %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod_pos #q (2 * k + 1)}
    pow_mod_int #q (pow_mod_int_neg_one #q (2 * k + 1)) quot %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {}
    pow_mod_int #q ((-1) % q) quot %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int_neg_one (quot));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q quot}
    pow_mod_int #q ((-1) % q) quot %* pow_psi (r * (2 * k + 1)) %* (pow_mod_int #q ((-1) % q) quot);
    (==) {lemma_mul_zq_comm (pow_mod_int #q ((-1) % q) quot) (pow_psi (r * (2 * k + 1)))}
    pow_psi (r * (2 * k + 1)) %* pow_mod_int #q ((-1) % q) (quot) %* pow_mod_int #q ((-1) % q) (quot);
    (==) {lemma_mul_zq_assoc (pow_psi (r * (2 * k + 1))) (pow_mod_int #q ((-1) % q) (quot)) (pow_mod_int #q ((-1) % q) (quot))}
    pow_psi (r * (2 * k + 1)) %* (pow_mod_int #q ((-1) % q) (quot) %* pow_mod_int #q ((-1) % q) (quot));
    (==) {lemma_pow_mod_int_add #q ((-1) % q) quot quot}
    pow_psi (r * (2 * k + 1)) %* pow_mod_int #q ((-1) % q) (quot + quot);
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q (quot + quot)}
    pow_psi (r * (2 * k + 1)) %* pow_mod_int_neg_one (quot + quot);
    (==) {}
    pow_psi (r * (2 * k + 1));
  }

val convolution_theorem_kth_term_ok_6_inner_sum_aux:
    f:rq 
  -> g:rq 
  -> k:nat{k < n}
  -> j:int
  -> i:int 
  -> Lemma
      (pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])
    == pow_psi (((i - j) % n) * (2 * k + 1)) %* (g.[(i - j) % n]))
let convolution_theorem_kth_term_ok_6_inner_sum_aux f g k j i =
  calc (==) {
    pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]);
    (==) {convolution_theorem_kth_term_ok_6_aux_aux_rewrite f g k j i}
    pow_psi ((i - j) * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n]);
    (==) {}
    (pow_psi ((i - j) * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n))) %* (g.[(i - j) % n]);
    (==) {convolution_theorem_kth_term_ok_6_rewrite f g k j i}
    (pow_psi (((i - j) % n) * (2 * k + 1))) %* (g.[(i - j) % n]);
  }

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
val convolution_theorem_kth_term_ok_6_outer_sum_aux_helper:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      ((sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))
    == (sum_of_zqs 0 n (fun i -> pow_psi (((i - j) % n) * (2 * k + 1)) %* (g.[(i - j) % n]))))
let convolution_theorem_kth_term_ok_6_outer_sum_aux_helper f g k j =
  let original = (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])) in
  let goal = (fun i -> pow_psi (((i - j) % n) * (2 * k + 1)) %* (g.[(i - j) % n])) in
  Classical.forall_intro (convolution_theorem_kth_term_ok_6_inner_sum_aux f g k j)


val convolution_theorem_kth_term_ok_6_outer_sum_aux:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      (f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2 * k + 1)) %* pow_psi (-j * (2 * k + 1)) %* (pow_mod_int_neg_one ((i - j) / n)) %* (g.[(i - j) % n])))
    == f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (((i - j) % n) * (2*k+1)) %* (g.[(i - j) % n]))))
let convolution_theorem_kth_term_ok_6_outer_sum_aux f g k j =
  convolution_theorem_kth_term_ok_6_outer_sum_aux_helper f g k j

#reset-options "--z3rlimit 15 --fuel 0 --ifuel 0"
val convolution_theorem_kth_term_ok_6:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (((i - j) % n) * (2*k+1)) %* (g.[(i - j) % n])))))
let convolution_theorem_kth_term_ok_6 f g k =
  convolution_theorem_kth_term_ok_5 f g k;
  Classical.forall_intro (convolution_theorem_kth_term_ok_6_outer_sum_aux f g k)

val convolution_theorem_kth_term_ok_7_inner_sum_aux:
    f:rq
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      (sum_of_zqs 0 n (fun i -> pow_psi (((i - j) % n) * (2*k+1)) %* (g.[(i - j) % n]))
    == sum_of_zqs 0 n (fun i' -> pow_psi (i' * (2*k+1)) %* (g.[i'])))
let convolution_theorem_kth_term_ok_7_inner_sum_aux f g k j =
  let original = (fun i -> pow_psi (((i - j) % n) * (2*k+1)) %* (g.[(i - j) % n])) in
  let goal = (fun i' -> pow_psi (i' * (2*k+1)) %* (g.[i'])) in 
  lemma_sum_shift_mod n j goal


val convolution_theorem_kth_term_ok_7_outer_sum_aux:
    f:rq
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      (f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (((i - j) % n) * (2*k+1)) %* (g.[(i - j) % n])))
    == f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))))
let convolution_theorem_kth_term_ok_7_outer_sum_aux f g k j =
  convolution_theorem_kth_term_ok_7_inner_sum_aux f g k j

val convolution_theorem_kth_term_ok_7:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i])))))
let convolution_theorem_kth_term_ok_7 f g k =
  convolution_theorem_kth_term_ok_6 f g k;
  Classical.forall_intro (convolution_theorem_kth_term_ok_7_outer_sum_aux f g k)

val convolution_theorem_kth_term_ok_8_rewrite7_aux:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> j:int
  -> Lemma
      (f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i])))
    == (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))) %* (f.[j] %* pow_psi (j * (2 * k + 1))))
let convolution_theorem_kth_term_ok_8_rewrite7_aux f g k j = 
  calc (==) {
    f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i])));
    (==) {lemma_mul_mod_comm (f.[j] %* pow_psi (j * (2 * k + 1))) (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i])))}
    (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))) %* (f.[j] %* pow_psi (j * (2 * k + 1)));
  }

val convolution_theorem_kth_term_ok_8_rewrite7:
    f:rq
  -> g:rq
  -> k:nat{k < n}
  -> Lemma
       (sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))))
     == sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))) %* (f.[j] %* pow_psi (j * (2 * k + 1)))))
let convolution_theorem_kth_term_ok_8_rewrite7 f g k =
  Classical.forall_intro (convolution_theorem_kth_term_ok_8_rewrite7_aux f g k)

val convolution_theorem_kth_term_ok_8_apply_mul:
    f:rq
  -> g:rq  
  -> k:nat{k < n}
  -> Lemma
      (sum_of_zqs 0 n (fun j -> (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))) %* (f.[j] %* pow_psi (j * (2 * k + 1))))
   == (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))) %* (sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)))))
let convolution_theorem_kth_term_ok_8_apply_mul f g k =
  sum_mul_lemma (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))) 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)))

val convolution_theorem_kth_term_ok_8_comm:
    f:rq
  -> g:rq  
  -> k:nat{k < n}
  -> Lemma
      ((sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))) %* (sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1))))
    == (sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)))) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))))
let convolution_theorem_kth_term_ok_8_comm f g k = ()

val convolution_theorem_kth_term_ok_8:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == (sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)))) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))))
let convolution_theorem_kth_term_ok_8 f g k =
  convolution_theorem_kth_term_ok_7 f g k;
  convolution_theorem_kth_term_ok_8_rewrite7 f g k;
  convolution_theorem_kth_term_ok_8_apply_mul f g k;
  convolution_theorem_kth_term_ok_8_comm f g k

val convolution_theorem_kth_term_ok_9:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == ntt_kth_term f k %* ntt_kth_term g k)
let convolution_theorem_kth_term_ok_9 f g k =
  convolution_theorem_kth_term_ok_8 f g k

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"
val convolution_theorem_kth_term_ok:
    f:rq
  -> g:rq
  -> k:nat
  -> Lemma 
      (requires True) 
      (ensures (ntt_kth_term (mul_quotient_ring f g) k == ntt_kth_term f k %* ntt_kth_term g k))
let convolution_theorem_kth_term_ok f g k =
  if 0 <= k && k < n then 
    convolution_theorem_kth_term_ok_9 f g k
  else ()

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0 --split_queries always"
val convolution_theorem:
    f:rq
  -> g:rq
  -> Lemma 
      (requires True) 
      (ensures equal 
        (ntt (mul_quotient_ring f g))
        (mul_componentwise (ntt f) (ntt g)))
let convolution_theorem f g =
  Classical.forall_intro (convolution_theorem_kth_term_ok f g);
  let lhs = ntt (mul_quotient_ring f g) in
  let rhs = mul_componentwise (ntt f) (ntt g) in
  assert (forall (i:nat{i < n}).{:pattern (lhs.[i]); (rhs.[i])} (lhs.[i] == rhs.[i]))

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"
val mul_ntt_ok:
    f:rq
  -> g:rq
  -> Lemma 
      (requires True) 
      (ensures Seq.equal 
        (mul_quotient_ring f g) 
        (intt (mul_componentwise (ntt f) (ntt g))))
let mul_ntt_ok f g =
  convolution_theorem f g;
  assert (Seq.equal
            (intt (ntt (mul_quotient_ring f g))) 
            (intt (mul_componentwise (ntt f) (ntt g))));
  intt_ntt_is_id (mul_quotient_ring f g);
  assert (mul_quotient_ring f g == intt (mul_componentwise (ntt f) (ntt g)))
  
