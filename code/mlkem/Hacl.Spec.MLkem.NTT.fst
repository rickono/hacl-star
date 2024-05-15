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

// let pow_mod_int_neg_one (n:int): zq =
//   // pow_mod #q (neg_zq 1) (int_to_zq n)
//   if n % 2 = 0 then 1 else ((-1) % q)

val lemma_rewrite_pow_psi_conv_theorem:
    i:int
  -> j:int 
  -> k:int
  -> Lemma (pow_mod_int_neg_one ((i - j) / n) %* pow_psi ((i - j) * (2 * k + 1))
         == pow_psi ((i - j % n) * (2 * k + 1)))
let lemma_rewrite_pow_psi_conv_theorem i j k = admit()

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

// If we have a polynomial a = a_0 + a_1 * X + a_2 * X^2 + a_3 * X^3 + ... + a_n-1 * X^n-1
// then the NTT should be  a*_k = sum_{j=0}^{n-1} a_j * omega_n^(j*k),
// where omega_n is the nth root of unity
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
  else sum_of_zqs 0 (n-1) (fun i -> mul_zq (f.[i]) (pow_psi (-k * (2 * i + 1))))

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
let intt_ntt_kth_term f k = 
  sum_of_zqs 0 (n-1) (fun i -> mul_zq (ntt_kth_term f i) (pow_psi (-k * (2 * i + 1)))) / n

val intt_ntt_is_id_kth_term: 
    (f:lpoly n) 
  -> (k:nat{k < n}) 
  -> Lemma (ensures (f.[k]) == ((intt (ntt f)).[k]))
let intt_ntt_is_id_kth_term f k =
  let rhs = intt_ntt_kth_term f k in
  assert (rhs == sum_of_zqs 0 (n-1) (fun i -> mul_zq (ntt_kth_term f i) (pow_psi (-k * (2 * i + 1)))) / n);
  admit()

val intt_ntt_is_id:
    f:rq
  -> Lemma (requires True) (ensures Seq.equal f (intt (ntt f)))
let intt_ntt_is_id f =
  admit()


val ntt_intt_is_id:
    f:rq
  -> Lemma (requires True) (ensures Seq.equal f (ntt (intt f)))
let ntt_intt_is_id f =
  admit()


let mul_componentwise (f g:rq) = createi n (fun i -> f.[i] %* g.[i])

#reset-options "--z3rlimit 15 --fuel 2 --ifuel 0"
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

#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
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

#reset-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
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
  Classical.forall_intro (convolution_theorem_kth_term_ok_6_inner_sum_aux f g k j);
  sum_rewrite_lemma 0 n original goal

#reset-options "--z3rlimit 15 --fuel 0 --ifuel 0"
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

val convolution_theorem_kth_term_ok_7:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i])))))
let convolution_theorem_kth_term_ok_7 f g k =
  admit()

val convolution_theorem_kth_term_ok_8:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == (sum_of_zqs 0 n (fun j -> f.[j] %* pow_psi (j * (2 * k + 1)))) %* (sum_of_zqs 0 n (fun i -> pow_psi (i * (2*k+1)) %* (g.[i]))))
let convolution_theorem_kth_term_ok_8 f g k =
  admit()

val convolution_theorem_kth_term_ok_9:
    f:rq 
  -> g:rq
  -> k:nat{k < n}
  -> Lemma 
      (requires True) 
      (ensures ntt_kth_term (mul_quotient_ring f g) k
            == ntt_kth_term f k %* ntt_kth_term g k)
let convolution_theorem_kth_term_ok_9 f g k =
  admit()

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
  // assert (forall (i:nat{i < n}).{:pattern (lhs.[i])} (lhs.[i] == ntt_kth_term (mul_quotient_ring f g) i));
  // assert (forall (i:nat{i < n}).{:pattern (rhs.[i])} (rhs.[i] == (ntt f).[i] %* (ntt g).[i]));
  assert (forall (i:nat{i < n}).{:pattern (lhs.[i]); (rhs.[i])} (lhs.[i] == rhs.[i]))


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
  


// val ntt_inner_inner:
//     z:zq
//   -> f:tq
//   -> j:nat
//   -> len:len_t
//   -> start:start_t len
//   -> Tot (tq) (decreases (start + len) - j)
// let rec ntt_inner_inner z f j len start: tq =
//   // for j <- start; j < start + len; j++
//   if j < (start + len) then
//     // t <- zeta * f_hat[j+ len]
//     let t = mul_zq z (index_tq f (j + len)) in
//     let f_j = index_tq f j in
//     // f_hat[j + len] <- f_hat[j] - t
//     let f_upd = upd_tq f (j + len) (add_zq f_j (neg_zq t)) in
//     // f_hat[j] <- f_hat[j] + t
//     let f_upd_upd = upd_tq f_upd j (add_zq f_j t) in
//     ntt_inner_inner z f_upd_upd (j + 1) len start
//   else
//     f

// val ntt_inner_inner_f (j:nat{j < 256}) (len:len_t) (start:start_t len) (z:zq) (f:tq): zq
// let ntt_inner_inner_f j len start z f =
//     if j < start || j >= start + 2 * len then
//       index_tq f j
//     else if j >= start && j < start + len then
//       let t = mul_zq z (index_tq f (j + len)) in
//       add_zq (index_tq f j) t
//     else
//       let t = mul_zq z (index_tq f j) in
//       add_zq (index_tq f (j - len)) (neg_zq t)


// val ntt_inner_inner_func:
//     z:zq 
//   -> f:tq 
//   -> len:len_t
//   -> start:start_t len
//   -> tq
// let ntt_inner_inner_func z f len start = 
//   let rq_rep = createi #zq 256 (fun j -> ntt_inner_inner_f j len start z f) in rq_to_tq rq_rep

// // val ntt_inner_inner_func_ok: 
// //     z:zq
// //   -> f:tq
// //   -> len:len_t
// //   -> start:start_t len
// //   -> Lemma (ensures ntt_inner_inner z f start len start = ntt_inner_inner_func z f len start)
// // let ntt_inner_inner_func_ok z f len start = ()

// val zeta_to_k:
//     k:nat{k < 128}
//   -> zq
// let zeta_to_k k = pow_mod #q zeta k
// let test = 
//   let zeta_0 = pow_mod #q zeta 0 in
//   pow_mod_def #q zeta 0;
//   lemma_pow_mod #q zeta 0;
//   lemma_pow0 zeta;
//   assert (zeta_0 = 1);
//   ()

// val zeta_to_k_pos_lemma: (k:nat{k > 0 && k < 128}) -> Lemma (requires True) (ensures (zeta_to_k k = mul_zq (zeta_to_k (k - 1)) zeta))
// let zeta_to_k_pos_lemma k = 
//   pow_mod_def #q zeta k;
//   lemma_pow_mod #q zeta k;
//   lemma_pow_unfold zeta k;
//   assert (pow zeta k % q = zeta_to_k k);
//   assert (zeta * pow zeta (k - 1) % q = zeta_to_k k);
//   lemma_pow_mod #q zeta (k - 1);
//   assert (pow zeta (k - 1) % q = zeta_to_k (k - 1));
//   ()

// val ntt_outer_inner_body:
//     f:tq
//   -> len:len_t
//   -> start:start_t len
//   -> k:nat{k < 128}
//   -> tq
// let ntt_outer_inner_body f len start k = 
//   // zeta <- Zeta ^ (BitRev7(k)) mod q
//   let z = pow_mod #q zeta (bitrev7_int k) in
//   let f_upd = ntt_inner_inner z f start len start in
//   f_upd

// val ntt_outer_inner:
//     f:tq
//   -> len:len_t
//   -> start:start_t len
//   -> Tot (tq) (decreases (256 - 2 * len) - start)
// let rec ntt_outer_inner f len start =
//   let k = (128 / len) + (start / (2 * len)) in
//   let f_upd:tq = ntt_outer_inner_body f len start k in
//   if start + 2 * len >= 256 then 
//     f_upd
//   else
//     ntt_outer_inner f_upd len (start + 2 * len)

// val ntt_outer:
//     len:len_t
//   -> f:tq
//   -> Tot tq (decreases len)
// let rec ntt_outer len f =
//   let f_upd = ntt_outer_inner f len 0 in
//   if len = 2 then
//     f_upd
//   else
//     ntt_outer (len / 2) f_upd

// val len_t_lemma: (i:nat{i < 7}) -> 
//   Lemma (ensures pow2 i = 2 || pow2 i = 4 || pow2 i = 8 || pow2 i = 16 || pow2 i = 32 || pow2 i = 64)
// let len_t_lemma i = admit()

// val ntt_outer_intermediate:
//     f:tq
//   -> i:nat{i < 7}
//   -> Tot tq (decreases i)
// let rec ntt_outer_intermediate f i =
//   len_t_lemma (6-i);
//   let len:len_t = 128 / (pow2 (6-i)) in
//   let f_upd = ntt_outer_inner f len 0 in
//   if i = 0 then
//     f_upd
//   else
//     ntt_outer_intermediate f_upd (i-1)

// // val ntt_outer_int_ok: 
// //     f:tq
// //   -> Lemma (requires True) (ensures (ntt_outer 128 f = ntt_outer_intermediate f 6))
// // let ntt_outer_int_ok f =
// //   assert (ntt_outer 2 f = ntt_outer_intermediate f 0);
// //   ()

// let ntt (f:rq): tq =
//   let ntt_image = ntt_outer 128 (rq_to_tq f) in 
//   ntt_image

// val intt_inner_inner:
//     z:zq
//   -> f:tq
//   -> j:nat
//   -> len:len_t
//   -> start:start_t len
//   -> Tot (tq) (decreases (start + len) - j)
// let rec intt_inner_inner z f j len start: tq =
//   // for j <- start; j < start + len; j++
//   if j < (start + len) then
//     // t <- zeta * f_hat[j+ len]
//     let t = (index_tq f j) in 
//     // f[j] <- t + f[j+len]
//     let f_j = add_zq t (index_tq f (j + len)) in
//     let f_upd = upd_tq f j f_j in
//     // f[j+len] <- zeta * (f[j+len] - t)
//     let f_j_len = mul_zq z (add_zq (index_tq f (j + len)) (neg_zq t)) in
//     let f_upd_upd = upd_tq f_upd (j + len) f_j_len in
//     intt_inner_inner z f_upd_upd (j + 1) len start
//   else
//     f

// val intt_outer_inner_body:
//     f:tq
//   -> len:len_t
//   -> start:start_t len
//   -> k:nat{k < 128}
//   -> tq
// let intt_outer_inner_body f len start k =
//   // zeta <- Zeta ^ (BitRev7(k)) mod q
//   let z = pow_mod #q zeta (bitrev7_int k) in
//   let f_upd = intt_inner_inner z f start len start in
//   f_upd


// val intt_outer_inner:
//     f:tq
//   -> len:len_t
//   -> start:start_t len
//   -> Tot tq (decreases (256 - 2 * len) - start)
// let rec intt_outer_inner f len start =
//   let k = (256 / len) - (start / (2 * len)) - 1 in
//   // zeta <- Zeta ^ (BitRev7(k)) mod q
//   let z = pow_mod #q zeta (bitrev7_int k) in
//   let f_upd = intt_outer_inner_body f len start k in
//   if start + 2 * len >= 256 then
//     f_upd
//   else
//     intt_outer_inner f_upd len (start + 2 * len)

// val intt_outer:
//     len:len_t
//   -> f:tq
//   -> Tot tq (decreases (128 - len))
// let rec intt_outer len f =
//   let f_upd = intt_outer_inner f len 0 in
//   if len = 128 then
//     f_upd
//   else
//     intt_outer (len * 2) f_upd

// val intt:
//     f:tq
//   -> rq
// let intt f =
//   let intt_image = intt_outer 128 f in 
//   let unscaled_intt = tq_to_rq intt_image in
//   scalar_mul unscaled_intt 3303

// // NTT multiplication specification
// // i-th coordinate in Tq of the product hat(h) = hat(f) x_Tq hat(g) is given by:
// //    hat(h)[2i] + hat(h)[2i+1] = (hat(f)[2i]+hat(f)[2i+1]X) * (hat(g)[2i]+hat(g)[2i+1]X) mod (X^2 - zeta^(2 BitRev_7(i)+1))

// // index f i should yield an lpoly 2 which is equivalent to f[2i]+f[2i+1]X
// // ntt_mul_base calculates the product of two lpoly 2 with modulus X^2 - gamma
// let ntt_mul_base (a b:lpoly 2) (gamma: zq): lpoly 2 =
//   let c0 = add_zq (mul_zq (index a 0) (index b 0)) (mul_zq gamma (mul_zq (index a 1) (index b 1))) in
//   let c1 = add_zq (mul_zq (index a 0) (index b 1)) (mul_zq (index a 1) (index b 0)) in
//   cons c0 (cons c1 empty)
