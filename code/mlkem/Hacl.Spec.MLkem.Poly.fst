module Hacl.Spec.MLkem.Poly
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let n: int = 256
let q: int = 3329
let m: int = (pow2 32) / q
let zq = x:int{ x < q && x >= 0 }

let lpoly deg = lseq zq deg
let rq = lpoly n

let zero deg = create deg 0
let one deg = create deg 1

val add_zq: a:zq -> b:zq -> zq
let add_zq a b = (a + b) % q

val mul_zq: a:zq -> b:zq -> zq
let mul_zq a b = (a * b) % q

val neg_zq: a:zq -> zq
let neg_zq a = 
  if a = 0 then 0
  else q - a

val sub_zq: a:zq -> b:zq -> zq
let sub_zq a b = add_zq a (neg_zq b)

let poly_index #deg (p:lpoly deg) (i:int) : zq =
  if 0 <= i && i < length p then 
  index p i
  else 0

val add:
    #deg:size_nat
  -> a:lpoly deg
  -> b:lpoly deg
  -> lpoly deg
let add #deg a b =
  createi deg (fun i -> add_zq (index a i) (index b i))

let test_add =
  let a: lpoly 2 = Seq.cons 1 (Seq.cons 2 Seq.empty) in
  let b: lpoly 2 = Seq.cons 3 (Seq.cons 5 Seq.empty) in
  let c: lpoly 2 = add a b in
  assert (length c = 2);
  assert (index c 0 = 4);
  assert (index c 1 = 7)

val add_rq: a:rq -> b:rq -> rq
let add_rq a b = add #n a b

// T_q is the image of R_q under the Number Theoretic Transform
let tq = lseq (lpoly 2) 128

let index_tq (t:tq) (i:size_nat{i < 256}) : zq =
  let p2 = index t (i / 2) in
  index p2 (i % 2)

let upd_tq (t:tq) (i:size_nat{i < 256}) (v:zq) : tq =
  let p2 = index t (i / 2) in
  let p2_upd = upd p2 (i % 2) v in
  upd t (i / 2) p2_upd

val scalar_mul:
    #deg:size_nat
  -> p:lpoly deg
  -> c:zq
  -> lpoly deg
let scalar_mul #deg p c =
  createi deg (fun i -> mul_zq c (index p i))

val kth_coeff_ith_component: 
    #deg:size_nat
  -> a: lpoly deg
  -> b: lpoly deg
  -> k:int{ 0 <= k && k < deg}
  -> i:int{ 0 <= i && i < deg}
  -> zq
let kth_coeff_ith_component #deg a b k i =
  if 0 <= i - k then
    mul_zq (index a k) (index b (i - k))
  else
    neg_zq (mul_zq (index a k) (index b (deg + (i - k))))

val sum_coefficients_to_i:
    #deg:size_nat
  -> a:lpoly deg
  -> b:lpoly deg
  -> k:int{ 0 <= k && k < deg}
  -> i:int{ 0 <= i && i < deg}
  -> zq
let rec sum_coefficients_to_i #deg a b k i =
  if i = 0 then
    kth_coeff_ith_component a b k i
  else
    add_zq (kth_coeff_ith_component a b k i) (sum_coefficients_to_i a b k (i - 1))

val mul_ab_kth_coeff:
    #deg:size_nat 
  -> a:lpoly deg
  -> b:lpoly deg
  -> k:int{ 0 <= k && k < deg}
  -> zq
let mul_ab_kth_coeff #deg a b k =
  sum_coefficients_to_i a b k (deg - 1)

// Multiplication of polynomials should be done mod X^deg- 1
val mul_quotient_ring:
    #deg:size_nat
  -> a:lpoly deg
  -> b:lpoly deg
  -> lpoly deg
let mul_quotient_ring #deg a b =
  createi deg (fun i -> mul_ab_kth_coeff a b i)

let zeta = 17
let bit7 = lseq bool 7

let bitrev7 (bits:bit7): bit7 =
  createi 7 (fun i -> index bits (6 - i))

let bit (b:bool): b:nat{b = 0 || b = 1} = if b then 1 else 0

let bit7_v (bits:bit7): r:nat{r < 128} =
  let r0 = bit (index bits 0) in 
  let r1 = bit (index bits 1) in
  let r2 = bit (index bits 2) in
  let r3 = bit (index bits 3) in
  let r4 = bit (index bits 4) in
  let r5 = bit (index bits 5) in
  let r6 = bit (index bits 6) in
  r0 + 2 * r1 + 4 * r2 + 8 * r3 + 16 * r4 + 32 * r5 + 64 * r6

let bitrev_ok (bits:bit7): Lemma 
  (requires True) 
  (ensures (
    let rev = bitrev7 bits in
    forall (i:nat{ i < 7 }). (index bits i = index rev (6 - i))
  )) = ()

let get_bit (bits:nat{ bits < 128}) (i:nat{i < 7}): b:nat{b = 0 || b = 1 } =
  bits / (pow2 i) % 2

let bitsequence (i:nat{ i < 128}): bit7 =
  createi 7 (fun j -> (get_bit i j) = 1)

let bitrev7_int (bits:nat{bits < 128}): result:nat{result < 128} =
  bit7_v (bitrev7 (bitsequence bits))

// Types specifying the possible values of the length and start parameters
type len_t = l:nat{l = 2 || l = 4 || l = 8 || l = 16 || l = 32 || l = 64 || l = 128}
type start_t (len:len_t) = s:nat{s % (2*len) = 0 && s < 256}

// These just convert between the two representations of polynomials, such that 
// f[2i] = p[i][0] and f[2i+1] = p[i][1] (does not do the actual NTT)
let rq_to_tq (f:rq): tq =
  createi 128 (fun i ->
    let f0 = index f (2 * i) in
    let f1 = index f (2 * i + 1) in
    let p: lpoly 2 = cons f0 (cons f1 empty) in
    p
  )
let tq_to_rq (f:tq): rq =
  createi 256 (fun i ->
    let p = index f (i / 2) in
    if i % 2 = 0 then
      index p 0
    else
      index p 1
  )
let tq_eq (f g: tq) = 
  let f_rq = tq_to_rq f in
  let g_rq = tq_to_rq g in
  Seq.equal f_rq g_rq

val ntt_inner_inner:
    z:zq
  -> f:tq
  -> j:nat
  -> len:len_t
  -> start:start_t len
  -> Tot (tq) (decreases (start + len) - j)
let rec ntt_inner_inner z f j len start: tq =
  // for j <- start; j < start + len; j++
  if j < (start + len) then
    // t <- zeta * f_hat[j+ len]
    let t = mul_zq z (index_tq f (j + len)) in
    let f_j = index_tq f j in
    // f_hat[j + len] <- f_hat[j] - t
    let f_upd = upd_tq f (j + len) (add_zq f_j (neg_zq t)) in
    // f_hat[j] <- f_hat[j] + t
    let f_upd_upd = upd_tq f_upd j (add_zq f_j t) in
    ntt_inner_inner z f_upd_upd (j + 1) len start
  else
    f

val zeta_to_k:
    k:nat{k < 128}
  -> zq
let zeta_to_k k = pow_mod #q zeta k
let test = 
  let zeta_0 = pow_mod #q zeta 0 in
  pow_mod_def #q zeta 0;
  lemma_pow_mod #q zeta 0;
  lemma_pow0 zeta;
  assert (zeta_0 = 1);
  ()

val zeta_to_k_pos_lemma: (k:nat{k > 0 && k < 128}) -> Lemma (requires True) (ensures (zeta_to_k k = mul_zq (zeta_to_k (k - 1)) zeta))
let zeta_to_k_pos_lemma k = 
  pow_mod_def #q zeta k;
  lemma_pow_mod #q zeta k;
  lemma_pow_unfold zeta k;
  assert (pow zeta k % q = zeta_to_k k);
  assert (zeta * pow zeta (k - 1) % q = zeta_to_k k);
  lemma_pow_mod #q zeta (k - 1);
  assert (pow zeta (k - 1) % q = zeta_to_k (k - 1));
  ()

val ntt_outer_inner_body:
    f:tq
  -> len:len_t
  -> start:start_t len
  -> k:nat{k < 128}
  -> tq
let ntt_outer_inner_body f len start k = 
  // zeta <- Zeta ^ (BitRev7(k)) mod q
  let z = pow_mod #q zeta (bitrev7_int k) in
  let f_upd = ntt_inner_inner z f start len start in
  f_upd

val ntt_outer_inner:
    f:tq
  -> len:len_t
  -> start:start_t len
  -> Tot (tq) (decreases (256 - 2 * len) - start)
let rec ntt_outer_inner f len start =
  let k = (128 / len) + (start / (2 * len)) in
  let f_upd:tq = ntt_outer_inner_body f len start k in
  if start + 2 * len >= 256 then 
    f_upd
  else
    ntt_outer_inner f_upd len (start + 2 * len)

val ntt_outer:
    len:len_t
  -> f:tq
  -> Tot tq (decreases len)
let rec ntt_outer len f =
  let f_upd = ntt_outer_inner f len 0 in
  if len = 2 then
    f_upd
  else
    ntt_outer (len / 2) f_upd

let ntt (f:rq): tq =
  let ntt_image = ntt_outer 128 (rq_to_tq f) in 
  ntt_image

val intt_inner_inner:
    z:zq
  -> f:tq
  -> j:nat
  -> len:len_t
  -> start:start_t len
  -> Tot (tq) (decreases (start + len) - j)
let rec intt_inner_inner z f j len start: tq =
  // for j <- start; j < start + len; j++
  if j < (start + len) then
    // t <- zeta * f_hat[j+ len]
    let t = (index_tq f j) in 
    // f[j] <- t + f[j+len]
    let f_j = add_zq t (index_tq f (j + len)) in
    let f_upd = upd_tq f j f_j in
    // f[j+len] <- zeta * (f[j+len] - t)
    let f_j_len = mul_zq z (add_zq (index_tq f (j + len)) (neg_zq t)) in
    let f_upd_upd = upd_tq f_upd (j + len) f_j_len in
    intt_inner_inner z f_upd_upd (j + 1) len start
  else
    f

val intt_outer_inner_body:
    f:tq
  -> len:len_t
  -> start:start_t len
  -> k:nat{k < 128}
  -> tq
let intt_outer_inner_body f len start k =
  // zeta <- Zeta ^ (BitRev7(k)) mod q
  let z = pow_mod #q zeta (bitrev7_int k) in
  let f_upd = intt_inner_inner z f start len start in
  f_upd


val intt_outer_inner:
    f:tq
  -> len:len_t
  -> start:start_t len
  -> Tot tq (decreases (256 - 2 * len) - start)
let rec intt_outer_inner f len start =
  let k = (256 / len) - (start / (2 * len)) - 1 in
  // zeta <- Zeta ^ (BitRev7(k)) mod q
  let z = pow_mod #q zeta (bitrev7_int k) in
  let f_upd = intt_outer_inner_body f len start k in
  if start + 2 * len >= 256 then
    f_upd
  else
    intt_outer_inner f_upd len (start + 2 * len)

val intt_outer:
    len:len_t
  -> f:tq
  -> Tot tq (decreases (128 - len))
let rec intt_outer len f =
  let f_upd = intt_outer_inner f len 0 in
  if len = 128 then
    f_upd
  else
    intt_outer (len * 2) f_upd

val intt:
    f:tq
  -> rq
let intt f =
  let intt_image = intt_outer 128 f in 
  let unscaled_intt = tq_to_rq intt_image in
  scalar_mul unscaled_intt 3303

// NTT multiplication specification
// i-th coordinate in Tq of the product hat(h) = hat(f) x_Tq hat(g) is given by:
//    hat(h)[2i] + hat(h)[2i+1] = (hat(f)[2i]+hat(f)[2i+1]X) * (hat(g)[2i]+hat(g)[2i+1]X) mod (X^2 - zeta^(2 BitRev_7(i)+1))

// index f i should yield an lpoly 2 which is equivalent to f[2i]+f[2i+1]X
// ntt_mul_base calculates the product of two lpoly 2 with modulus X^2 - gamma
let ntt_mul_base (a b:lpoly 2) (gamma: zq): lpoly 2 =
  let c0 = add_zq (mul_zq (index a 0) (index b 0)) (mul_zq gamma (mul_zq (index a 1) (index b 1))) in
  let c1 = add_zq (mul_zq (index a 0) (index b 1)) (mul_zq (index a 1) (index b 0)) in
  cons c0 (cons c1 empty)

val ntt_mul:
    f:tq
  -> g:tq
  -> tq 
let ntt_mul f g =
  createi 128 (fun i -> 
    let gamma = pow_mod #q zeta ((2 * bit7_v (bitrev7 (bitsequence i))) + 1) in
    ntt_mul_base (index f i) (index g i) gamma
    )

val ntt_mul_ok:
    f:rq
  -> g:rq
  -> Lemma (requires True) (ensures (intt (ntt_mul (ntt f) (ntt g)) = mul_quotient_ring f g))


// NTT correctness specification.
// hat(f) := (f mod (X^2 - zeta^(2 BitRev_7(0)+1)), ... , f mod (X^2 - zeta^(2 BitRev_7(127)+1)))
// val ntt:
//     a:rq
//   -> Pure (tq) (requires True) (ensures (fun r -> r = a))


// val prev_step:
//     deg:size_nat
//   -> i:int{ 0 <= i && i < deg}
//   -> j:int{ 0 <= j && j < deg}
//   -> tuple2 int int
// let prev_step deg i j =
//   if j = 0 then
//     (i - 1, deg - 1)
//   else
//     (i, j - 1)

// val mul_intermediate:
//     #deg:size_nat
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> i:int{ 0 <= i && i < deg}
//   -> j:int{ 0 <= j && j < deg}
//   -> lpoly deg
// let rec mul_intermediate #deg a b i j =
//   let c = mul_zq (index a i) (index b j) in
//   if i + j = 0 then 
//     let res = create deg 0 in
//     upd res 0 c
//   else
//     let (prev_i, prev_j) = prev_step deg i j in
//     let res = mul_intermediate a b prev_i prev_j in
//     upd res ((i + j) % deg) (add_zq c (index res ((i + j) % deg)))

// val mul: 
//     #deg:size_nat
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> lpoly deg
// let mul #deg a b = 
//   if deg = 0 then 
//     create 0 0
//   else
//     mul_intermediate a b (deg - 1) (deg - 1)


let test1 = 
  let a: lpoly 1 = 
  let m = mul_zq 1 2 in
  let res = create 1 0 in 
  upd res 0 m in
  assert (index a 0 = 2);
  assert (length a = 1);
  assert (Seq.equal a (Seq.cons 2 Seq.empty))

// val mul_equal_3_: Lemma () 
  
#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let test2 = 
  let a: lpoly 1 = Seq.cons 1 Seq.empty in
  let b: lpoly 1 = Seq.cons 3 Seq.empty in
  let p: lpoly 1 = mul_quotient_ring a b in
  assert (index p 0 = mul_ab_kth_coeff a b 0)


// let a: lpoly 2 = Seq.cons 1 (Seq.cons 2 Seq.empty)
// let b: lpoly 2 = Seq.cons 3 (Seq.cons 5 Seq.empty)
// let c: lpoly 2 = mul a b
// let _ = 
//   assert (length c = 2);
//   assert (index c 0 = 11)