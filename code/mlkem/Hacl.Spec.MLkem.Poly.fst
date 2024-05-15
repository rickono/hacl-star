module Hacl.Spec.MLkem.Poly
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max
open Hacl.Spec.MLkem.Zq
open Hacl.Spec.MLkem.Sums

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let lpoly deg = lseq zq deg
let rq = lpoly n

let zero deg = create deg 0
let one deg = create deg 1

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
// let tq = lseq (lpoly 2) 128
let tq = lseq zq 256

// let index_tq (t:tq) (i:size_nat{i < 256}) : zq =
//   let p2 = index t (i / 2) in
//   index p2 (i % 2)
let index_tq (t:tq) (i:size_nat{i < 256}) : zq = index t i

// let upd_tq (t:tq) (i:size_nat{i < 256}) (v:zq) : tq =
//   let p2 = index t (i / 2) in
//   let p2_upd = upd p2 (i % 2) v in
//   upd t (i / 2) p2_upd
let upd_tq (t:tq) (i:size_nat{i < 256}) (v:zq) : tq = upd t i v

let rq_to_tq (f:rq) = f
let tq_to_rq (f:tq) = f
let tq_eq (f g: tq) = Seq.equal f g

val scalar_mul:
    #deg:size_nat
  -> p:lpoly deg
  -> c:zq
  -> lpoly deg
let scalar_mul #deg p c =
  createi deg (fun i -> mul_zq c (index p i))

// val kth_coeff_ith_component: 
//     #deg:size_nat
//   -> a: lpoly deg
//   -> b: lpoly deg
//   -> k:int{ 0 <= k && k < deg}
//   -> i:int{ 0 <= i && i < deg}
//   -> zq
// let kth_coeff_ith_component #deg a b k i =
//   if 0 <= i - k then
//     mul_zq (index a k) (index b (i - k))
//   else
//     neg_zq (mul_zq (index a k) (index b (deg + (i - k))))

// val sum_coefficients_to_i:
//     #deg:size_nat
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> k:int{ 0 <= k && k < deg}
//   -> i:int{ 0 <= i && i < deg}
//   -> zq
// let rec sum_coefficients_to_i #deg a b k i =
//   if i = 0 then
//     kth_coeff_ith_component a b k i
//   else
//     add_zq (kth_coeff_ith_component a b k i) (sum_coefficients_to_i a b k (i - 1))

// val mul_ab_kth_coeff:
//     #deg:size_nat 
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> k:int{ 0 <= k && k < deg}
//   -> zq
// let mul_ab_kth_coeff #deg a b k =
//   sum_coefficients_to_i a b k (deg - 1)

// // Multiplication of polynomials should be done mod X^deg- 1
// val mul_quotient_ring:
//     #deg:size_nat
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> lpoly deg
// let mul_quotient_ring #deg a b =
//   createi deg (fun i -> mul_ab_kth_coeff a b i)

unfold
let (.[]) = poly_index #n

val poly_index_lemma (p:lpoly n) (i:int{0 <= i && i < n}) : 
  Lemma (p.[i] = index p i)
  [SMTPat p.[i]]
let poly_index_lemma p i = ()

val poly_equal (p q: lpoly n) :
  Lemma 
    (requires (forall (i:nat{i < n}). (p.[i] == q.[i])))
    (ensures equal p q)
let poly_equal p q = 
  assert (length p = n);
  assert (forall (i:nat{i < n}). (p.[i] == index p i));
  assert (forall (i:nat{i < n}). (q.[i] == index q i));
  assert (forall (i:nat{i < n}). (index p i == index q i))
