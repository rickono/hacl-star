module Hacl.Spec.MLkem.Poly
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence

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

val add_rq: a:rq -> b:rq -> rq
let add_rq a b = add #n a b

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
    mul_zq (index a k) (index b (deg + (i - k)))

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
val mul:
    #deg:size_nat
  -> a:lpoly deg
  -> b:lpoly deg
  -> lpoly deg
let mul #deg a b =
  createi deg (fun i -> mul_ab_kth_coeff a b i)