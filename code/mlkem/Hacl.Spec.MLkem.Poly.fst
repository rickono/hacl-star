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
// val mul:
//     #deg:size_nat
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> lpoly deg
// let mul #deg a b =
//   createi deg (fun i -> mul_ab_kth_coeff a b i)

val prev_step:
    deg:size_nat
  -> i:int{ 0 <= i && i < deg}
  -> j:int{ 0 <= j && j < deg}
  -> tuple2 int int
let prev_step deg i j =
  if j = 0 then
    (i - 1, deg - 1)
  else
    (i, j - 1)

val mul_intermediate:
    #deg:size_nat
  -> a:lpoly deg
  -> b:lpoly deg
  -> i:int{ 0 <= i && i < deg}
  -> j:int{ 0 <= j && j < deg}
  -> Tot (lpoly deg) (decreases ((deg * i) + j))
let rec mul_intermediate #deg a b i j =
  let c = mul_zq (index a i) (index b j) in
  if i + j = 0 then 
    let res = create deg 0 in
    upd res 0 c
  else
    let (prev_i, prev_j) = prev_step deg i j in
    let res = mul_intermediate a b prev_i prev_j in
    upd res ((i + j) % deg) (add_zq c (index res ((i + j) % deg)))

val mul: 
    #deg:size_nat
  -> a:lpoly deg
  -> b:lpoly deg
  -> lpoly deg
let mul #deg a b = 
  if deg = 0 then 
    create 0 0
  else
    mul_intermediate a b (deg - 1) (deg - 1)


let test1 = 
  let a: lpoly 1 = 
  let m = mul_zq 1 2 in
  let res = create 1 0 in 
  upd res 0 m in
  assert (index a 0 = 2);
  assert (length a = 1);
  assert (Seq.equal a (Seq.cons 2 Seq.empty))

let test2 = 
  let a: lpoly 1 = Seq.cons 1 Seq.empty in
  let b: lpoly 1 = Seq.cons 3 Seq.empty in
  let p: lpoly 1 = mul a b in
  let p_i: lpoly 1 = mul_intermediate a b 0 0 in
  let c: zq = mul_zq (index a 0) (index b 0) in
  assert (c = 3);
  let s: zq = Seq.index p_i 0 in
  assert (c = s);
  // assert (Seq.index p_i 0 = c);
  assert (Seq.equal p_i (Seq.cons 3 Seq.empty))

