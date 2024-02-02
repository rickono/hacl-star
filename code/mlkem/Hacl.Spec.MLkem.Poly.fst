module Hacl.Spec.MLkem.Poly
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes

let q: int = 3329
let zq = x:int{ x < q && x >= 0 }

let lpoly deg = (lseq zq deg)
let zero = create 0 0
let one = create 1 1

// let valid (s:lseq zq deg) : bool =
//   length s = 0 || (index s (length s - 1) <> 0)



val poly_index:
    #deg:nat
  -> p: lpoly deg
  -> i:nat
  -> zq
  
let poly_index p i =
  if 0 <= i && i < length p then 
  index p i
  else 0

let to_seq #deg (p:lpoly deg) : Pure (seq zq)
  (requires True)
  (ensures fun s ->
    length s == deg /\
    (forall (i:nat).{:pattern (poly_index p i) \/ (index s i)} i < length s ==> poly_index p i == index s i)
  )
  =
  init deg (poly_index p)

// let rec of_seq (s:lseq zq deg) : Pure poly_mod
//   (requires True)
//   (ensures fun p ->
//     length p <= length s /\
//     (forall (i:nat).{:pattern (p.[i]) \/ (index s i)} i < length s ==> p.[i] == index s i)
//   )
//   (decreases (length s))
//   =
//   if length s < deg 
//   then init deg (fun i -> if i < length s then s.[i] else 0)
//   else
//     of_seq (slice s 0 (length s - 1))

// let rec of_seq (s:seq zq) : Pure poly_mod
//   (requires True)
//   (ensures fun p ->
//     length p <= length s /\
//     (forall (i:nat).{:pattern (p.[i]) \/ (index s i)} i < length s ==> p.[i] == index s i)
//   )
//   (decreases (length s))
//   =
//   if valid s then s
//   else
//     of_seq (slice s 0 (length s - 1))

[@"opaque_to_smt"]
// let of_fun (len:nat) (f:nat -> zq) : Pure poly_mod
let of_fun (#deg:nat) (f:nat -> zq) : Pure (lpoly deg)
  (requires True)
  (ensures fun p ->
    // length p <= len /\
    (forall (i:nat).{:pattern poly_index p i \/ (f i)} i < deg ==> poly_index p i == f i) /\
    (forall (i:nat).{:pattern poly_index p i} (poly_index p i <> 0) ==> 0 <= i /\ i < deg)
  )
  =
  init deg f
  // of_seq (init len f)

val get_lowest_n: #deg:nat -> p:lpoly deg -> n:nat -> Pure (lseq zq n)
  (requires True)
  (ensures fun s ->
    length s == n /\
    (forall (i:nat).{:pattern (poly_index p i) \/ (index s i)} i < n ==> poly_index p i == index s i)
  )
let get_lowest_n #deg p n =
  if n <= deg then
    (slice p 0 n)
  else append p (create (n - deg) 0)

val add_zq: a:zq -> b:zq -> Pure zq
  (requires True)
  (ensures fun r -> r == (a + b) % q)
let add_zq a b = (a + b) % q

val add: #aDeg:size_nat 
  -> #bDeg:size_nat{bDeg <= aDeg} 
  -> a:lpoly aDeg
  -> b:lpoly bDeg
  -> Pure (lpoly aDeg) 
  (requires True)
  (ensures fun p ->
    let len = max (length a) (length b) in
    length p <= len /\
    (forall (i:nat).{:pattern poly_index p i} poly_index p i == (poly_index a i + poly_index b i) % q)
  )
let add #aDeg #bDeg a b = 
  let len = max (length a) (length b) in
  of_fun (fun (i:nat) -> (poly_index a i + poly_index b i) % q)

// // f j + f (j + 1) + ... + f (k - 1)
// let rec sum_element (j k: int) (f: int -> int) : Tot int (decreases (k -j)) = 
//   if j >= k then 0
//   else (sum_element j (k-1) f) + f (k - 1)

// // a0 * bk + a1 * b(k-1) + ... + ak * b0
// let mul_element (a b:poly_mod) (k:int) : zq = 
//   (sum_element 0 (k+1) (fun i -> (a.[i] * b.[k - i]))) % q

// let mul (a b:poly_mod) : Pure poly_mod
//   (requires True)
//   (ensures fun p ->
//     let len = length a + length b in
//     length p <= len /\
//     (forall (i:nat).{:pattern p.[i]} i < len ==> p.[i] == mul_element a b i)
//   ) =
//   let len = length a + length b in
//   of_fun len (fun (i:nat) -> mul_element a b i)