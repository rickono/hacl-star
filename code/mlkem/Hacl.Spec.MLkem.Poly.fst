module Hacl.Spec.MLkem.Poly
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence

let q: int = 3329
let zq = x:int{ x < q && x >= 0 }

let lpoly deg = lseq zq deg

val add_zq: a:zq -> b:zq -> zq
let add_zq a b = (a + b) % q

val add:
    #deg:size_nat
  -> a:lpoly deg
  -> b:lpoly deg
  -> lpoly deg
let add #deg a b =
  createi deg (fun i -> add_zq (index a i) (index b i))
