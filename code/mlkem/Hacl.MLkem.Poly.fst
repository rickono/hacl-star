module Hacl.MLkem.Poly

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open FStar.Seq

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = Hacl.Spec.MLkem.Poly
module Seq = Lib.Sequence
module M = LowStar.Modifies
module U32 = FStar.UInt32

open FStar.Ghost
open Lib.Buffer
open Lib.IntTypes
// open Lib.Loops

let q: uint32 = u32 S.q
let zq = x:uint32{v x < v q}

let zq_v (x:zq): S.zq = v x

let lpoly deg = lbuffer zq deg

val lpoly_v: #deg:size_t -> h:HS.mem -> p:lpoly deg -> GTot (S.lpoly (v deg))
let lpoly_v #deg h p =
  let s:lseq zq (v deg) = as_seq h p in
  Seq.map zq_v s

val add_zq (a:zq) (b:zq): Pure (zq)
  (requires True)
  (ensures fun r -> zq_v r == S.add_zq (zq_v a) (zq_v b))
let add_zq a b =
  // assert (v a + v b == v (a +. b)) ;
  let sum = a +. b in
  let overflow_mask = lte_mask q sum in
  // assert (v overflow_mask == 0 \/ v overflow_mask == v 0xFFFFFFFFul) ;
  let sub_value = logand overflow_mask q in
  logand_lemma overflow_mask q ;
  // assert (v sub_value == 0 \/ v sub_value == v q ) ;
  sum -. sub_value

let empty #a: lseq a 0 = FStar.Seq.empty

let cons #a #len (elem:a) (s:lseq a len): lseq a (len + 1) = FStar.Seq.cons elem s

val slice_plus_one (#a:Type) (#len1 #len2:size_nat) (s1: lseq a len1) (s2: lseq a len2) (i: size_nat):
  Lemma (requires (
    i < len1 /\
    i < len2 /\
    Seq.equal (Seq.slice #_ #len1 s1 0 i) (Seq.slice #_ #len2 s2 0 i) /\
    Seq.index #_ #len1 s1 i == Seq.index #_ #len2 s2 i))
  (ensures Seq.equal (Seq.slice #_ #len1 s1 0 (i + 1)) (Seq.slice #_ #len2 s2 0 (i + 1)))
let slice_plus_one #a #len1 #len2 s1 s2 i =
  let x = Seq.index #_ #len1 s1 i in
  let s1' = Seq.concat #_ #i #1 (Seq.slice #_ #len1 s1 0 i) (cons x empty) in
  let s2' = Seq.concat #_ #i #1 (Seq.slice #_ #len2 s2 0 i) (cons x empty) in
  assert (Seq.equal s1' (Seq.slice #_ #len1 s1 0 (i + 1)));
  assert (Seq.equal s2' (Seq.slice #_ #len2 s2 0 (i + 1)))

val add:
    #deg: size_t
  -> a:lpoly deg
  -> b:lpoly deg
  -> res:lpoly deg
  -> Stack unit
  (requires fun h ->
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ disjoint a res /\ disjoint b res
  )
  (ensures fun h0 _ h1 ->
    live h1 a /\ 
    live h1 b /\ 
    live h1 res /\
    disjoint a b /\
    disjoint a res /\
    disjoint b res /\
    modifies (loc res) h0 h1 /\
    Seq.equal (lpoly_v h1 res) (S.add (lpoly_v h0 a) (lpoly_v h0 b))
   )

let add #deg a b res =
  push_frame ();
  let h0 = ST.get () in
  let spec_sum: erased _ = S.add (lpoly_v h0 a) (lpoly_v h0 b) in
  let inv h (i:nat) =
    live h a /\ live h b /\ live h res /\ modifies (loc res) h0 h /\
    i <= v deg /\
    Seq.equal (Seq.slice (lpoly_v h res) 0 i) (Seq.slice spec_sum 0 i) in
  let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v deg }):
    Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 () h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
    =
      let h0 = ST.get () in
      assert (Seq.equal (Seq.slice (lpoly_v h0 res) 0 (v i)) (Seq.slice spec_sum 0 (v i)));
      let ai = a.(i) in
      let bi = b.(i) in
      let sum = add_zq ai bi in
      res.(i) <- sum;
      let h1 = ST.get () in
      assert (Seq.equal (Seq.slice (lpoly_v h1 res) 0 (v i)) (Seq.slice spec_sum 0 (v i)));
      assert (Seq.index (lpoly_v h1 res) (v i) == Seq.index spec_sum (v i));
      slice_plus_one #_ #(v deg) #(v deg) (lpoly_v h1 res) spec_sum (v i)
    in
  Lib.Loops.for 0ul deg inv body;
  pop_frame ()
