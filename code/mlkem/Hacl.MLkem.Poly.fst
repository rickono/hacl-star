module Hacl.MLkem.Poly

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open FStar.Seq

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = Hacl.Spec.MLkem.Poly
module M = LowStar.Modifies

open Lib.Buffer
open Lib.IntTypes
open Lib.Loops

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let q: uint32 = u32 S.q
let zq = x:uint32{ v x < v q /\ v x >= 0 }

let lpoly deg = lbuffer zq deg

// Functions to convert from impl to spec for proofs
let zq_to_s_zq (x:zq): S.zq =
  v x
let seq_int32_to_int (s:seq zq): (seq S.zq) =
  init (Seq.length s) (fun i -> (zq_to_s_zq (Seq.index s i)))
let poly_impl_to_spec #deg (p:lpoly deg) (h: HS.mem): GTot (S.lpoly (v deg)) =
  seq_int32_to_int (as_seq h p)

val poly_index:
    #deg:size_t
  -> p: lpoly deg
  -> i:size_t
  -> Stack (zq)
    (requires fun h0 -> live h0 p)
    (ensures fun h0 r h1 -> 
      let res_zq = v r in 
      let spec_zq = (S.poly_index (poly_impl_to_spec p h1) (v i)) in 
      res_zq == spec_zq
    )
let poly_index #deg p i =
  assert (v 0ul >= 0);
  if 0ul <=. i && i <. deg then 
  index p i
  else u32 0

val add_zq (a:zq) (b:zq): Pure (zq)
  (requires True)
  (ensures fun r -> v r == (v a + v b) % (v q))
let add_zq a b =
  // assert (v a + v b == v (a +. b)) ;
  let sum = a +. b in
  let overflow_mask = lte_mask q sum in
  // assert (v overflow_mask == 0 \/ v overflow_mask == v 0xFFFFFFFFul) ;
  let sub_value = logand overflow_mask q in
  logand_lemma overflow_mask q ;
  // assert (v sub_value == 0 \/ v sub_value == v q ) ;
  sum -. sub_value


val add:
  aDeg: size_t
  -> a:lpoly aDeg
  -> bDeg: size_t{v bDeg <= v aDeg}
  -> b:lpoly bDeg
  -> res:lpoly aDeg
  -> Stack unit
  (requires fun h ->
    live h a /\ 
    live h b /\ 
    disjoint a b
  )
  (ensures  fun h0 _ h1 ->
    let spec_a = poly_impl_to_spec a h0 in
    let spec_b = poly_impl_to_spec b h0 in
    let spec_res = poly_impl_to_spec res h1 in 
    modifies (loc res) h0 h1 /\
    (spec_res == S.add spec_a spec_b)
  )


let add aDeg a bDeg b res =
  let h0 = ST.get () in
  let inv h (i: nat) =
    live h a /\ live h b /\ live h res /\
    i <= v aDeg /\
    (modifies (loc res) h0 h) /\
    S.get_lowest_n (poly_impl_to_spec res h) i == S.add (S.get_lowest_n (poly_impl_to_spec a h) i) (S.get_lowest_n (poly_impl_to_spec b h) i)
  in
  let body (i:pub_uint32 { 0 <= v i /\ v i < v aDeg }): Stack unit
    (requires (fun h -> inv h (v i)))
    (ensures (fun h0 _ h1 -> inv h0 (v i) /\ inv h1 (v i + 1)))
  =
    let open B in
    res.(i) <- add_zq (poly_index a i) (poly_index b i)
  in
  Lib.Loops.for 0ul aDeg inv body