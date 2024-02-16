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
// open Lib.Loops

val main: unit -> Stack UInt32.t (requires fun _ -> True) (ensures fun _ _ _ -> True)
let main () = 0ul

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
  aDeg: size_t{v aDeg > 0}
  -> a:lpoly aDeg
  // -> bDeg: size_t{v bDeg = v aDeg}
  -> b:lpoly aDeg
  -> res:lpoly aDeg
  -> Stack unit
  (requires fun h ->
    live h a /\ 
    live h b /\ 
    live h res /\
    disjoint a b /\
    disjoint a res /\
    disjoint b res
  )
  (ensures  fun h0 _ h1 ->
    let spec_a = poly_impl_to_spec a h0 in
    let spec_b = poly_impl_to_spec b h0 in
    let spec_res = poly_impl_to_spec res h1 in 
    modifies (loc res) h0 h1 /\
    (Seq.equal spec_res (S.add spec_a spec_b))
  )

// let seq_slice_equal (s1 s2: seq zq): Lemma 
//   // (requires (Seq.equal (Seq.slice s1 (length s1)) (Seq.slice s2 (length s2))) /\ (Seq.length s1 == Seq.length s2) /\ (Seq.)) 
//   (ensures Seq.equal s1 s2)

let add aDeg a b res =
  // push_frame ();
  // let res0 = create aDeg (u32 0) in
  let h0 = ST.get () in
  let inv h (i: nat{ i <= v aDeg}) =
    let res_lowest = S.get_lowest_n (poly_impl_to_spec res h) i in
    let first_i_a = S.get_lowest_n (poly_impl_to_spec a h) i in
    let first_i_b = S.get_lowest_n (poly_impl_to_spec b h) i in
    let add_a_b_lowest = S.add #i #i first_i_a first_i_b in

    // assert (Seq.length first_i_a == i);
    // assert (Seq.length first_i_b == i);
    // assert (Seq.length first_i_a == Seq.length first_i_b);

    // assert (Seq.length res_lowest == Seq.length add_a_b_lowest);
    // assert (Seq.length res_lowest == i);
    // assert (S.poly_index res_lowest i == S.poly_index first_i_a i + S.poly_index first_i_b i);

    // assume (S.poly_index res_lowest i == (S.poly_index first_i_a i) + (S.poly_index first_i_b i) % S.q);

    // assume (Seq.equal (Seq.slice res_lowest 0 i) (Seq.slice add_a_b_lowest 0 i));
    // assume (i = 0 \/ Seq.index res_lowest (i-1) == Seq.index add_a_b_lowest (i-1));
    // assert (Seq.length res_lowest == i /\ Seq.length add_a_b_lowest == i);
    // assume (i = 0 \/ Seq.equal (Seq.slice res_lowest 0 (i-1)) (Seq.slice add_a_b_lowest 0 (i-1)));
    // assume (i = v aDeg \/ (Seq.index res_lowest i) = (Seq.index add_a_b_lowest i));
    // assume (i = 0 \/ Seq.index res_lowest (i-1) == Seq.index add_a_b_lowest (i-1));
    
    assume (Seq.equal res_lowest add_a_b_lowest);
    live h a /\ live h b /\ live h res /\
    disjoint a b /\ disjoint a res /\ disjoint b res /\
    i <= v aDeg /\
    (modifies (loc res) h0 h) /\
    Seq.equal res_lowest add_a_b_lowest
    
    // res_lowest == add_a_b_lowest
  in
  // let body (i:size_t { 0 <= v i /\ v i < v aDeg })
  // : Stack unit
  //   (requires (fun h -> inv h (v i)))
  //   (ensures (fun h0 _ h1 -> inv h0 (v i) ))
  // =
  //   res.(i) <- add_zq (poly_index a i) (poly_index b i)
  // in
  Lib.Loops.for 0ul aDeg inv 
  (fun i ->
    // res.(i) <- add_zq (poly_index a i) (poly_index b i)
    res.(i) <- u32 3328
  )