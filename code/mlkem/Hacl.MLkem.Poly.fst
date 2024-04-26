module Hacl.MLkem.Poly

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open FStar.Seq
open FStar.Int
open Lib.NatMod

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = Hacl.Spec.MLkem.Poly
module Seq = Lib.Sequence
module M = LowStar.Modifies
module U32 = FStar.UInt32
module LE = Lib.Exponentiation
module PT = Hacl.Impl.PrecompTable

open FStar.Ghost
open Lib.Buffer
open Lib.IntTypes
// open Lib.Loops

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let n: size_t = size S.n
let q32: uint32 = u32 S.q
let q64: uint64 = u64 S.q
let m: uint64 = u64 S.m
let zq = x:uint32{v x < S.q}

let zq_v (x:zq): S.zq = v x

let lpoly deg = lbuffer zq deg
let rq = lpoly n

val lpoly_v: #deg:size_t -> h:HS.mem -> p:lpoly deg -> GTot (S.lpoly (v deg))
let lpoly_v #deg h p =
  let s:lseq zq (v deg) = as_seq h p in
  Seq.map zq_v s
val rq_v: h:HS.mem -> p:rq -> GTot (S.lpoly (v n))
let rq_v h p = lpoly_v #n h p

// Converts the lbuffer to a list of lpoly 2 to match spec rep
let tq = lbuffer zq n
val tq_v: h:HS.mem -> p:tq -> GTot (S.tq)
let tq_v h f =
  let s = as_seq h f in
  let l = Seq.map zq_v s in
  S.rq_to_tq l


val add_zq (a:zq) (b:zq): Pure (zq)
  (requires True)
  (ensures fun r -> zq_v r == S.add_zq (zq_v a) (zq_v b))
let add_zq a b =
  // assert (v a + v b == v (a +. b)) ;
  let sum = a +. b in
  let overflow_mask = lte_mask q32 sum in
  // assert (v overflow_mask == 0 \/ v overflow_mask == v 0xFFFFFFFFul) ;
  let sub_value = logand overflow_mask q32 in
  logand_lemma overflow_mask q32 ;
  // assert (v sub_value == 0 \/ v sub_value == v q ) ;
  sum -. sub_value

val neg_zq (a:zq): Pure (zq)
  (requires True)
  (ensures fun r -> zq_v r == S.neg_zq (zq_v a))
let neg_zq a =
  let neg = q32 -. a in
  let overflow_mask = lte_mask q32 neg in
  logand_lemma overflow_mask q32 ;
  let sub_value = logand overflow_mask q32 in
  neg -. sub_value

val sub_zq (a:zq) (b:zq): Pure (zq)
  (requires True)
  (ensures fun r -> zq_v r == S.sub_zq (zq_v a) (zq_v b))
let sub_zq a b =
  let diff = q32 +. a -. b in
  let overflow_mask = lte_mask q32 diff in
  // assert (v overflow_mask == 0 \/ v overflow_mask == v 0xFFFFFFFFul) ;
  let sub_value = logand overflow_mask q32 in
  logand_lemma overflow_mask q32 ;
  // assert (v sub_value == 0 \/ v sub_value == v q ) ;
  diff -. sub_value

// Making this additional function to add mod n was much easier than making a more generic a+b mod m function
val add_mod_n (a:uint32{v a < S.n}) (b:uint32{v b < S.n}): Pure uint32
  (requires True)
  (ensures fun r -> v r == (v a + v b) % S.n)
let add_mod_n a b =
  let sum = a +. b in
  let sec_n = u32 S.n in
  let overflow_mask = lte_mask sec_n sum in
  logand_lemma overflow_mask sec_n ;
  let sub_value = logand overflow_mask sec_n in
  sum -. sub_value

#reset-options "--z3rlimit 100 --fuel 0 --ifuel 0 --split_queries always"
val mul_zq_lemma (a:zq) (b:zq): 
  Lemma (requires True) (ensures (v (a *. b) == (v a * v b)))
let mul_zq_lemma a b =
  assert (v a < 3329);
  assert (v b < 3329);
  assert (v a * v b < 3329 * 3329);
  ()

val error_increases_lemma (prodA:uint64{v prodA <= 3328 * 3328}) (prodB:uint64{v prodB <= 3328 * 3328}): 
  Lemma 
    (requires v prodA <= v prodB)
    (ensures (
      let quotA = (prodA *. m) >>. (32ul) in
      let quotB = (prodB *. m) >>. (32ul) in
      v quotA <= v quotB
    ))
let error_increases_lemma prodA prodB =
  let quotA = (prodA *. m) >>. (32ul) in
  let quotB = (prodB *. m) >>. (32ul) in
  assert (v quotA <= v quotB);
  ()
  
val quot_max_error_lemma (prod:uint64{v prod <= 3328 * 3328}): 
  Lemma 
    (requires True)
    (ensures (
      let quot = (prod *. m) >>. (32ul) in
      v quot = (v prod / v q64) \/ v quot = ((v prod / v q64) - 1))
    )
let quot_max_error_lemma prod = 
  assert (v prod < 3329 * 3329);
  let maxProd = (q64 -. (u64 1)) *. (q64 -. (u64 1)) in
  assert (v prod <= v maxProd);
  error_increases_lemma prod maxProd;
  ()

val mul_zq (a:zq) (b:zq): Pure (zq)
  (requires True)
  (ensures fun r -> zq_v r == S.mul_zq (zq_v a) (zq_v b))
let mul_zq a b =
  let prod = cast U64 SEC (a *. b) in
  mul_zq_lemma a b ; // convinces fstar that there's no overflow
  let quot = (prod *. m) >>. (32ul) in
  assert (v a <= 3328 /\ v b <= 3328);
  assert (v prod <= 3328 * 3328);
  quot_max_error_lemma prod ;
  assert (v quot = (v prod / v q64) \/ v quot = ((v prod / v q64) - 1)) ;
  let rem = prod -. (quot *. q64) in
  assert(v rem < 2 * v q64) ;
  let overflow_mask = lte_mask q64 rem in
  assert (v rem < v q64 \/ v overflow_mask = ones_v U64) ;
  let sub_value = logand overflow_mask q64 in
  // gt_mask_lemma rem q64 ;
  logand_lemma overflow_mask q64 ;
  let result = rem -. sub_value in
  // assert (v result < v q64) ;
  cast U32 SEC result

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let empty #a: lseq a 0 = FStar.Seq.empty

let cons #a #len (elem:a) (s:lseq a len): lseq a (len + 1) = FStar.Seq.cons elem s

val slice_plus_one (#a:Type) (#len1 #len2:size_nat) (s1: lseq a len1) (s2: lseq a len2) (i j: size_nat):
  Lemma (requires (
    i < len1 /\
    i < len2 /\
    j < len1 /\
    j < len2 /\
    i <= j /\
    Seq.equal (Seq.slice #_ #len1 s1 i j) (Seq.slice #_ #len2 s2 i j) /\
    Seq.index #_ #len1 s1 j == Seq.index #_ #len2 s2 j))
  (ensures Seq.equal (Seq.slice #_ #len1 s1 i (j + 1)) (Seq.slice #_ #len2 s2 i (j + 1)))
let slice_plus_one #a #len1 #len2 s1 s2 i j =
  let x = Seq.index #_ #len1 s1 j in
  let s1' = Seq.concat #_ #(j - i) #1 (Seq.slice #_ #len1 s1 i j) (cons x empty) in
  let s2' = Seq.concat #_ #(j - i) #1 (Seq.slice #_ #len2 s2 i j) (cons x empty) in
  assert (Seq.equal s1' (Seq.slice #_ #len1 s1 i (j + 1)));
  assert (Seq.equal s2' (Seq.slice #_ #len2 s2 i (j + 1)))

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
      slice_plus_one #_ #(v deg) #(v deg) (lpoly_v h1 res) spec_sum 0 (v i)
    in
  Lib.Loops.for 0ul deg inv body;
  pop_frame ()

val add_rq: 
    a: rq 
  -> b: rq 
  -> res: rq 
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
    Seq.equal (lpoly_v h1 res) (S.add_rq (lpoly_v h0 a) (lpoly_v h0 b))
   )
let add_rq a b res = add #n a b res

val scalar_mul:
    #deg: size_t
  -> a:lpoly deg
  -> b:zq
  -> res:lpoly deg
  -> Stack unit
  (requires fun h ->
    live h a /\ live h res /\
    disjoint a res
  )
  (ensures fun h0 _ h1 ->
    live h1 a /\
    live h1 res /\
    disjoint a res /\
    modifies (loc res) h0 h1 /\
    Seq.equal (lpoly_v h1 res) (S.scalar_mul (lpoly_v h0 a) (zq_v b))
   )

let scalar_mul #deg a b res =
  push_frame ();
  let h0 = ST.get () in
  let spec_prod: erased _ = S.scalar_mul (lpoly_v h0 a) (zq_v b) in
  let inv h (i:nat) =
    live h a /\ live h res /\ modifies (loc res) h0 h /\
    i <= v deg /\
    Seq.equal (Seq.slice (lpoly_v h res) 0 i) (Seq.slice spec_prod 0 i) in
  let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v deg }):
    Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 () h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
    =
      let h0 = ST.get () in
      assert (Seq.equal (Seq.slice (lpoly_v h0 res) 0 (v i)) (Seq.slice spec_prod 0 (v i)));
      let ai = a.(i) in
      let prod = mul_zq ai b in
      res.(i) <- prod;
      let h1 = ST.get () in
      assert (Seq.equal (Seq.slice (lpoly_v h1 res) 0 (v i)) (Seq.slice spec_prod 0 (v i)));
      slice_plus_one #_ #(v deg) #(v deg) (lpoly_v h1 res) spec_prod 0 (v i)
    in
  Lib.Loops.for 0ul deg inv body;
  pop_frame ()

// let zeta = u32 S.zeta

// val and_lte_lemma (a b:uint32): Lemma (requires True) (ensures (v (a &. b) <= v a) && (v (a &. b) <= v b))
// let and_lte_lemma a b =
//   logand_pos_le #128 (v a) (v b);
//   logand_spec a b;
//   ()

// val bitrev7_:
//     num:U32.t{v num < 128} 
//   -> (i:size_t{v i <= 6}) 
//   -> (res:U32.t{v res < 128})
//   -> Stack U32.t 
//     (requires fun _ -> Seq.slice (S.bitsequence (v res)) 0 (v i) = Seq.slice (S.bitrev7 (S.bitsequence (v num))) 0 (v i))
//     (ensures fun _ r _ -> v r < 128 && Seq.slice (S.bitsequence (v r)) 0 ((v i) + 1) = Seq.slice (S.bitrev7 (S.bitsequence (v num))) 0 ((v i) + 1))
// let rec bitrev7_ num i res =
//   let mask_low_bit = num &. (1ul) in
//   let rev_bit = mask_low_bit <<. (6ul -. i) in
//   let res_upd = res &. rev_bit in
//   logand_spec res rev_bit;
//   assert (v (res &. rev_bit) = logand_v (v res) (v rev_bit));
//   logand_pos_le #128 (v res) (v rev_bit);
//   if i >=. 6ul then
//     res_upd
//   else
//     bitrev7_ (num >>. 1ul) (i +. 1ul) res_upd


// val bitrev7 (num: uint32{v num < 128}): Stack U32.t
//   (requires fun _ -> True)
//   (ensures fun _ r _ -> v r < 128 && S.bitsequence (v r) = S.bitrev7 (S.bitsequence (v num)))
// let bitrev7 num =
//   admit()
//   // let rev_spec = S.bit7_v (S.bitrev7 (S.bitsequence (v num))) in
//   // let res = bitrev7_ num 0ul (u32 0) in
//   // res

// val z_exp (k:uint32{v k < 128}): uint32
// let z_exp k = 
//   admit()
//   // let rec loop (i:uint32) (acc:uint32): uint32 =
//   //   if i = k then
//   //     acc
//   //   else
//   //     let acc' = mul_zq acc zeta in
//   //     loop (i +. 1ul) acc'
//   // in
//   // loop 0ul zeta

// let precomp_zeta_table_list: x:list zq{FStar.List.Tot.length x = 128} 
//   = normalize_term (SPT.precomp_base_table_list )
// val precomp_zeta_table: x:glbuffer zq 128ul{witnessed x precomp_zeta_table_lseq /\ recallable x}
// let precomp_zeta_table = createL_global (Seq.to_list precomp_zeta_table_lseq)

// val precomp_zeta_lseq : erased (Seq.lseq zq 128)
// let precomp_zeta_lseq =
//   Seq.createi 128 (fun i -> 
//     let z = S.zeta_to_k i in 
//     let z':zq = u32 z in
//     z')

// val seq_eq_idx_lemma: #len:size_nat -> s1:lseq zq len -> s2:lseq zq len -> i:nat{i < len} -> Lemma (requires Seq.equal #_ #len s1 s2) (ensures Seq.index #_ #len s1 i == Seq.index #_ #len s2 i)
// let seq_eq_idx_lemma s1 s2 i = ()

// let is_zeta_table (table:lbuffer zq 128ul) h = Seq.equal (as_seq h table) precomp_zeta_lseq

// val index_zeta_table:
//     i:size_t{i <. 128ul}
//   -> table:lbuffer zq 128ul
//   -> Stack zq 
//     (requires fun h -> live h table /\ is_zeta_table table h)
//     (ensures fun h0 r h1 -> live h1 table /\ zq_v r = S.zeta_to_k (v i))
// let index_zeta_table i table =
//   table.(i)

// val precomp_zeta: table:lbuffer zq 128ul -> Stack unit 
//   (requires fun h -> live h table)
//   (ensures fun h0 _ h1 -> live h1 table /\ is_zeta_table table h1)
// let precomp_zeta table = 
//   push_frame ();
//   let h0 = ST.get () in
//   let inv h (i:nat) = 
//     live h table /\
//     modifies (loc table) h0 h /\
//     i <= 128 /\ 
//     Seq.equal (Seq.slice precomp_zeta_lseq 0 i) (Seq.slice (as_seq h table) 0 i) in
//   table.(0ul) <- u32 1;
//   pow_mod_def #S.q S.zeta 0;
//   lemma_pow_mod #S.q S.zeta 0;
//   lemma_pow0 S.zeta;
//   assert (S.zeta_to_k 0 == 1);
//   let h' = ST.get () in
//   assert (v (Seq.index (as_seq h' table) 0) == (S.zeta_to_k 0));
//   let body (i: U32.t{1 <= U32.v i && U32.v i < 128}): 
//     Stack unit 
//     (requires fun h -> inv h (U32.v i))
//     (ensures fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)) 
//   =
//     let h0 = ST.get () in
//     let table_as_seq: erased (Seq.lseq zq 128) = as_seq h0 table in
//     assert (Seq.equal (Seq.slice table_as_seq 0 (v i)) (Seq.slice precomp_zeta_lseq 0 (v i)));
//     seq_eq_idx_lemma #(v i) (Seq.slice table_as_seq 0 (v i)) (Seq.slice precomp_zeta_lseq 0 (v i)) (v i - 1);
//     assert ((Seq.index table_as_seq (v i - 1)) == (Seq.index precomp_zeta_lseq (v i - 1)));
//     assert (v (Seq.index precomp_zeta_lseq (v i - 1)) == S.zeta_to_k (v i - 1));
//     assert (v table.(i -. 1ul) == S.zeta_to_k (v i - 1));
//     S.zeta_to_k_pos_lemma (v i);
//     table.(i) <- mul_zq table.(i -. 1ul) zeta;
//     let h1 = ST.get () in
//     assert (v table.(i) == S.zeta_to_k (v i));
//     assert (Seq.index (as_seq h1 table) (v i) == Seq. index precomp_zeta_lseq (v i));
//     assert (Seq.equal (Seq.slice (as_seq h1 table) 0 (v i)) (Seq.slice precomp_zeta_lseq 0 (v i)));
//     slice_plus_one #_ #128 #128 (as_seq h1 table) precomp_zeta_lseq 0 (v i)
//   in
//   Lib.Loops.for 1ul 128ul inv body;
//   pop_frame ()

// type len_t = l:size_t{v l = 2 || v l = 4 || v l = 8 || v l = 16 || v l = 32 || v l = 64 || v l = 128}
// type start_t (len:len_t) = s:size_t{v s < 256 && (v s) % (2 * (v len)) = 0}
// val start_plus_len: #len:len_t -> s:start_t len -> Lemma (ensures v s + v len < 256)
// let start_plus_len #len s = ()

// val start_t_lemma: 
//     #i:size_t{v i < 7}
//   -> i':size_t{i' <. (1ul <<. i)}
//   -> Lemma (ensures 2 * (v (128ul >>. i)) * (v i' + 1) <= 256)
// let start_t_lemma #i i' =
//   let len = 128ul >>. i in
//   assert (v i' < pow2 (v i));
//   assume (pow2 7 = 128);
//   assert (v len = pow2 7 / pow2 (v i));
//   ()

// val ntt_inner_inner_f_ok_1:
//     j:nat
//   -> len:len_t
//   -> start:start_t len
//   -> z:zq
//   -> res_j:zq
//   -> res_j_plus_len:zq
//   -> f:S.tq
//   -> t:zq
//   -> Lemma 
//       (requires 
//         j < v start + v len /\
//         j >= v start /\
//         v res_j = S.index_tq f j /\ 
//         j + v len < 256 /\
//         v res_j_plus_len = S.index_tq f (j + v len) /\ 
//         v t = S.mul_zq (v z) (v res_j_plus_len)
//       )
//       (ensures v (add_zq res_j t) = S.ntt_inner_inner_f j (v len) (v start) (v z) f)
// let ntt_inner_inner_f_ok_1 j len start z res_j res_j_plus_len f t = ()

// val ntt_inner_inner_f_ok_2:
//     j:nat
//   -> len:len_t
//   -> start:start_t len
//   -> z:zq
//   -> res_j:zq
//   -> res_j_minus_len:zq
//   -> f:S.tq
//   -> t:zq
//   -> Lemma 
//       (requires 
//         j < v start + 2 * (v len) /\
//         j >= v start + v len /\
//         j < 256 /\
//         v res_j = S.index_tq f j /\ 
//         v res_j_minus_len = S.index_tq f (j - v len) /\ 
//         v t = S.mul_zq (v z) (v res_j)
//       )
//       (ensures v (add_zq res_j_minus_len (neg_zq t)) = S.ntt_inner_inner_f j (v len) (v start) (v z) f)
// let ntt_inner_inner_f_ok_2 j len start z res_j res_j_plus_len f t = ()

// val seq_slice_idx_lemma:
//     #a:eqtype
//   -> start:nat
//   -> fin:nat{start <= fin /\ fin <= 256}
//   -> i:nat{start <= i /\ i < fin}
//   -> s1:lseq a 256
//   -> s2:lseq a 256
//   -> Lemma 
//       (requires Seq.equal (Seq.slice #_ #256 s1 start fin) (Seq.slice #_ #256 s2 start fin))
//       (ensures Seq.index #a #256 s1 i = Seq.index #a #256 s2 i)
// let seq_slice_idx_lemma #a start fin i s1 s2 =
//   let slice_i = i - start in
//   let slice1 = Seq.slice #_ #256 s1 start fin in
//   let slice2 = Seq.slice #_ #256 s2 start fin in
//   assert (Seq.index slice1 slice_i = Seq.index slice2 slice_i)

// #reset-options "--z3rlimit 20 --fuel 0 --ifuel 0"
// // This should be equivalent to running the S.ntt_inner_inner
// val ntt_inner_inner:
//     res:rq
//   -> len:len_t
//   -> start:start_t len{v start + (2 * v len) <= 256}
//   -> z:zq
//   -> Stack unit
//   (requires fun h ->
//     live h res)
//   (ensures fun h0 _ h1 -> 
//     live h1 res /\
//     modifies (loc res) h0 h1 /\
//     Seq.equal
//       (Seq.slice (lpoly_v h1 res) (v start) (v start + v len + v len))
//       (Seq.slice (S.tq_to_rq (S.ntt_inner_inner_func (v z) (tq_v h0 res) (v len) (v start))) (v start) (v start + v len + v len)))
// let ntt_inner_inner res len start z =
//   push_frame ();
//   let h0 = ST.get () in
//   let spec_res: erased (lseq S.zq S.n) = (S.tq_to_rq (S.ntt_inner_inner_func (v z) (tq_v h0 res)  (v len) (v start))) in
//   let spec_tq: erased (S.tq) = (S.ntt_inner_inner_func (v z) (tq_v h0 res)  (v len) (v start)) in
//   let loop_stop = start +. len in
//   assert (v len <= 256);
//   assert (v len + v start + v len <= 256);
//   assert (v start >= 0);
//   let inv h (j:nat) =
//     // start_plus_len #len start;
//     live h res /\
//     modifies (loc res) h0 h /\
//     j <= v start + v len /\
//     j >= v start /\
//     j <= 256 /\
//     j >= 0 /\
//     Seq.equal
//       (Seq.slice (lpoly_v h res) j (v start + v len))
//       (Seq.slice (lpoly_v h0 res) j (v start + v len)) /\
//     Seq.equal
//       (Seq.slice (lpoly_v h res) (j + v len) (v start + 2 * (v len)))
//       (Seq.slice (lpoly_v h0 res) (j + v len) (v start + 2 * (v len))) /\
//     Seq.equal 
//       (Seq.slice (lpoly_v h res) (v start) j) 
//       (Seq.slice #_ #(S.n) spec_res (v start) j) /\
//     Seq.equal 
//       (Seq.slice (lpoly_v h res) (v start + v len) (v len + j))
//       (Seq.slice #_ #(S.n) spec_res (v start + v len) (v len + j)) in
//   let body (j:U32.t{v start <= v j /\ v j < v loop_stop}): 
//     Stack unit 
//     (requires fun h -> inv h (U32.v j))
//     (ensures fun h0 _ h1 -> inv h0 (U32.v j) /\ inv h1 (U32.v j + 1)) 
//   =
//     let h0' = ST.get () in
//     let res_j = res.(j) in
//     let res_j_plus_len = res.(j +. len) in
//     let t = mul_zq z res_j_plus_len in
//     // res[j:start+len] = res0[j:start+len]
//     // assert (Seq.equal (Seq.slice (lpoly_v h0' res) (v j) (v start + v len)) (Seq.slice (lpoly_v h0 res) (v j) (v start + v len)));
//     seq_slice_idx_lemma #_ (v j) (v start + v len) (v j) (lpoly_v h0' res) (lpoly_v h0 res);
//     // res[j] = res0[j]
//     // assert (Seq.index (lpoly_v h0' res) (v j) = Seq.index (lpoly_v h0 res) (v j));
//     seq_slice_idx_lemma #_ (v j + v len) (v start + 2 * (v len)) (v j + v len) (lpoly_v h0' res) (lpoly_v h0 res);
//     // res[j+len] = res0[j+len]
//     // assert (Seq.index (lpoly_v h0' res) (v j + v len) = Seq.index (lpoly_v h0 res) (v j + v len));
//     ntt_inner_inner_f_ok_1 (v j) len start z res_j res_j_plus_len (tq_v h0 res) t;
//     // this gives us res[j] + t (in h0') = S.ntt_inner_inner_f j len start z res (in h0)
//     ntt_inner_inner_f_ok_2 (v j + v len) len start z res_j_plus_len res_j (tq_v h0 res) t;
//     // This gives us res[j] - t (in h0') = S.ntt_inner_inner_f j+len len start z res (in h0)
//     // assert (v (add_zq res_j t) == S.ntt_inner_inner_f (v j) (v len) (v start) (v z) (tq_v h0' res));
//     // assert (v (add_zq res_j (neg_zq t)) == S.ntt_inner_inner_f (v j + v len) (v len) (v start) (v z) (tq_v h0' res));
//     res.(j) <- add_zq res_j t;
//     res.(j +. len) <- add_zq res_j (neg_zq t);
//     assert (v j + v len > v j);
//     assert (v (j +. len) > v j);
//     assert (v (j +. len) > v j + 1);
//     let h1 = ST.get () in
//     // assert (Seq.index (lpoly_v h1 res) (v j) == Seq.index #_ #(S.n) spec_res (v j));
//     // assert (Seq.equal (Seq.slice (lpoly_v h1 res) (v start) (v j)) (Seq.slice #_ #(S.n) spec_res (v start) (v j)));
//     slice_plus_one #_ #256 #256 (lpoly_v h1 res) spec_res (v start) (v j);
//     // assert (Seq.index (lpoly_v h1 res) (v j + v len) == Seq.index #_ #(S.n) spec_res (v j + v len));
//     // assert (Seq.equal (Seq.slice (lpoly_v h1 res) (v start + v len) (v j + v len)) (Seq.slice #_ #(S.n) spec_res (v start + v len) (v j + v len)));
//     slice_plus_one #_ #256 #256 (lpoly_v h1 res) spec_res (v start + v len) (v j + v len);
//     assert (v j + v len >= v start + v len);
//     assert (v j < v j + v len);
//     assume (Seq.equal (Seq.slice (lpoly_v h1 res) (v j + 1) (v start + v len)) (Seq.slice (lpoly_v h0 res) (v j + 1) (v start + v len)));
//     assume (Seq.equal (Seq.slice (lpoly_v h1 res) (v j + 1 + v len) (v start + 2 * (v len))) (Seq.slice (lpoly_v h0 res) (v j + 1 + v len) (v start + 2 * (v len))));
//     assume (v j + 1 < v start + v len);
//     assume (v j + 1 <= 256) in
//   // admit()
//   Lib.Loops.for start loop_stop inv body;
//   pop_frame ()


// let is_len_t (l:size_t) = (v l = 2 || v l = 4 || v l = 8 || v l = 16 || v l = 32 || v l = 64 || v l = 128)

// val k_lt_128:
//     (len:len_t)
//   -> (start:start_t len)
//   -> Lemma (ensures v ((128ul /. len) +. (start /. (2ul *. len))) < 128)
// let k_lt_128 len start = ()

// val start_lte_256:
//     #i:size_t{v i < 7} 
//   -> len:len_t
//   -> s_i:size_t
//   -> Lemma 
//     (requires len = (128ul >>. i) /\ s_i <. (1ul <<. i)) 
//     (ensures v (2ul *. (1ul <<. i) *. (128ul >>. i)) <= 256)
// let start_lte_256 #i len s_i = ()
// val start_divisible_by_len:
//     #i:size_t{v i < 7} 
//   -> len:len_t
//   -> s_i:size_t
//   -> Lemma 
//     (requires len = (128ul >>. i) /\ s_i <. (1ul <<. i) /\ len <> 0ul) 
//     (ensures v (2ul *. s_i *. len) % v (2ul *. len) = 0)
// let start_divisible_by_len #i len s_i = ()

// val ntt_outer_inner:
//     res:rq
//   -> zeta_table:lbuffer zq 128ul
//   -> i:size_t{v i < 7}
//   -> Stack unit
//   (requires fun h ->
//     live h res /\
//     live h zeta_table /\
//     is_zeta_table zeta_table h)
//   (ensures fun h0 _ h1 ->
//     assume (is_len_t (128ul >>. i));
//     let len:len_t = 128ul >>. i in
//     live h1 res /\
//     modifies (loc res) h0 h1 /\
//     S.tq_eq (tq_v h1 res) (S.ntt_outer_inner (tq_v h0 res) (v len) 0))
// let ntt_outer_inner res zeta_table i =
//   // Start goes from 0->2^8
//   // Increments by 2*len each time, say len=2^(7-i)
//   // # of loops is 2^8 / (2*2^(7-i)) = 2^i = 1 <<. i
//   assume(is_len_t (128ul >>. i));
//   let h0 = ST.get () in
//   let len:len_t = 128ul >>. i in
//   let loop_iters = 1ul <<. i in
//   let spec_res: erased _ = S.tq_to_rq (S.ntt_outer_inner (tq_v h0 res) (v len) 0) in
//   let inv h (i:nat) =
//     live h res /\
//     live h zeta_table /\
//     i <= v loop_iters /\
//     is_zeta_table zeta_table h /\
//     Seq.equal
//       (Seq.slice #_ #256 (lpoly_v h res) 0 (i * 2 * (v len)))
//       (Seq.slice #_ #256 spec_res 0 (i * 2 * (v len)))
//     in
//   let body (s_i:size_t{v s_i >= 0 /\ v s_i < v loop_iters}): 
//     Stack unit 
//     (requires fun h -> inv h (v i))
//     (ensures fun h0 _ h1 -> inv h0 (v i) /\ inv h1 (v i + 1)) 
//   =
//     // Max value: 2 * 2^i * 2^(7-i) = 2^8 = 256
//     start_lte_256 #i len s_i;
//     start_divisible_by_len #i len s_i;
//     let start:start_t len = 2ul *. len *. s_i in
//     k_lt_128 len start;
//     let k = (128ul /. len) +. (start /. (2ul *. len)) in
//     let zeta = index_zeta_table k zeta_table in
//     ntt_inner_inner res len start zeta in
//   Lib.Loops.for 0ul loop_iters inv body


// val ntt:
//     f:rq
//   -> res:rq
//   -> zeta_table:lbuffer zq 128ul
//   -> Stack unit
//   (requires fun h ->
//     live h f /\ live h res /\
//     live h zeta_table /\
//     disjoint f res
//   )
//   (ensures fun h0 _ h1 ->
//     live h1 f /\
//     live h1 res /\
//     disjoint f res /\
//     modifies (loc res) h0 h1 /\
//     S.tq_eq (tq_v h1 res) (S.ntt (lpoly_v h0 f))
//    )
// let ntt f res zeta_table =
//   push_frame ();
//   let h0 = ST.get () in
//   precomp_zeta zeta_table;
//   let inv_inner_inner (len:len_t) (start:start_t len) (z:zq) h (j':nat) =
//     let j:nat = v start + j' in
//     let spec_tq = (S.ntt_inner_inner (v z) (tq_v h f) j (v len) (v start)) in
//     // let first_part_spec = Seq.slice (S.tq_to_rq spec_tq) (v start) (j + 1) in
//     // let first_part_impl = Seq.slice (lpoly_v h res) (v start) (j + 1) in
//     // let second_part_spec = Seq.slice (S.tq_to_rq spec_tq) (v start + v len) (v len + j + 1) in
//     // let second_part_impl = Seq.slice (lpoly_v h res) (v start + v len) (v len + j + 1) in
//     j' <= v len /\
//     live h f /\ live h res /\ modifies (loc res) h0 h /\ j' < v len /\
//     Seq.equal 
//       (Seq.slice (lpoly_v h res) (v start) (j + 1)) 
//       (Seq.slice (S.tq_to_rq spec_tq) (v start) (j + 1)) /\
//     Seq.equal 
//       (Seq.slice (lpoly_v h res) (v start + v len) (v len + j + 1)) 
//       (Seq.slice (S.tq_to_rq spec_tq) (v start + v len) (v len + j + 1)) in
//   let body_inner_inner (len:len_t) (start:start_t len) (z:zq) (j':size_t{v j' < v len}): 
//     Stack unit 
//     (requires (fun h -> inv_inner_inner len start z h (v j'))) 
//     (ensures (fun h0 _ h1 -> inv_inner_inner len start z h0 (v j') /\ inv_inner_inner len start z h1 (v j' + 1))) 
//   =
//     let h0 = ST.get () in
//     let j = start +. j' in
//     let t = mul_zq z f.(j +. len) in
//     start_plus_len #len start;
//     assert (v j < 256);
//     res.(j) <- add_zq f.(j) t;
//     res.(j +. len) <- add_zq f.(j) (neg_zq t) in
//   let inv_outer_inner (#i:size_t{i <. 7ul}) (len:len_t) h (i':nat) =
//     assert (i' < v (1ul <<. i));
//     start_t_lemma #i (u32 i');
//     let start:S.start_t (v len) = 2 * (v len) * i' in
//     let spec_tq = S.ntt_outer_inner (tq_v h f) (v len) start in
//     live h f /\ live h res /\ modifies (loc res) h0 h /\ i' < (pow2 (v i)) /\
//     // After each loop iteration, we should have the next 2*len elements match spec (from calling inner_inner)
//     Seq.equal 
//       (Seq.slice (S.tq_to_rq spec_tq) 0 (start + 2 * len))
//       (Seq.slice (S.tq_to_rq (tq_v h res)) 0 (start + 2 * len)) in
//   let body_outer_inner #i (len:len_t) (i':size_t{i' <. (1ul <<. i)}): 
//     Stack unit 
//     (requires (fun h -> inv_outer_inner #i len h (v i'))) 
//     (ensures (fun h0 _ h1 -> inv_outer_inner #i len h0 (v i') /\ inv_outer_inner #i len h1 (v i' + 1))) 
//   = 
//     assume (2ul *. len *. i' <. 256ul);
//     let start:start_t len = 2ul *. len *. i' in
//     let k = (128ul /. len) +. (start /. (2 *. len)) in
//     let z = zeta_table.(k) in
//     Lib.Loops.for 0ul len (inv_inner_inner len start z) (body_inner_inner start z len) in
//   let inv_outer h (i:nat) =
//     live h f /\ live h res /\ modifies (loc res) h0 h /\ i < 7 /\
//     Seq.equal (S.tq_to_rq (S.ntt_outer_intermediate (tq_v h f) i)) (S.tq_to_rq (tq_v h res)) in
//   let body_outer (i:size_t):
//     Stack unit
//     (requires (fun h -> inv_outer h (v i)))
//     (ensures (fun h0 _ h1 -> inv_outer h0 (v i) /\ inv_outer h1 (v i + 1)))
//   =
//     let len = 128ul >>. i in
//     Lib.Loops.for 0ul (1ul <<. i) (inv_outer_inner #i len) (body_outer_inner #i len) in
//   Lib.Loops.for 0ul 7ul inv_outer body_outer;
//   pop_frame ()


// val intt:
//     #deg: size_t
//   -> a:rq
//   -> res:rq
//   -> Stack unit
//   (requires fun h ->
//     live h a /\ live h res /\
//     disjoint a res
//   )
//   (ensures fun h0 _ h1 ->
//     live h1 a /\
//     live h1 res /\
//     disjoint a res /\
//     modifies (loc res) h0 h1 /\
//     Seq.equal (lpoly_v h1 res) (S.intt (tq_v h0 a))
//    )


// val mul_inner_loop:
//     #deg: size_t
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> k:size_t{ 0 <= v k /\ v k < v deg }
//   -> res:lpoly deg
//   -> Stack unit
//   (requires fun h ->
//     live h a /\ live h b /\ live h res /\
//     disjoint a b /\ disjoint a res /\ disjoint b res
//   )
//   (ensures fun h0 _ h1 ->
//     live h1 a /\
//     live h1 b /\
//     live h1 res /\
//     disjoint a b /\
//     disjoint a res /\
//     disjoint b res /\
//     Seq.index (lpoly_v h1 res) (v k) == S.mul_ab_kth_coeff (lpoly_v h0 a) (lpoly_v h0 b) (v k)
//    )
// let mul_inner_loop #deg a b k res =
//   let h0 = ST.get () in
//   let spec_coeff: erased _ = S.mul_ab_kth_coeff (lpoly_v h0 a) (lpoly_v h0 b) (v k) in
//   let inv h (i:nat) =
//     live h a /\ live h b /\ i <= v deg in
//   let body (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v deg }):
//     Stack unit
//     (requires (fun h -> inv h (U32.v i)))
//     (ensures (fun h0 () h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
//     =
//       let ai = a.(i) in
//       let bi = b.(i) in
//       if k <=. i then
//         let a_coeff = a.(k) in
//         let b_coeff = b.(i -. k) in
//         let add_ith_component = add_zq res.(i) (mul_zq a_coeff b_coeff) in
//         res.(i) <- add_ith_component
//       else
//         let a_coeff = a.(k) in
//         let b_coeff = b.(deg +. k -. i) in
//         let add_ith_component = add_zq res.(k) (neg_zq (mul_zq a_coeff b_coeff)) in
//         res.(k) <- add_ith_component
//     in
//   Lib.Loops.for 0ul deg inv body

// val mul:
//     #deg: size_t
//   -> a:lpoly deg
//   -> b:lpoly deg
//   -> res:lpoly deg
//   -> Stack unit
//   (requires fun h ->
//     live h a /\ live h b /\ live h res /\
//     disjoint a b /\ disjoint a res /\ disjoint b res
//   )
//   (ensures fun h0 _ h1 ->
//     live h1 a /\
//     live h1 b /\
//     live h1 res /\
//     disjoint a b /\
//     disjoint a res /\
//     disjoint b res /\
//     modifies (loc res) h0 h1 /\
//     Seq.equal (lpoly_v h1 res) (S.mul_quotient_ring (lpoly_v h0 a) (lpoly_v h0 b))
//    )
// let mul #deg a b res =
//   push_frame ();
//   let h0 = ST.get () in
//   let spec_prod: erased _ = S.mul_quotient_ring (lpoly_v h0 a) (lpoly_v h0 b) in
//   let inv_i h (i:nat) =
//     live h a /\ live h b /\ live h res /\ modifies (loc res) h0 h /\
//     i <= v deg /\
//     (i < v deg /\ Seq.equal (lpoly_v h res) (S.mul_intermediate (lpoly_v h0 a) (lpoly_v h0 b) i ((v deg) - 1))) \/
//     Seq.equal (lpoly_v h res) (Seq.create (v deg) 0) in
//   let body_i (i: U32.t{ 0 <= U32.v i /\ U32.v i < U32.v deg }):
//     Stack unit
//     (requires (fun h -> inv_i h (U32.v i)))
//     (ensures (fun h0 () h1 -> inv_i h0 (U32.v i) /\ inv_i h1 (U32.v i + 1))) =
//     let h1 = ST.get () in
//     let inv_j h (j:nat) =
//       live h a /\ live h b /\ live h res /\ modifies (loc res) h0 h /\
//       j <= v deg /\
//       (j < v deg /\ Seq.equal (lpoly_v h res) (S.mul_intermediate (lpoly_v h0 a) (lpoly_v h0 b) (v i) j)) \/
//       Seq.equal (lpoly_v h res) (Seq.create (v deg) 0) in
//     let body_j (j: U32.t{ 0 <= U32.v j /\ U32.v j < U32.v deg }):
//       Stack unit
//       (requires (fun h -> inv_j h (U32.v j)))
//       (ensures (fun h0 () h1 -> inv_j h0 (U32.v j) /\ inv_j h1 (U32.v j + 1)))
//       =
//         let ai = a.(i) in
//         let bj = b.(j) in
//         let prod = mul_zq ai bj in
//         let coeff_index = add_mod_n i j in
//         let old = res.(coeff_index) in
//         res.(coeff_index) <- add_zq old prod
//       in
//     Lib.Loops.for 0ul deg inv_j body_j
//     in
//   Lib.Loops.for 0ul deg inv_i body_i;
//   pop_frame ()