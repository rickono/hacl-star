module Hacl.MLkem.NTT

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open FStar.Seq
open FStar.Int
open Lib.NatMod

module PS = Hacl.Spec.MLkem.Poly
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = Hacl.Spec.MLkem.NTT
module Seq = Lib.Sequence
module M = LowStar.Modifies
module U32 = FStar.UInt32
module LE = Lib.Exponentiation
module PT = Hacl.Impl.PrecompTable

open FStar.Ghost
open Lib.Buffer
open Lib.IntTypes
open Hacl.MLkem.Poly
// open Lib.Loops

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let zeta = u32 S.zeta

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

val precomp_zeta_lseq : erased (Seq.lseq zq 128)
let precomp_zeta_lseq =
  Seq.createi 128 (fun i -> 
    let z = S.zeta_to_k i in 
    let z':zq = u32 z in
    z')

val seq_eq_idx_lemma: #len:size_nat -> s1:lseq zq len -> s2:lseq zq len -> i:nat{i < len} -> Lemma (requires Seq.equal #_ #len s1 s2) (ensures Seq.index #_ #len s1 i == Seq.index #_ #len s2 i)
let seq_eq_idx_lemma s1 s2 i = ()

let is_zeta_table (table:lbuffer zq 128ul) h = Seq.equal (as_seq h table) precomp_zeta_lseq

val index_zeta_table:
    i:size_t{i <. 128ul}
  -> table:lbuffer zq 128ul
  -> Stack zq 
    (requires fun h -> live h table /\ is_zeta_table table h)
    (ensures fun h0 r h1 -> live h1 table /\ zq_v r = S.zeta_to_k (v i))
let index_zeta_table i table =
  table.(i)

val precomp_zeta: table:lbuffer zq 128ul -> Stack unit 
  (requires fun h -> live h table)
  (ensures fun h0 _ h1 -> live h1 table /\ is_zeta_table table h1)
let precomp_zeta table = 
  push_frame ();
  let h0 = ST.get () in
  let inv h (i:nat) = 
    live h table /\
    modifies (loc table) h0 h /\
    i <= 128 /\ 
    Seq.equal (Seq.slice precomp_zeta_lseq 0 i) (Seq.slice (as_seq h table) 0 i) in
  table.(0ul) <- u32 1;
  pow_mod_def #PS.q S.zeta 0;
  lemma_pow_mod #PS.q S.zeta 0;
  lemma_pow0 S.zeta;
  assert (S.zeta_to_k 0 == 1);
  let h' = ST.get () in
  assert (v (Seq.index (as_seq h' table) 0) == (S.zeta_to_k 0));
  let body (i: U32.t{1 <= U32.v i && U32.v i < 128}): 
    Stack unit 
    (requires fun h -> inv h (U32.v i))
    (ensures fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)) 
  =
    let h0 = ST.get () in
    let table_as_seq: erased (Seq.lseq zq 128) = as_seq h0 table in
    assert (Seq.equal (Seq.slice table_as_seq 0 (v i)) (Seq.slice precomp_zeta_lseq 0 (v i)));
    seq_eq_idx_lemma #(v i) (Seq.slice table_as_seq 0 (v i)) (Seq.slice precomp_zeta_lseq 0 (v i)) (v i - 1);
    assert ((Seq.index table_as_seq (v i - 1)) == (Seq.index precomp_zeta_lseq (v i - 1)));
    assert (v (Seq.index precomp_zeta_lseq (v i - 1)) == S.zeta_to_k (v i - 1));
    assert (v table.(i -. 1ul) == S.zeta_to_k (v i - 1));
    S.zeta_to_k_pos_lemma (v i);
    table.(i) <- mul_zq table.(i -. 1ul) zeta;
    let h1 = ST.get () in
    assert (v table.(i) == S.zeta_to_k (v i));
    assert (Seq.index (as_seq h1 table) (v i) == Seq. index precomp_zeta_lseq (v i));
    assert (Seq.equal (Seq.slice (as_seq h1 table) 0 (v i)) (Seq.slice precomp_zeta_lseq 0 (v i)));
    slice_plus_one #_ #128 #128 (as_seq h1 table) precomp_zeta_lseq 0 (v i)
  in
  Lib.Loops.for 1ul 128ul inv body;
  pop_frame ()

type len_t = l:size_t{v l = 2 || v l = 4 || v l = 8 || v l = 16 || v l = 32 || v l = 64 || v l = 128}
type start_t (len:len_t) = s:size_t{v s < 256 && (v s) % (2 * (v len)) = 0}
val start_plus_len: #len:len_t -> s:start_t len -> Lemma (ensures v s + v len < 256)
let start_plus_len #len s = ()

val start_t_lemma: 
    #i:size_t{v i < 7}
  -> i':size_t{i' <. (1ul <<. i)}
  -> Lemma (ensures 2 * (v (128ul >>. i)) * (v i' + 1) <= 256)
let start_t_lemma #i i' =
  let len = 128ul >>. i in
  assert (v i' < pow2 (v i));
  assume (pow2 7 = 128);
  assert (v len = pow2 7 / pow2 (v i));
  ()

val ntt_inner_inner_f_ok_1:
    j:nat
  -> len:len_t
  -> start:start_t len
  -> z:zq
  -> res_j:zq
  -> res_j_plus_len:zq
  -> f:PS.tq
  -> t:zq
  -> Lemma 
      (requires 
        j < v start + v len /\
        j >= v start /\
        v res_j = PS.index_tq f j /\ 
        j + v len < 256 /\
        v res_j_plus_len = PS.index_tq f (j + v len) /\ 
        v t = PS.mul_zq (v z) (v res_j_plus_len)
      )
      (ensures v (add_zq res_j t) = S.ntt_inner_inner_f j (v len) (v start) (v z) f)
let ntt_inner_inner_f_ok_1 j len start z res_j res_j_plus_len f t = ()

val ntt_inner_inner_f_ok_2:
    j:nat
  -> len:len_t
  -> start:start_t len
  -> z:zq
  -> res_j:zq
  -> res_j_minus_len:zq
  -> f:PS.tq
  -> t:zq
  -> Lemma 
      (requires 
        j < v start + 2 * (v len) /\
        j >= v start + v len /\
        j < 256 /\
        v res_j = PS.index_tq f j /\ 
        v res_j_minus_len = PS.index_tq f (j - v len) /\ 
        v t = PS.mul_zq (v z) (v res_j)
      )
      (ensures v (add_zq res_j_minus_len (neg_zq t)) = S.ntt_inner_inner_f j (v len) (v start) (v z) f)
let ntt_inner_inner_f_ok_2 j len start z res_j res_j_plus_len f t = ()

val seq_slice_idx_lemma:
    #a:eqtype
  -> #len:size_nat
  -> start:nat
  -> fin:nat{start <= fin /\ fin <= len}
  -> i:nat{start <= i /\ i < fin}
  -> s1:lseq a len
  -> s2:lseq a len
  -> Lemma 
      (requires Seq.equal (Seq.slice #_ #len s1 start fin) (Seq.slice #_ #len s2 start fin))
      (ensures Seq.index #a #len s1 i = Seq.index #a #len s2 i)
let seq_slice_idx_lemma #a #len start fin i s1 s2 =
  let slice_i = i - start in
  let slice1 = Seq.slice #_ #len s1 start fin in
  let slice2 = Seq.slice #_ #len s2 start fin in
  assert (Seq.index slice1 slice_i = Seq.index slice2 slice_i)

val seq_slice_idx_mismatched_lemma:
    #a:eqtype
  -> #s1_len:size_nat
  -> #s2_len:size_nat
  -> start_1:size_nat
  -> fin_1:size_nat{start_1 <= fin_1 /\ fin_1 <= s1_len}
  -> start_2:size_nat
  -> fin_2:size_nat{start_2 <= fin_2 /\ fin_2 <= s2_len}
  -> i:nat{0 <= i /\ i < fin_1 - start_1}
  -> s1:lseq a s1_len
  -> s2:lseq a s2_len
  -> Lemma 
      (requires 
        fin_2 - start_2 = fin_1 - start_1 /\ 
        Seq.equal 
          (Seq.slice #_ #s1_len s1 start_1 fin_1) 
          (Seq.slice #_ #s2_len s2 start_2 fin_2))
      (ensures Seq.index #a #s1_len s1 (start_1 + i) = Seq.index #a #s2_len s2 (start_2 + i))
let seq_slice_idx_mismatched_lemma #a #s1_len #s2_len start_1 fin_1 start_2 fin_2 i s1 s2 =
  let slice1 = Seq.slice #_ #s1_len s1 start_1 fin_1 in
  let slice2 = Seq.slice #_ #s2_len s2 start_2 fin_2 in
  assert (Seq.index slice1 i = Seq.index slice2 i)


val slice_minus_one:
    #a:eqtype
  -> #len:size_nat
  -> s1:lseq a len
  -> s2:lseq a len
  -> i:nat
  -> j:nat{i < j /\ j <= len}
  -> Lemma 
      (requires 
        Seq.equal 
          (Seq.slice #_ #len s1 i j) 
          (Seq.slice #_ #len s2 i j))
      (ensures 
        Seq.equal 
          (Seq.slice #_ #len s1 (i + 1) j)
          (Seq.slice #_ #len s2 (i + 1) j))
let slice_minus_one #a #len i j = admit()

#reset-options "--z3rlimit 20 --fuel 0 --ifuel 0"

let add_v_lemma (a b:U32.t): Lemma (requires v a <= 256 /\ v b <= 256) (ensures v (a +. b) = v a + v b) = ()

val j_bounds_lemma:
    len:len_t
  -> start:start_t len
  -> i:U32.t{0 <= v i /\ v i < v len}
  -> j:U32.t
  -> Lemma 
      (requires start +. i = j)
      (ensures
        j <. start +. len /\
        j >=. start /\
        j +. len <. 256ul /\
        j >=. 0ul /\
        j <. 256ul /\
        v j + v len < 256 /\
        v start + v i = v j
      )
let j_bounds_lemma len start i j = ()

let ntt_inner_inner_inv (res:rq) (len:len_t) (start:start_t len{v start + (2 * v len) <= 256}) (z:zq) (h0:HS.mem) (h:HS.mem) (i:nat) =
    let spec_res:erased (lseq PS.zq PS.n) = PS.tq_to_rq (S.ntt_inner_inner_func (v z) (tq_v h0 res) (v len) (v start)) in
    let first_len:erased (lbuffer_t MUT zq len) = Lib.Buffer.gsub res start len in
    let second_len = Lib.Buffer.gsub res (start +. len) len in
    let first_len_spec:erased (lseq PS.zq (v len)) = Seq.slice #_ #(PS.n) spec_res (v start) (v start + v len) in
    let second_len_spec:erased (lseq PS.zq (v len)) = Seq.slice #_ #(PS.n) spec_res (v start + v len) (v start + 2 * v len) in
    i <= v len /\
    live h res /\
    modifies (loc res) h0 h /\
    disjoint first_len second_len /\
    Seq.equal 
      (Seq.slice (lpoly_v h first_len) 0 i)
      (Seq.slice #_ #(v len) first_len_spec 0 i) /\
    Seq.equal 
      (Seq.slice (lpoly_v h second_len) 0 i)
      (Seq.slice #_ #(v len) second_len_spec 0 i) /\ 
    Seq.equal 
      (Seq.slice (lpoly_v h first_len) i (v len))
      (Seq.slice (lpoly_v h0 first_len) i (v len)) /\ 
    Seq.equal 
      (Seq.slice (lpoly_v h second_len) i (v len))
      (Seq.slice (lpoly_v h0 second_len) i (v len)) /\
    Seq.equal 
      (Seq.slice (lpoly_v h0 second_len) i (v len))
      (Seq.slice (lpoly_v h0 res) (i + v start + v len) (v start + 2 * v len))

#reset-options "--z3rlimit 20 --fuel 0 --ifuel 0 --split_queries always"
// This should be equivalent to running the S.ntt_inner_inner
val ntt_inner_inner:
    res:rq
  -> len:len_t
  -> start:start_t len{v start + (2 * v len) <= 256}
  -> z:zq
  -> Stack unit
  (requires fun h ->
    live h res)
  (ensures fun h0 _ h1 -> 
    live h1 res /\
    modifies (loc res) h0 h1 /\
    Seq.equal
      (Seq.slice (lpoly_v h1 res) (v start) (v start + v len + v len))
      (Seq.slice (PS.tq_to_rq (S.ntt_inner_inner_func (v z) (tq_v h0 res) (v len) (v start))) (v start) (v start + v len + v len)))
let ntt_inner_inner res len start z =
  let h0 = ST.get () in
  let spec_res: erased (lseq PS.zq PS.n) = (PS.tq_to_rq (S.ntt_inner_inner_func (v z) (tq_v h0 res)  (v len) (v start))) in

  let first_len = Lib.Buffer.sub res start len in
  let second_len = Lib.Buffer.sub res (start +. len) len in
  let first_len_spec:erased (lseq PS.zq (v len)) = Seq.slice #_ #(PS.n) spec_res (v start) (v start + v len) in
  let second_len_spec:erased (lseq PS.zq (v len)) = Seq.slice #_ #(PS.n) spec_res (v start + v len) (v start + 2 * v len) in

  let inv h (i:nat) =
    i <= v len /\
    live h res /\
    modifies (loc res) h0 h /\
    disjoint first_len second_len /\
    Seq.equal 
      (Seq.slice (lpoly_v h first_len) 0 i)
      (Seq.slice #_ #(v len) first_len_spec 0 i) /\
    Seq.equal 
      (Seq.slice (lpoly_v h second_len) 0 i)
      (Seq.slice #_ #(v len) second_len_spec 0 i) /\ 
    Seq.equal 
      (Seq.slice (lpoly_v h first_len) i (v len))
      (Seq.slice (lpoly_v h0 first_len) i (v len)) /\ 
    Seq.equal 
      (Seq.slice (lpoly_v h second_len) i (v len))
      (Seq.slice (lpoly_v h0 second_len) i (v len)) /\
    Seq.equal 
      (Seq.slice (lpoly_v h0 second_len) i (v len))
      (Seq.slice (lpoly_v h0 res) (i + v start + v len) (v start + 2 * v len)) in
  let body (i:U32.t{0 <= v i /\ v i < v len}):
    Stack unit 
    (requires fun h -> inv h (U32.v i))
    (ensures fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)) 
  =
    let j = start +. i in
    let h0' = ST.get () in
    let res_j = first_len.(i) in
    let res_j_plus_len = second_len.(i) in
    let t = mul_zq z res_j_plus_len in

    // j < start + len /\ j >= start /\ j + len < 256 /\ j >= 0
    j_bounds_lemma len start i j;

    // we want: f_j = S.ntt_inner_inner_f j len start z res /\
    //          f_j_plus_len = S.ntt_inner_inner_f j+len len start z res
    let f_j = add_zq res_j t in
    let f_j_plus_len = add_zq res_j (neg_zq t) in

    // Requires:
    // j_bounds_lemma:    j < v start + v len 
    // j_bounds_lemma:    j >= start
    // j_bounds_lemma:    j + v len < 256
    // Probably done?:    v t = PS.mul_zq (v z) (v res_j_plus_len)
    //                    v res_j = PS.index_tq f j
    //                        We need to prove: first_len.(i) = PS.index (tq_v h0 res) j
    //                    v res_j_plus_len = PS.index_tq f (j + v len)
    //                        We need to prove: second_len.(i) = PS.index (tq_v h0 res) (j + v len)
    seq_slice_idx_mismatched_lemma #_ #(v len) #256 (v i) (v len) (v start + v i) (v start + v len) 0 (lpoly_v h0 first_len) (lpoly_v h0 res);
    // h0_first_len[i] = h0_res[start + i]
    assert (Seq.index (lpoly_v h0 first_len) (U32.v i) = Seq.index (lpoly_v h0 res) (v start + v i));
    assert (Seq.index (lpoly_v h0 first_len) (U32.v i) = Seq.index (lpoly_v h0 res) (v j));
    seq_slice_idx_lemma #_ #(v len) (v i) (v len) (v i) (lpoly_v h0 first_len) (lpoly_v h0' first_len);
    assert (v res_j == PS.index_tq (tq_v h0 res) (v j));
    assert (v t = PS.mul_zq (v z) (v res_j_plus_len));

    assert ((v start + 2 * v len) - (v start + v len + v i) = (v len - v i));
    assert (Seq.equal 
            (Seq.slice (lpoly_v h0 second_len) (v i) (v len)) 
            (Seq.slice (lpoly_v h0 res) (v start + v len + v i) (v start + 2 * v len)));
    seq_slice_idx_mismatched_lemma #_ #(v len) #256 (v i) (v len) (v start + v len + v i) (v start + 2 * v len) 0 (lpoly_v h0 second_len) (lpoly_v h0 res);
    seq_slice_idx_lemma #_ #(v len) (v i) (v len) (v i) (lpoly_v h0 second_len) (lpoly_v h0' second_len);
    assert (v res_j_plus_len == PS.index_tq (tq_v h0 res) (v j + v len));

    ntt_inner_inner_f_ok_1 (v j) len start z res_j res_j_plus_len (tq_v h0 res) t;
    ntt_inner_inner_f_ok_2 (v j + v len) len start z res_j_plus_len res_j (tq_v h0 res) t;

    slice_minus_one #_ #((v len) - (v i))
                    (Seq.slice (lpoly_v h0 first_len) (v i) (v len)) 
                    (Seq.slice (lpoly_v h0 res) (v start + v i) (v start + v len))
                    0 ((v len) - (v i));
    slice_minus_one #_ #((v len) - (v i))
                    (Seq.slice (lpoly_v h0 second_len) (v i) (v len)) 
                    (Seq.slice (lpoly_v h0 res) (v start + v len + v i) (v start + 2 * v len))
                    0 ((v len) - (v i));

    assert (Seq.equal 
      (Seq.slice (lpoly_v h0 second_len) (v i + 1) (v len))
      (Seq.slice (lpoly_v h0 res) (v i + 1 +v start + v len) (v start + 2 * v len)));

    first_len.(i) <- f_j;
    second_len.(i) <- f_j_plus_len;

    let h1 = ST.get () in
    assert (Seq.equal (Seq.slice (lpoly_v h1 first_len) 0 (U32.v i)) (Seq.slice #_ #(v len) first_len_spec 0 (U32.v i)));
    assert (Seq.equal (Seq.slice (lpoly_v h1 second_len) 0 (U32.v i)) (Seq.slice #_ #(v len) second_len_spec 0 (U32.v i)));
    slice_plus_one #_ #(v len) #(v len) (lpoly_v h1 first_len) first_len_spec 0 (U32.v i);
    slice_plus_one #_ #(v len) #(v len) (lpoly_v h1 second_len) second_len_spec 0 (U32.v i);
    
    assert (Seq.equal 
      (Seq.slice (lpoly_v h1 first_len) (v i + 1) (v len))
      (Seq.slice (lpoly_v h0 first_len) (v i + 1) (v len)));
    assert (Seq.equal 
      (Seq.slice (lpoly_v h1 second_len) (v i + 1) (v len))
      (Seq.slice (lpoly_v h0 second_len) (v i + 1) (v len)));
    assert (v i + 1 <= v len);
    assert (live h1 res);
    assume (modifies (loc res) h0 h1);
    assert (disjoint first_len second_len) in
  assume (inv h0 0);
  push_frame ();
  // Lib.Loops.for 0ul len inv body;
  let h1 = ST.get () in
  assume (inv h1 (v len));
  assert (Seq.equal (Seq.concat #_ #(v len) #(v len) first_len_spec second_len_spec ) (Seq.slice #_ #PS.n spec_res (v start) (v start + v len + v len)));
  assert (Seq.equal (lpoly_v h1 first_len) first_len_spec);
  assert (Seq.equal (lpoly_v h1 second_len) second_len_spec);
  assert (Seq.equal (Seq.slice (lpoly_v h1 res) (v start) (v start + v len + v len)) (Seq.concat (lpoly_v h1 first_len) (lpoly_v h1 second_len)));
  assert (Seq.equal
      (Seq.slice (lpoly_v h1 res) (v start) (v start + v len + v len))
      (Seq.slice (PS.tq_to_rq (S.ntt_inner_inner_func (v z) (tq_v h0 res) (v len) (v start))) (v start) (v start + v len + v len)));
  assert (modifies (loc res) h0 h1);
  assert (live h1 res);
  pop_frame ();
  ()

// let ntt_inner_inner res len start z =
//   push_frame ();
//   let h0 = ST.get () in
//   let spec_res: erased (lseq PS.zq PS.n) = (PS.tq_to_rq (S.ntt_inner_inner_func (v z) (tq_v h0 res)  (v len) (v start))) in
//   let spec_tq: erased (PS.tq) = (S.ntt_inner_inner_func (v z) (tq_v h0 res)  (v len) (v start)) in
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
//       (Seq.slice #_ #(PS.n) spec_res (v start) j) /\
//     Seq.equal 
//       (Seq.slice (lpoly_v h res) (v start + v len) (v len + j))
//       (Seq.slice #_ #(PS.n) spec_res (v start + v len) (v len + j)) in
//   let body (j:U32.t{v start <= v j /\ v j < v loop_stop}): 
//     Stack unit 
//     (requires fun h -> inv h (U32.v j))
//     (ensures fun h0 _ h1 -> inv h0 (U32.v j) /\ inv h1 (U32.v j + 1)) 
//   =
//     let h0' = ST.get () in
//     let res_j = res.(j) in
//     let res_j_plus_len = res.(j +. len) in
//     let t = mul_zq z res_j_plus_len in
//     // // res[j:start+len] = res0[j:start+len]
//     // // assert (Seq.equal (Seq.slice (lpoly_v h0' res) (v j) (v start + v len)) (Seq.slice (lpoly_v h0 res) (v j) (v start + v len)));
//     seq_slice_idx_lemma #_ (v j) (v start + v len) (v j) (lpoly_v h0' res) (lpoly_v h0 res);
//     // res[j] = res0[j]
//     // assert (Seq.index (lpoly_v h0' res) (v j) = Seq.index (lpoly_v h0 res) (v j));
//     seq_slice_idx_lemma #_ (v j + v len) (v start + 2 * (v len)) (v j + v len) (lpoly_v h0' res) (lpoly_v h0 res);
//     // res[j+len] = res0[j+len]
//     // assert (Seq.index (lpoly_v h0' res) (v j + v len) = Seq.index (lpoly_v h0 res) (v j + v len));
//     ntt_inner_inner_f_ok_1 (v j) len start z res_j res_j_plus_len (tq_v h0 res) t;
//     // // this gives us res[j] + t (in h0') = S.ntt_inner_inner_f j len start z res (in h0)
//     ntt_inner_inner_f_ok_2 (v j + v len) len start z res_j_plus_len res_j (tq_v h0 res) t;
//     // // This gives us res[j] - t (in h0') = S.ntt_inner_inner_f j+len len start z res (in h0)
//     assert (v (add_zq res_j t) == S.ntt_inner_inner_f (v j) (v len) (v start) (v z) (tq_v h0' res));
//     assert (v (add_zq res_j (neg_zq t)) == S.ntt_inner_inner_f (v j + v len) (v len) (v start) (v z) (tq_v h0' res));
//     res.(j) <- add_zq res_j t;
//     res.(j +. len) <- add_zq res_j (neg_zq t);
//     assert (v j + v len > v j);
//     assert (v (j +. len) > v j);
//     assert (v (j +. len) > v j + 1);
//     let h1 = ST.get () in
//     // assert (Seq.index (lpoly_v h1 res) (v j) == Seq.index #_ #(S.n) spec_res (v j));
//     // assert (Seq.equal (Seq.slice (lpoly_v h1 res) (v start) (v j)) (Seq.slice #_ #(S.n) spec_res (v start) (v j)));
//     // slice_plus_one #_ #256 #256 (lpoly_v h1 res) spec_res (v start) (v j);
//     // // assert (Seq.index (lpoly_v h1 res) (v j + v len) == Seq.index #_ #(S.n) spec_res (v j + v len));
//     // // assert (Seq.equal (Seq.slice (lpoly_v h1 res) (v start + v len) (v j + v len)) (Seq.slice #_ #(S.n) spec_res (v start + v len) (v j + v len)));
//     // slice_plus_one #_ #256 #256 (lpoly_v h1 res) spec_res (v start + v len) (v j + v len);
//     assert (v j + v len >= v start + v len);
//     assert (v j < v j + v len);
//     // assume (Seq.equal (Seq.slice (lpoly_v h1 res) (v j + 1) (v start + v len)) (Seq.slice (lpoly_v h0 res) (v j + 1) (v start + v len)));
//     // assume (Seq.equal (Seq.slice (lpoly_v h1 res) (v j + 1 + v len) (v start + 2 * (v len))) (Seq.slice (lpoly_v h0 res) (v j + 1 + v len) (v start + 2 * (v len))));
//     // assume (v j + 1 < v start + v len);
//     // assume (v j + 1 <= 256) in
//     assert (v j + 1 <= v start + v len);
//     assert (v j + 1 >= v start);
//     assert (v j + 1 <= 256);
//     assert (v j >= 0);
//     assume (Seq.equal (Seq.slice (lpoly_v h1 res) (v j + 1) (v start + v len)) (Seq.slice (lpoly_v h0 res) (v j + 1) (v start + v len)));
//     assume (Seq.equal (Seq.slice (lpoly_v h1 res) (v j + 1 + v len) (v start + 2 * (v len))) (Seq.slice (lpoly_v h0 res) (v j + 1 + v len) (v start + 2 * (v len))));
//     assert (Seq.equal (Seq.slice (lpoly_v h1 res) (v start) (v j + 1)) (Seq.slice #_ #(PS.n) spec_res (v start) (v j + 1)));
//     assert (Seq.equal (Seq.slice (lpoly_v h1 res) (v start + v len) (v j + 1 + v len)) (Seq.slice #_ #(PS.n) spec_res (v start + v len) (v j + 1 + v len))) in
//   admit()
  // Lib.Loops.for start loop_stop inv body;
  // pop_frame ()


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
//     PS.tq_eq (tq_v h1 res) (S.ntt_outer_inner (tq_v h0 res) (v len) 0))
// let ntt_outer_inner res zeta_table i =
//   // Start goes from 0->2^8
//   // Increments by 2*len each time, say len=2^(7-i)
//   // # of loops is 2^8 / (2*2^(7-i)) = 2^i = 1 <<. i
//   assume(is_len_t (128ul >>. i));
//   let h0 = ST.get () in
//   let len:len_t = 128ul >>. i in
//   let loop_iters = 1ul <<. i in
//   let spec_res: erased _ = PS.tq_to_rq (S.ntt_outer_inner (tq_v h0 res) (v len) 0) in
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
//     PS.tq_eq (tq_v h1 res) (S.ntt (lpoly_v h0 f))
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
//       (Seq.slice (PS.tq_to_rq spec_tq) (v start) (j + 1)) /\
//     Seq.equal 
//       (Seq.slice (lpoly_v h res) (v start + v len) (v len + j + 1)) 
//       (Seq.slice (PS.tq_to_rq spec_tq) (v start + v len) (v len + j + 1)) in
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
//       (Seq.slice (PS.tq_to_rq spec_tq) 0 (start + 2 * len))
//       (Seq.slice (PS.tq_to_rq (tq_v h res)) 0 (start + 2 * len)) in
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
//     Seq.equal (PS.tq_to_rq (S.ntt_outer_intermediate (tq_v h f) i)) (PS.tq_to_rq (tq_v h res)) in
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
