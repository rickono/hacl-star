module Hacl.Gf128.PreComp

open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer
open Lib.IntVector

open Hacl.Impl.Gf128.Fields
open Hacl.Impl.Gf128.Generic

module ST = FStar.HyperStack.ST

module S = Spec.GF128
module GF = Spec.GaloisField
module Vec = Hacl.Spec.GF128.Vec


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

inline_for_extraction noextract
let gcm_ctx_elem = uint64
inline_for_extraction noextract
let gcm_ctx_len = 266ul
inline_for_extraction noextract
let gcm_ctx_elem_zero = u64 0
inline_for_extraction noextract
let gcm_ctx = lbuffer gcm_ctx_elem gcm_ctx_len


[@CInline]
val gcm_init:
    ctx:gcm_ctx
  -> key:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h ctx /\ live h key /\ disjoint ctx key)
  (ensures  fun h0 _ h1 -> modifies1 ctx h0 h1)

let gcm_init ctx key = gcm_init #Vec.PreComp ctx key


[@CInline]
val gcm_update_blocks:
    ctx:gcm_ctx
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h ctx /\ live h text)
  (ensures  fun h0 _ h1 -> modifies1 ctx h0 h1)

let gcm_update_blocks ctx len text =
  let acc = get_acc ctx in
  let pre = get_precomp ctx in
  gf128_update_vec #Vec.PreComp acc pre len text


[@CInline]
val gcm_update_blocks_padded:
    ctx:gcm_ctx
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h -> live h ctx /\ live h text)
  (ensures  fun h0 _ h1 -> modifies1 ctx h0 h1)

let gcm_update_blocks_padded ctx len text =
  gcm_update_blocks ctx len text


[@CInline]
val gcm_emit:
    tag:lbuffer uint8 16ul
  -> ctx:gcm_ctx ->
  Stack unit
  (requires fun h -> live h ctx /\ live h tag)
  (ensures  fun h0 _ h1 -> modifies1 tag h0 h1)

let gcm_emit tag ctx =
  let acc = get_acc ctx in
  decode tag acc


[@CInline]
val ghash:
    tag:block
  -> len:size_t
  -> text:lbuffer uint8 len
  -> key:block ->
  Stack unit
  (requires fun h -> live h tag /\ live h text /\ live h key)
  (ensures  fun h0 _ h1 -> modifies1 tag h0 h1)

let ghash tag len text key =
  ghash #Vec.PreComp tag len text key
