module Hacl.SHA3

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.SHA3

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = Spec.SHA3

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val shake128_hacl:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> outputByteLen:size_t
  -> output:lbuffer uint8 outputByteLen
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.shake128 (v inputByteLen) (as_seq h0 input) (v outputByteLen))
let shake128_hacl inputByteLen input outputByteLen output =
  keccak 1344ul 256ul inputByteLen input (byte 0x1F) outputByteLen output

val shake256_hacl:
    inputByteLen:size_t
  -> input:lbuffer uint8 inputByteLen
  -> outputByteLen:size_t
  -> output:lbuffer uint8 outputByteLen
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.shake256 (v inputByteLen) (as_seq h0 input) (v outputByteLen))
let shake256_hacl inputByteLen input outputByteLen output =
  keccak 1088ul 512ul inputByteLen input (byte 0x1F) outputByteLen output

val sha3_224:
    output:lbuffer uint8 28ul
  -> input:buffer_t MUT uint8
  -> input_len:size_t{v input_len == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_224 (v input_len) (as_seq h0 (input <: lbuffer uint8 input_len)))
let sha3_224 output input input_len =
  keccak 1152ul 448ul input_len input (byte 0x06) 28ul output

val sha3_256:
    output:lbuffer uint8 32ul
  -> input:buffer_t MUT uint8
  -> input_len:size_t{v input_len == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_256 (v input_len) (as_seq h0 (input <: lbuffer uint8 input_len)))
let sha3_256 output input input_len =
  keccak 1088ul 512ul input_len input (byte 0x06) 32ul output

val sha3_384:
    output:lbuffer uint8 48ul
  -> input:buffer_t MUT uint8
  -> input_len:size_t{v input_len == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_384 (v input_len) (as_seq h0 (input <: lbuffer uint8 input_len)))
let sha3_384 output input input_len =
  keccak 832ul 768ul input_len input (byte 0x06) 48ul output

val sha3_512:
    output:lbuffer uint8 64ul
  -> input:buffer_t MUT uint8
  -> input_len:size_t{v input_len == length input}
  -> Stack unit
     (requires fun h ->
       live h input /\ live h output /\ disjoint input output)
     (ensures  fun h0 _ h1 ->
       modifies (loc output) h0 h1 /\
       as_seq h1 output ==
       S.sha3_512 (v input_len) (as_seq h0 (input <: lbuffer uint8 input_len)))
let sha3_512 output input input_len =
  keccak 576ul 1024ul input_len input (byte 0x06) 64ul output
