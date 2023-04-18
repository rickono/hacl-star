/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "internal/EverCrypt_Hash.h"

#include "internal/Vale.h"
#include "internal/Hacl_Hash_SHA3.h"
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include "internal/Hacl_Hash_MD5.h"
#include "internal/Hacl_Hash_Blake2s_Simd128.h"
#include "internal/Hacl_Hash_Blake2s.h"
#include "internal/Hacl_Hash_Blake2b_Simd256.h"
#include "internal/Hacl_Hash_Blake2b.h"
#include "config.h"

#define MD5_s 0
#define SHA1_s 1
#define SHA2_224_s 2
#define SHA2_256_s 3
#define SHA2_384_s 4
#define SHA2_512_s 5
#define SHA3_224_s 6
#define SHA3_256_s 7
#define SHA3_384_s 8
#define SHA3_512_s 9
#define Blake2S_s 10
#define Blake2S_128_s 11
#define Blake2B_s 12
#define Blake2B_256_s 13

typedef uint8_t state_s_tags;

typedef struct EverCrypt_Hash_state_s_s
{
  state_s_tags tag;
  union {
    uint32_t *case_MD5_s;
    uint32_t *case_SHA1_s;
    uint32_t *case_SHA2_224_s;
    uint32_t *case_SHA2_256_s;
    uint64_t *case_SHA2_384_s;
    uint64_t *case_SHA2_512_s;
    uint64_t *case_SHA3_224_s;
    uint64_t *case_SHA3_256_s;
    uint64_t *case_SHA3_384_s;
    uint64_t *case_SHA3_512_s;
    uint32_t *case_Blake2S_s;
    Lib_IntVector_Intrinsics_vec128 *case_Blake2S_128_s;
    uint64_t *case_Blake2B_s;
    Lib_IntVector_Intrinsics_vec256 *case_Blake2B_256_s;
  }
  ;
}
EverCrypt_Hash_state_s;

static Spec_Hash_Definitions_hash_alg alg_of_state(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    return Spec_Hash_Definitions_MD5;
  }
  if (scrut.tag == SHA1_s)
  {
    return Spec_Hash_Definitions_SHA1;
  }
  if (scrut.tag == SHA2_224_s)
  {
    return Spec_Hash_Definitions_SHA2_224;
  }
  if (scrut.tag == SHA2_256_s)
  {
    return Spec_Hash_Definitions_SHA2_256;
  }
  if (scrut.tag == SHA2_384_s)
  {
    return Spec_Hash_Definitions_SHA2_384;
  }
  if (scrut.tag == SHA2_512_s)
  {
    return Spec_Hash_Definitions_SHA2_512;
  }
  if (scrut.tag == SHA3_224_s)
  {
    return Spec_Hash_Definitions_SHA3_224;
  }
  if (scrut.tag == SHA3_256_s)
  {
    return Spec_Hash_Definitions_SHA3_256;
  }
  if (scrut.tag == SHA3_384_s)
  {
    return Spec_Hash_Definitions_SHA3_384;
  }
  if (scrut.tag == SHA3_512_s)
  {
    return Spec_Hash_Definitions_SHA3_512;
  }
  if (scrut.tag == Blake2S_s)
  {
    return Spec_Hash_Definitions_Blake2S;
  }
  if (scrut.tag == Blake2S_128_s)
  {
    return Spec_Hash_Definitions_Blake2S;
  }
  if (scrut.tag == Blake2B_s)
  {
    return Spec_Hash_Definitions_Blake2B;
  }
  if (scrut.tag == Blake2B_256_s)
  {
    return Spec_Hash_Definitions_Blake2B;
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static EverCrypt_Hash_state_s *create_in(Spec_Hash_Definitions_hash_alg a)
{
  EverCrypt_Hash_state_s s;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC((uint32_t)4U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = MD5_s, { .case_MD5_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC((uint32_t)5U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA1_s, { .case_SHA1_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA2_224_s, { .case_SHA2_224_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA2_256_s, { .case_SHA2_256_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA2_384_s, { .case_SHA2_384_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)8U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA2_512_s, { .case_SHA2_512_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA3_224_s, { .case_SHA3_224_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA3_256_s, { .case_SHA3_256_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA3_384_s, { .case_SHA3_384_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)25U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = SHA3_512_s, { .case_SHA3_512_s = buf } });
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        bool vec128 = EverCrypt_AutoConfig2_has_vec128();
        #if HACL_CAN_COMPILE_VEC128
        if (vec128)
        {
          s =
            (
              (EverCrypt_Hash_state_s){
                .tag = Blake2S_128_s,
                { .case_Blake2S_128_s = Hacl_Hash_Blake2s_Simd128_malloc_with_key() }
              }
            );
        }
        else
        {
          uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint32_t));
          s = ((EverCrypt_Hash_state_s){ .tag = Blake2S_s, { .case_Blake2S_s = buf } });
        }
        #else
        uint32_t *buf = (uint32_t *)KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint32_t));
        s = ((EverCrypt_Hash_state_s){ .tag = Blake2S_s, { .case_Blake2S_s = buf } });
        #endif
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        bool vec256 = EverCrypt_AutoConfig2_has_vec256();
        #if HACL_CAN_COMPILE_VEC256
        if (vec256)
        {
          s =
            (
              (EverCrypt_Hash_state_s){
                .tag = Blake2B_256_s,
                { .case_Blake2B_256_s = Hacl_Hash_Blake2b_Simd256_malloc_with_key() }
              }
            );
        }
        else
        {
          uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
          s = ((EverCrypt_Hash_state_s){ .tag = Blake2B_s, { .case_Blake2B_s = buf } });
        }
        #else
        uint64_t *buf = (uint64_t *)KRML_HOST_CALLOC((uint32_t)16U, sizeof (uint64_t));
        s = ((EverCrypt_Hash_state_s){ .tag = Blake2B_s, { .case_Blake2B_s = buf } });
        #endif
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  EverCrypt_Hash_state_s
  *buf = (EverCrypt_Hash_state_s *)KRML_HOST_MALLOC(sizeof (EverCrypt_Hash_state_s));
  buf[0U] = s;
  return buf;
}

static void init(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_MD5_init(p1);
    return;
  }
  if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_SHA1_init(p1);
    return;
  }
  if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_init_224(p1);
    return;
  }
  if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_init_256(p1);
    return;
  }
  if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_init_384(p1);
    return;
  }
  if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_init_512(p1);
    return;
  }
  if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    memset(p1, 0U, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    memset(p1, 0U, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    memset(p1, 0U, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    memset(p1, 0U, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    Hacl_Hash_Blake2s_init(p1, (uint32_t)0U, (uint32_t)32U);
    return;
  }
  if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    #if HACL_CAN_COMPILE_VEC128
    Hacl_Hash_Blake2s_Simd128_init(p1, (uint32_t)0U, (uint32_t)32U);
    return;
    #else
    return;
    #endif
  }
  if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    Hacl_Hash_Blake2b_init(p1, (uint32_t)0U, (uint32_t)64U);
    return;
  }
  if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    #if HACL_CAN_COMPILE_VEC256
    Hacl_Hash_Blake2b_Simd256_init(p1, (uint32_t)0U, (uint32_t)64U);
    return;
    #else
    return;
    #endif
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static uint32_t
k224_256[64U] =
  {
    (uint32_t)0x428a2f98U, (uint32_t)0x71374491U, (uint32_t)0xb5c0fbcfU, (uint32_t)0xe9b5dba5U,
    (uint32_t)0x3956c25bU, (uint32_t)0x59f111f1U, (uint32_t)0x923f82a4U, (uint32_t)0xab1c5ed5U,
    (uint32_t)0xd807aa98U, (uint32_t)0x12835b01U, (uint32_t)0x243185beU, (uint32_t)0x550c7dc3U,
    (uint32_t)0x72be5d74U, (uint32_t)0x80deb1feU, (uint32_t)0x9bdc06a7U, (uint32_t)0xc19bf174U,
    (uint32_t)0xe49b69c1U, (uint32_t)0xefbe4786U, (uint32_t)0x0fc19dc6U, (uint32_t)0x240ca1ccU,
    (uint32_t)0x2de92c6fU, (uint32_t)0x4a7484aaU, (uint32_t)0x5cb0a9dcU, (uint32_t)0x76f988daU,
    (uint32_t)0x983e5152U, (uint32_t)0xa831c66dU, (uint32_t)0xb00327c8U, (uint32_t)0xbf597fc7U,
    (uint32_t)0xc6e00bf3U, (uint32_t)0xd5a79147U, (uint32_t)0x06ca6351U, (uint32_t)0x14292967U,
    (uint32_t)0x27b70a85U, (uint32_t)0x2e1b2138U, (uint32_t)0x4d2c6dfcU, (uint32_t)0x53380d13U,
    (uint32_t)0x650a7354U, (uint32_t)0x766a0abbU, (uint32_t)0x81c2c92eU, (uint32_t)0x92722c85U,
    (uint32_t)0xa2bfe8a1U, (uint32_t)0xa81a664bU, (uint32_t)0xc24b8b70U, (uint32_t)0xc76c51a3U,
    (uint32_t)0xd192e819U, (uint32_t)0xd6990624U, (uint32_t)0xf40e3585U, (uint32_t)0x106aa070U,
    (uint32_t)0x19a4c116U, (uint32_t)0x1e376c08U, (uint32_t)0x2748774cU, (uint32_t)0x34b0bcb5U,
    (uint32_t)0x391c0cb3U, (uint32_t)0x4ed8aa4aU, (uint32_t)0x5b9cca4fU, (uint32_t)0x682e6ff3U,
    (uint32_t)0x748f82eeU, (uint32_t)0x78a5636fU, (uint32_t)0x84c87814U, (uint32_t)0x8cc70208U,
    (uint32_t)0x90befffaU, (uint32_t)0xa4506cebU, (uint32_t)0xbef9a3f7U, (uint32_t)0xc67178f2U
  };

void EverCrypt_Hash_update_multi_256(uint32_t *s, uint8_t *blocks, uint32_t n)
{
  bool has_shaext = EverCrypt_AutoConfig2_has_shaext();
  bool has_sse = EverCrypt_AutoConfig2_has_sse();
  #if HACL_CAN_COMPILE_VALE
  if (has_shaext && has_sse)
  {
    uint64_t n1 = (uint64_t)n;
    uint64_t scrut = sha256_update(s, blocks, n1, k224_256);
    return;
  }
  #endif
  Hacl_Hash_SHA2_update_multi_256(s, blocks, n);
}

static void
update_multi(EverCrypt_Hash_state_s *s, uint64_t prevlen, uint8_t *blocks, uint32_t len)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    uint32_t n = len / (uint32_t)64U;
    Hacl_Hash_MD5_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    uint32_t n = len / (uint32_t)64U;
    Hacl_Hash_SHA1_update_multi(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    uint32_t n = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    uint32_t n = len / (uint32_t)64U;
    EverCrypt_Hash_update_multi_256(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    uint32_t n = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_384(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    uint32_t n = len / (uint32_t)128U;
    Hacl_Hash_SHA2_update_multi_512(p1, blocks, n);
    return;
  }
  if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    uint32_t n = len / (uint32_t)144U;
    for (uint32_t i = (uint32_t)0U; i < n; i++)
    {
      uint8_t *block = blocks + i * (uint32_t)144U;
      Hacl_Impl_SHA3_absorb_inner((uint32_t)144U, block, p1);
    }
    return;
  }
  if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    uint32_t n = len / (uint32_t)136U;
    for (uint32_t i = (uint32_t)0U; i < n; i++)
    {
      uint8_t *block = blocks + i * (uint32_t)136U;
      Hacl_Impl_SHA3_absorb_inner((uint32_t)136U, block, p1);
    }
    return;
  }
  if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    uint32_t n = len / (uint32_t)104U;
    for (uint32_t i = (uint32_t)0U; i < n; i++)
    {
      uint8_t *block = blocks + i * (uint32_t)104U;
      Hacl_Impl_SHA3_absorb_inner((uint32_t)104U, block, p1);
    }
    return;
  }
  if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    uint32_t n = len / (uint32_t)72U;
    for (uint32_t i = (uint32_t)0U; i < n; i++)
    {
      uint8_t *block = blocks + i * (uint32_t)72U;
      Hacl_Impl_SHA3_absorb_inner((uint32_t)72U, block, p1);
    }
    return;
  }
  if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    uint32_t n = len / (uint32_t)64U;
    uint32_t wv[16U] = { 0U };
    Hacl_Hash_Blake2s_update_multi(n * (uint32_t)64U, wv, p1, prevlen, blocks, n);
    return;
  }
  if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    #if HACL_CAN_COMPILE_VEC128
    uint32_t n = len / (uint32_t)64U;
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 wv[4U] KRML_POST_ALIGN(16) = { 0U };
    Hacl_Hash_Blake2s_Simd128_update_multi(n * (uint32_t)64U, wv, p1, prevlen, blocks, n);
    return;
    #else
    return;
    #endif
  }
  if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    uint32_t n = len / (uint32_t)128U;
    uint64_t wv[16U] = { 0U };
    Hacl_Hash_Blake2b_update_multi(n * (uint32_t)128U,
      wv,
      p1,
      FStar_UInt128_uint64_to_uint128(prevlen),
      blocks,
      n);
    return;
  }
  if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    #if HACL_CAN_COMPILE_VEC256
    uint32_t n = len / (uint32_t)128U;
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv[4U] KRML_POST_ALIGN(32) = { 0U };
    Hacl_Hash_Blake2b_Simd256_update_multi(n * (uint32_t)128U,
      wv,
      p1,
      FStar_UInt128_uint64_to_uint128(prevlen),
      blocks,
      n);
    return;
    #else
    return;
    #endif
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

void
EverCrypt_Hash_update_last_256(
  uint32_t *s,
  uint64_t prev_len,
  uint8_t *input,
  uint32_t input_len
)
{
  uint32_t blocks_n = input_len / (uint32_t)64U;
  uint32_t blocks_len = blocks_n * (uint32_t)64U;
  uint8_t *blocks = input;
  uint32_t rest_len = input_len - blocks_len;
  uint8_t *rest = input + blocks_len;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  uint64_t total_input_len = prev_len + (uint64_t)input_len;
  uint32_t
  pad_len =
    (uint32_t)1U
    +
      ((uint32_t)128U - ((uint32_t)9U + (uint32_t)(total_input_len % (uint64_t)(uint32_t)64U)))
      % (uint32_t)64U
    + (uint32_t)8U;
  uint32_t tmp_len = rest_len + pad_len;
  uint8_t tmp_twoblocks[128U] = { 0U };
  uint8_t *tmp = tmp_twoblocks;
  uint8_t *tmp_rest = tmp;
  uint8_t *tmp_pad = tmp + rest_len;
  memcpy(tmp_rest, rest, rest_len * sizeof (uint8_t));
  Hacl_Hash_Core_SHA2_pad_256(total_input_len, tmp_pad);
  EverCrypt_Hash_update_multi_256(s, tmp, tmp_len / (uint32_t)64U);
}

static void
update_last(EverCrypt_Hash_state_s *s, uint64_t prev_len, uint8_t *last, uint32_t last_len)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_MD5_update_last(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_SHA1_update_last(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    EverCrypt_Hash_update_last_256(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    EverCrypt_Hash_update_last_256(p1, prev_len, last, last_len);
    return;
  }
  if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_SHA2_update_last_384(p1, FStar_UInt128_uint64_to_uint128(prev_len), last, last_len);
    return;
  }
  if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_SHA2_update_last_512(p1, FStar_UInt128_uint64_to_uint128(prev_len), last, last_len);
    return;
  }
  if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    if (last_len == (uint32_t)144U)
    {
      Hacl_Impl_SHA3_absorb_inner((uint32_t)144U, last, p1);
      uint8_t *uu____0 = last + last_len;
      uint8_t lastBlock[144U] = { 0U };
      memcpy(lastBlock, uu____0, (uint32_t)0U * sizeof (uint8_t));
      lastBlock[0U] = (uint8_t)0x06U;
      Hacl_Impl_SHA3_loadState((uint32_t)144U, lastBlock, p1);
      uint8_t nextBlock[144U] = { 0U };
      nextBlock[143U] = (uint8_t)0x80U;
      Hacl_Impl_SHA3_loadState((uint32_t)144U, nextBlock, p1);
      Hacl_Impl_SHA3_state_permute(p1);
      return;
    }
    uint8_t lastBlock[144U] = { 0U };
    memcpy(lastBlock, last, last_len * sizeof (uint8_t));
    lastBlock[last_len] = (uint8_t)0x06U;
    Hacl_Impl_SHA3_loadState((uint32_t)144U, lastBlock, p1);
    uint8_t nextBlock[144U] = { 0U };
    nextBlock[143U] = (uint8_t)0x80U;
    Hacl_Impl_SHA3_loadState((uint32_t)144U, nextBlock, p1);
    Hacl_Impl_SHA3_state_permute(p1);
    return;
  }
  if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    if (last_len == (uint32_t)136U)
    {
      Hacl_Impl_SHA3_absorb_inner((uint32_t)136U, last, p1);
      uint8_t *uu____1 = last + last_len;
      uint8_t lastBlock[136U] = { 0U };
      memcpy(lastBlock, uu____1, (uint32_t)0U * sizeof (uint8_t));
      lastBlock[0U] = (uint8_t)0x06U;
      Hacl_Impl_SHA3_loadState((uint32_t)136U, lastBlock, p1);
      uint8_t nextBlock[136U] = { 0U };
      nextBlock[135U] = (uint8_t)0x80U;
      Hacl_Impl_SHA3_loadState((uint32_t)136U, nextBlock, p1);
      Hacl_Impl_SHA3_state_permute(p1);
      return;
    }
    uint8_t lastBlock[136U] = { 0U };
    memcpy(lastBlock, last, last_len * sizeof (uint8_t));
    lastBlock[last_len] = (uint8_t)0x06U;
    Hacl_Impl_SHA3_loadState((uint32_t)136U, lastBlock, p1);
    uint8_t nextBlock[136U] = { 0U };
    nextBlock[135U] = (uint8_t)0x80U;
    Hacl_Impl_SHA3_loadState((uint32_t)136U, nextBlock, p1);
    Hacl_Impl_SHA3_state_permute(p1);
    return;
  }
  if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    if (last_len == (uint32_t)104U)
    {
      Hacl_Impl_SHA3_absorb_inner((uint32_t)104U, last, p1);
      uint8_t *uu____2 = last + last_len;
      uint8_t lastBlock[104U] = { 0U };
      memcpy(lastBlock, uu____2, (uint32_t)0U * sizeof (uint8_t));
      lastBlock[0U] = (uint8_t)0x06U;
      Hacl_Impl_SHA3_loadState((uint32_t)104U, lastBlock, p1);
      uint8_t nextBlock[104U] = { 0U };
      nextBlock[103U] = (uint8_t)0x80U;
      Hacl_Impl_SHA3_loadState((uint32_t)104U, nextBlock, p1);
      Hacl_Impl_SHA3_state_permute(p1);
      return;
    }
    uint8_t lastBlock[104U] = { 0U };
    memcpy(lastBlock, last, last_len * sizeof (uint8_t));
    lastBlock[last_len] = (uint8_t)0x06U;
    Hacl_Impl_SHA3_loadState((uint32_t)104U, lastBlock, p1);
    uint8_t nextBlock[104U] = { 0U };
    nextBlock[103U] = (uint8_t)0x80U;
    Hacl_Impl_SHA3_loadState((uint32_t)104U, nextBlock, p1);
    Hacl_Impl_SHA3_state_permute(p1);
    return;
  }
  if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    if (last_len == (uint32_t)72U)
    {
      Hacl_Impl_SHA3_absorb_inner((uint32_t)72U, last, p1);
      uint8_t *uu____3 = last + last_len;
      uint8_t lastBlock[72U] = { 0U };
      memcpy(lastBlock, uu____3, (uint32_t)0U * sizeof (uint8_t));
      lastBlock[0U] = (uint8_t)0x06U;
      Hacl_Impl_SHA3_loadState((uint32_t)72U, lastBlock, p1);
      uint8_t nextBlock[72U] = { 0U };
      nextBlock[71U] = (uint8_t)0x80U;
      Hacl_Impl_SHA3_loadState((uint32_t)72U, nextBlock, p1);
      Hacl_Impl_SHA3_state_permute(p1);
      return;
    }
    uint8_t lastBlock[72U] = { 0U };
    memcpy(lastBlock, last, last_len * sizeof (uint8_t));
    lastBlock[last_len] = (uint8_t)0x06U;
    Hacl_Impl_SHA3_loadState((uint32_t)72U, lastBlock, p1);
    uint8_t nextBlock[72U] = { 0U };
    nextBlock[71U] = (uint8_t)0x80U;
    Hacl_Impl_SHA3_loadState((uint32_t)72U, nextBlock, p1);
    Hacl_Impl_SHA3_state_permute(p1);
    return;
  }
  if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    uint32_t wv[16U] = { 0U };
    Hacl_Hash_Blake2s_update_last(last_len, wv, p1, prev_len, last_len, last);
    return;
  }
  if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    #if HACL_CAN_COMPILE_VEC128
    KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 wv[4U] KRML_POST_ALIGN(16) = { 0U };
    Hacl_Hash_Blake2s_Simd128_update_last(last_len, wv, p1, prev_len, last_len, last);
    return;
    #else
    return;
    #endif
  }
  if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    uint64_t wv[16U] = { 0U };
    Hacl_Hash_Blake2b_update_last(last_len,
      wv,
      p1,
      FStar_UInt128_uint64_to_uint128(prev_len),
      last_len,
      last);
    return;
  }
  if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    #if HACL_CAN_COMPILE_VEC256
    KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 wv[4U] KRML_POST_ALIGN(32) = { 0U };
    Hacl_Hash_Blake2b_Simd256_update_last(last_len,
      wv,
      p1,
      FStar_UInt128_uint64_to_uint128(prev_len),
      last_len,
      last);
    return;
    #else
    return;
    #endif
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static void finish(EverCrypt_Hash_state_s *s, uint8_t *dst)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    Hacl_Hash_MD5_finish(p1, dst);
    return;
  }
  if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    Hacl_Hash_SHA1_finish(p1, dst);
    return;
  }
  if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    Hacl_Hash_Core_SHA2_finish_224(p1, dst);
    return;
  }
  if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    Hacl_Hash_Core_SHA2_finish_256(p1, dst);
    return;
  }
  if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    Hacl_Hash_Core_SHA2_finish_384(p1, dst);
    return;
  }
  if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    Hacl_Hash_Core_SHA2_finish_512(p1, dst);
    return;
  }
  if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    Hacl_Impl_SHA3_squeeze(p1, (uint32_t)144U, (uint32_t)28U, dst);
    return;
  }
  if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    Hacl_Impl_SHA3_squeeze(p1, (uint32_t)136U, (uint32_t)32U, dst);
    return;
  }
  if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    Hacl_Impl_SHA3_squeeze(p1, (uint32_t)104U, (uint32_t)48U, dst);
    return;
  }
  if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    Hacl_Impl_SHA3_squeeze(p1, (uint32_t)72U, (uint32_t)64U, dst);
    return;
  }
  if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    Hacl_Hash_Blake2s_finish((uint32_t)32U, dst, p1);
    return;
  }
  if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    #if HACL_CAN_COMPILE_VEC128
    Hacl_Hash_Blake2s_Simd128_finish((uint32_t)32U, dst, p1);
    return;
    #else
    return;
    #endif
  }
  if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    Hacl_Hash_Blake2b_finish((uint32_t)64U, dst, p1);
    return;
  }
  if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    #if HACL_CAN_COMPILE_VEC256
    Hacl_Hash_Blake2b_Simd256_finish((uint32_t)64U, dst, p1);
    return;
    #else
    return;
    #endif
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

static void free_(EverCrypt_Hash_state_s *s)
{
  EverCrypt_Hash_state_s scrut = *s;
  if (scrut.tag == MD5_s)
  {
    uint32_t *p1 = scrut.case_MD5_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA1_s)
  {
    uint32_t *p1 = scrut.case_SHA1_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_224_s)
  {
    uint32_t *p1 = scrut.case_SHA2_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_256_s)
  {
    uint32_t *p1 = scrut.case_SHA2_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_384_s)
  {
    uint64_t *p1 = scrut.case_SHA2_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA2_512_s)
  {
    uint64_t *p1 = scrut.case_SHA2_512_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_224_s)
  {
    uint64_t *p1 = scrut.case_SHA3_224_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_256_s)
  {
    uint64_t *p1 = scrut.case_SHA3_256_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_384_s)
  {
    uint64_t *p1 = scrut.case_SHA3_384_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == SHA3_512_s)
  {
    uint64_t *p1 = scrut.case_SHA3_512_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == Blake2S_s)
  {
    uint32_t *p1 = scrut.case_Blake2S_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p1 = scrut.case_Blake2S_128_s;
    KRML_ALIGNED_FREE(p1);
  }
  else if (scrut.tag == Blake2B_s)
  {
    uint64_t *p1 = scrut.case_Blake2B_s;
    KRML_HOST_FREE(p1);
  }
  else if (scrut.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p1 = scrut.case_Blake2B_256_s;
    KRML_ALIGNED_FREE(p1);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_FREE(s);
}

static void copy(EverCrypt_Hash_state_s *s_src, EverCrypt_Hash_state_s *s_dst)
{
  EverCrypt_Hash_state_s scrut0 = *s_src;
  if (scrut0.tag == MD5_s)
  {
    uint32_t *p_src = scrut0.case_MD5_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == MD5_s)
    {
      p_dst = x1.case_MD5_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)4U * sizeof (uint32_t));
    return;
  }
  if (scrut0.tag == SHA1_s)
  {
    uint32_t *p_src = scrut0.case_SHA1_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == SHA1_s)
    {
      p_dst = x1.case_SHA1_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)5U * sizeof (uint32_t));
    return;
  }
  if (scrut0.tag == SHA2_224_s)
  {
    uint32_t *p_src = scrut0.case_SHA2_224_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == SHA2_224_s)
    {
      p_dst = x1.case_SHA2_224_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint32_t));
    return;
  }
  if (scrut0.tag == SHA2_256_s)
  {
    uint32_t *p_src = scrut0.case_SHA2_256_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint32_t *p_dst;
    if (x1.tag == SHA2_256_s)
    {
      p_dst = x1.case_SHA2_256_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint32_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint32_t));
    return;
  }
  if (scrut0.tag == SHA2_384_s)
  {
    uint64_t *p_src = scrut0.case_SHA2_384_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == SHA2_384_s)
    {
      p_dst = x1.case_SHA2_384_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint64_t));
    return;
  }
  if (scrut0.tag == SHA2_512_s)
  {
    uint64_t *p_src = scrut0.case_SHA2_512_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == SHA2_512_s)
    {
      p_dst = x1.case_SHA2_512_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)8U * sizeof (uint64_t));
    return;
  }
  if (scrut0.tag == SHA3_224_s)
  {
    uint64_t *p_src = scrut0.case_SHA3_224_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == SHA3_224_s)
    {
      p_dst = x1.case_SHA3_224_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut0.tag == SHA3_256_s)
  {
    uint64_t *p_src = scrut0.case_SHA3_256_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == SHA3_256_s)
    {
      p_dst = x1.case_SHA3_256_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut0.tag == SHA3_384_s)
  {
    uint64_t *p_src = scrut0.case_SHA3_384_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == SHA3_384_s)
    {
      p_dst = x1.case_SHA3_384_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut0.tag == SHA3_512_s)
  {
    uint64_t *p_src = scrut0.case_SHA3_512_s;
    EverCrypt_Hash_state_s x1 = *s_dst;
    uint64_t *p_dst;
    if (x1.tag == SHA3_512_s)
    {
      p_dst = x1.case_SHA3_512_s;
    }
    else
    {
      p_dst = KRML_EABORT(uint64_t *, "unreachable (pattern matches are exhaustive in F*)");
    }
    memcpy(p_dst, p_src, (uint32_t)25U * sizeof (uint64_t));
    return;
  }
  if (scrut0.tag == Blake2S_s)
  {
    uint32_t *p_src = scrut0.case_Blake2S_s;
    EverCrypt_Hash_state_s scrut = *s_dst;
    if (scrut.tag == Blake2S_s)
    {
      uint32_t *p_dst = scrut.case_Blake2S_s;
      memcpy(p_dst, p_src, (uint32_t)16U * sizeof (uint32_t));
      return;
    }
    if (scrut.tag == Blake2S_128_s)
    {
      Lib_IntVector_Intrinsics_vec128 *p_dst = scrut.case_Blake2S_128_s;
      #if HACL_CAN_COMPILE_VEC128
      Hacl_Hash_Blake2s_Simd128_load_state128s_from_state32(p_dst, p_src);
      return;
      #else
      return;
      #endif
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  if (scrut0.tag == Blake2B_s)
  {
    uint64_t *p_src = scrut0.case_Blake2B_s;
    EverCrypt_Hash_state_s scrut = *s_dst;
    if (scrut.tag == Blake2B_s)
    {
      uint64_t *p_dst = scrut.case_Blake2B_s;
      memcpy(p_dst, p_src, (uint32_t)16U * sizeof (uint64_t));
      return;
    }
    if (scrut.tag == Blake2B_256_s)
    {
      Lib_IntVector_Intrinsics_vec256 *p_dst = scrut.case_Blake2B_256_s;
      #if HACL_CAN_COMPILE_VEC256
      Hacl_Hash_Blake2b_Simd256_load_state256b_from_state32(p_dst, p_src);
      return;
      #else
      return;
      #endif
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  if (scrut0.tag == Blake2S_128_s)
  {
    Lib_IntVector_Intrinsics_vec128 *p_src = scrut0.case_Blake2S_128_s;
    EverCrypt_Hash_state_s scrut = *s_dst;
    if (scrut.tag == Blake2S_128_s)
    {
      Lib_IntVector_Intrinsics_vec128 *p_dst = scrut.case_Blake2S_128_s;
      memcpy(p_dst, p_src, (uint32_t)4U * sizeof (Lib_IntVector_Intrinsics_vec128));
      return;
    }
    if (scrut.tag == Blake2S_s)
    {
      uint32_t *p_dst = scrut.case_Blake2S_s;
      #if HACL_CAN_COMPILE_VEC128
      Hacl_Hash_Blake2s_Simd128_store_state128s_to_state32(p_dst, p_src);
      return;
      #else
      return;
      #endif
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  if (scrut0.tag == Blake2B_256_s)
  {
    Lib_IntVector_Intrinsics_vec256 *p_src = scrut0.case_Blake2B_256_s;
    EverCrypt_Hash_state_s scrut = *s_dst;
    if (scrut.tag == Blake2B_256_s)
    {
      Lib_IntVector_Intrinsics_vec256 *p_dst = scrut.case_Blake2B_256_s;
      memcpy(p_dst, p_src, (uint32_t)4U * sizeof (Lib_IntVector_Intrinsics_vec256));
      return;
    }
    if (scrut.tag == Blake2B_s)
    {
      uint64_t *p_dst = scrut.case_Blake2B_s;
      #if HACL_CAN_COMPILE_VEC256
      Hacl_Hash_Blake2b_Simd256_store_state256b_to_state32(p_dst, p_src);
      return;
      #else
      return;
      #endif
    }
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
  KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
    __FILE__,
    __LINE__,
    "unreachable (pattern matches are exhaustive in F*)");
  KRML_HOST_EXIT(255U);
}

uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return MD5_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return SHA1_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return SHA2_224_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return SHA2_256_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return SHA2_384_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return SHA2_512_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        return SHA3_224_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        return SHA3_256_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        return SHA3_384_HASH_LEN;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        return SHA3_512_HASH_LEN;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return BLAKE2S_HASH_LEN;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return BLAKE2B_HASH_LEN;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint32_t block_len(Spec_Hash_Definitions_hash_alg a)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        return (uint32_t)128U;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        return (uint32_t)128U;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        return (uint32_t)144U;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        return (uint32_t)136U;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        return (uint32_t)104U;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        return (uint32_t)72U;
      }
    case Spec_Hash_Definitions_Shake128:
      {
        return (uint32_t)168U;
      }
    case Spec_Hash_Definitions_Shake256:
      {
        return (uint32_t)136U;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        return (uint32_t)64U;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        return (uint32_t)128U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/**
Allocate initial state for the agile hash. The argument `a` stands for the
choice of algorithm (see Hacl_Spec.h). This API will automatically pick the most
efficient implementation, provided you have called EverCrypt_AutoConfig2_init()
before. The state is to be freed by calling `free`.
*/
EverCrypt_Hash_Incremental_state_t
*EverCrypt_Hash_Incremental_malloc(Spec_Hash_Definitions_hash_alg a)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), block_len(a));
  uint8_t *buf = (uint8_t *)KRML_HOST_CALLOC(block_len(a), sizeof (uint8_t));
  EverCrypt_Hash_state_s *block_state = create_in(a);
  EverCrypt_Hash_Incremental_state_t
  s = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)(uint32_t)0U };
  EverCrypt_Hash_Incremental_state_t
  *p =
    (EverCrypt_Hash_Incremental_state_t *)KRML_HOST_MALLOC(sizeof (
        EverCrypt_Hash_Incremental_state_t
      ));
  p[0U] = s;
  init(block_state);
  return p;
}

/**
Reset an existing state to the initial hash state with empty data.
*/
void EverCrypt_Hash_Incremental_reset(EverCrypt_Hash_Incremental_state_t *state)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  uint8_t *buf = scrut.buf;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  Spec_Hash_Definitions_hash_alg i = alg_of_state(block_state);
  init(block_state);
  EverCrypt_Hash_Incremental_state_t
  tmp = { .block_state = block_state, .buf = buf, .total_len = (uint64_t)(uint32_t)0U };
  state[0U] = tmp;
}

/**
Feed an arbitrary amount of data into the hash. This function returns
EverCrypt_Error_Success for success, or EverCrypt_Error_MaximumLengthExceeded if
the combined length of all of the data passed to `update` (since the last call
to `init`) exceeds 2^61-1 bytes or 2^64-1 bytes, depending on the choice of
algorithm. Both limits are unlikely to be attained in practice.
*/
EverCrypt_Error_error_code
EverCrypt_Hash_Incremental_update(
  EverCrypt_Hash_Incremental_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
)
{
  EverCrypt_Hash_Incremental_state_t s = *state;
  EverCrypt_Hash_state_s *block_state = s.block_state;
  uint64_t total_len = s.total_len;
  Spec_Hash_Definitions_hash_alg i1 = alg_of_state(block_state);
  uint64_t sw;
  switch (i1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint64_t)2305843009213693951U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint64_t)2305843009213693951U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint64_t)2305843009213693951U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint64_t)2305843009213693951U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_Shake128:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    case Spec_Hash_Definitions_Shake256:
      {
        sw = (uint64_t)18446744073709551615U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  uint32_t ite;
  if ((uint64_t)chunk_len > sw - total_len)
  {
    ite = (uint32_t)1U;
  }
  else
  {
    uint32_t sz;
    if (total_len % (uint64_t)block_len(i1) == (uint64_t)0U && total_len > (uint64_t)0U)
    {
      sz = block_len(i1);
    }
    else
    {
      sz = (uint32_t)(total_len % (uint64_t)block_len(i1));
    }
    if (chunk_len <= block_len(i1) - sz)
    {
      EverCrypt_Hash_Incremental_state_t s1 = *state;
      EverCrypt_Hash_state_s *block_state1 = s1.block_state;
      uint8_t *buf = s1.buf;
      uint64_t total_len1 = s1.total_len;
      Spec_Hash_Definitions_hash_alg i2 = alg_of_state(block_state1);
      uint32_t sz1;
      if (total_len1 % (uint64_t)block_len(i2) == (uint64_t)0U && total_len1 > (uint64_t)0U)
      {
        sz1 = block_len(i2);
      }
      else
      {
        sz1 = (uint32_t)(total_len1 % (uint64_t)block_len(i2));
      }
      uint8_t *buf2 = buf + sz1;
      memcpy(buf2, chunk, chunk_len * sizeof (uint8_t));
      uint64_t total_len2 = total_len1 + (uint64_t)chunk_len;
      *state
      =
        (
          (EverCrypt_Hash_Incremental_state_t){
            .block_state = block_state1,
            .buf = buf,
            .total_len = total_len2
          }
        );
    }
    else if (sz == (uint32_t)0U)
    {
      EverCrypt_Hash_Incremental_state_t s1 = *state;
      EverCrypt_Hash_state_s *block_state1 = s1.block_state;
      uint8_t *buf = s1.buf;
      uint64_t total_len1 = s1.total_len;
      Spec_Hash_Definitions_hash_alg i2 = alg_of_state(block_state1);
      uint32_t sz1;
      if (total_len1 % (uint64_t)block_len(i2) == (uint64_t)0U && total_len1 > (uint64_t)0U)
      {
        sz1 = block_len(i2);
      }
      else
      {
        sz1 = (uint32_t)(total_len1 % (uint64_t)block_len(i2));
      }
      if (!(sz1 == (uint32_t)0U))
      {
        uint64_t prevlen = total_len1 - (uint64_t)sz1;
        update_multi(block_state1, prevlen, buf, block_len(i2));
      }
      uint32_t ite0;
      if
      (
        (uint64_t)chunk_len
        % (uint64_t)block_len(i2)
        == (uint64_t)0U
        && (uint64_t)chunk_len > (uint64_t)0U
      )
      {
        ite0 = block_len(i2);
      }
      else
      {
        ite0 = (uint32_t)((uint64_t)chunk_len % (uint64_t)block_len(i2));
      }
      uint32_t n_blocks = (chunk_len - ite0) / block_len(i2);
      uint32_t data1_len = n_blocks * block_len(i2);
      uint32_t data2_len = chunk_len - data1_len;
      uint8_t *data1 = chunk;
      uint8_t *data2 = chunk + data1_len;
      update_multi(block_state1, total_len1, data1, data1_len);
      uint8_t *dst = buf;
      memcpy(dst, data2, data2_len * sizeof (uint8_t));
      *state
      =
        (
          (EverCrypt_Hash_Incremental_state_t){
            .block_state = block_state1,
            .buf = buf,
            .total_len = total_len1 + (uint64_t)chunk_len
          }
        );
    }
    else
    {
      uint32_t diff = block_len(i1) - sz;
      uint8_t *chunk1 = chunk;
      uint8_t *chunk2 = chunk + diff;
      EverCrypt_Hash_Incremental_state_t s1 = *state;
      EverCrypt_Hash_state_s *block_state10 = s1.block_state;
      uint8_t *buf0 = s1.buf;
      uint64_t total_len10 = s1.total_len;
      Spec_Hash_Definitions_hash_alg i20 = alg_of_state(block_state10);
      uint32_t sz10;
      if (total_len10 % (uint64_t)block_len(i20) == (uint64_t)0U && total_len10 > (uint64_t)0U)
      {
        sz10 = block_len(i20);
      }
      else
      {
        sz10 = (uint32_t)(total_len10 % (uint64_t)block_len(i20));
      }
      uint8_t *buf2 = buf0 + sz10;
      memcpy(buf2, chunk1, diff * sizeof (uint8_t));
      uint64_t total_len2 = total_len10 + (uint64_t)diff;
      *state
      =
        (
          (EverCrypt_Hash_Incremental_state_t){
            .block_state = block_state10,
            .buf = buf0,
            .total_len = total_len2
          }
        );
      EverCrypt_Hash_Incremental_state_t s10 = *state;
      EverCrypt_Hash_state_s *block_state1 = s10.block_state;
      uint8_t *buf = s10.buf;
      uint64_t total_len1 = s10.total_len;
      Spec_Hash_Definitions_hash_alg i2 = alg_of_state(block_state1);
      uint32_t sz1;
      if (total_len1 % (uint64_t)block_len(i2) == (uint64_t)0U && total_len1 > (uint64_t)0U)
      {
        sz1 = block_len(i2);
      }
      else
      {
        sz1 = (uint32_t)(total_len1 % (uint64_t)block_len(i2));
      }
      if (!(sz1 == (uint32_t)0U))
      {
        uint64_t prevlen = total_len1 - (uint64_t)sz1;
        update_multi(block_state1, prevlen, buf, block_len(i2));
      }
      uint32_t ite0;
      if
      (
        (uint64_t)(chunk_len - diff)
        % (uint64_t)block_len(i2)
        == (uint64_t)0U
        && (uint64_t)(chunk_len - diff) > (uint64_t)0U
      )
      {
        ite0 = block_len(i2);
      }
      else
      {
        ite0 = (uint32_t)((uint64_t)(chunk_len - diff) % (uint64_t)block_len(i2));
      }
      uint32_t n_blocks = (chunk_len - diff - ite0) / block_len(i2);
      uint32_t data1_len = n_blocks * block_len(i2);
      uint32_t data2_len = chunk_len - diff - data1_len;
      uint8_t *data1 = chunk2;
      uint8_t *data2 = chunk2 + data1_len;
      update_multi(block_state1, total_len1, data1, data1_len);
      uint8_t *dst = buf;
      memcpy(dst, data2, data2_len * sizeof (uint8_t));
      *state
      =
        (
          (EverCrypt_Hash_Incremental_state_t){
            .block_state = block_state1,
            .buf = buf,
            .total_len = total_len1 + (uint64_t)(chunk_len - diff)
          }
        );
    }
    ite = (uint32_t)0U;
  }
  switch (ite)
  {
    case 0U:
      {
        return EverCrypt_Error_Success;
      }
    case 1U:
      {
        return EverCrypt_Error_MaximumLengthExceeded;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static void digest_md5(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_MD5)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_MD5);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_MD5));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[4U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = MD5_s, { .case_MD5_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_MD5) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_MD5);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_MD5);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha1(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA1)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA1);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA1));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[5U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA1_s, { .case_SHA1_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA1) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA1);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA1);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha224(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_224)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA2_224);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_224));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA2_224_s, { .case_SHA2_224_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA2_224) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA2_224);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA2_224);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha256(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_256)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA2_256);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_256));
  }
  uint8_t *buf_1 = buf_;
  uint32_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA2_256_s, { .case_SHA2_256_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA2_256) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA2_256);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA2_256);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha3_224(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_224)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA3_224);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_224));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[25U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA3_224_s, { .case_SHA3_224_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA3_224) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA3_224);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA3_224);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha3_256(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_256)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA3_256);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_256));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[25U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA3_256_s, { .case_SHA3_256_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA3_256) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA3_256);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA3_256);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha3_384(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_384)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA3_384);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_384));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[25U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA3_384_s, { .case_SHA3_384_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA3_384) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA3_384);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA3_384);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha3_512(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_512)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA3_512);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA3_512));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[25U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA3_512_s, { .case_SHA3_512_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA3_512) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA3_512);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA3_512);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha384(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_384)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA2_384);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_384));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA2_384_s, { .case_SHA2_384_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA2_384) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA2_384);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA2_384);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_sha512(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_512)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_SHA2_512);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_SHA2_512));
  }
  uint8_t *buf_1 = buf_;
  uint64_t buf[8U] = { 0U };
  EverCrypt_Hash_state_s s = { .tag = SHA2_512_s, { .case_SHA2_512_s = buf } };
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_SHA2_512) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_SHA2_512);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_SHA2_512);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_blake2s(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_Blake2S)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_Blake2S);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_Blake2S));
  }
  uint8_t *buf_1 = buf_;
  bool vec128 = EverCrypt_AutoConfig2_has_vec128();
  EverCrypt_Hash_state_s s;
  #if HACL_CAN_COMPILE_VEC128
  KRML_PRE_ALIGN(16) Lib_IntVector_Intrinsics_vec128 buf0[4U] KRML_POST_ALIGN(16) = { 0U };
  uint32_t buf[16U] = { 0U };
  if (vec128)
  {
    s = ((EverCrypt_Hash_state_s){ .tag = Blake2S_128_s, { .case_Blake2S_128_s = buf0 } });
  }
  else
  {
    s = ((EverCrypt_Hash_state_s){ .tag = Blake2S_s, { .case_Blake2S_s = buf } });
  }
  #else
  uint32_t buf[16U] = { 0U };
  s = ((EverCrypt_Hash_state_s){ .tag = Blake2S_s, { .case_Blake2S_s = buf } });
  #endif
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_Blake2S) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_Blake2S);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_Blake2S);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

static void digest_blake2b(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  uint8_t *buf_ = scrut.buf;
  uint64_t total_len = scrut.total_len;
  uint32_t r;
  if
  (
    total_len
    % (uint64_t)block_len(Spec_Hash_Definitions_Blake2B)
    == (uint64_t)0U
    && total_len > (uint64_t)0U
  )
  {
    r = block_len(Spec_Hash_Definitions_Blake2B);
  }
  else
  {
    r = (uint32_t)(total_len % (uint64_t)block_len(Spec_Hash_Definitions_Blake2B));
  }
  uint8_t *buf_1 = buf_;
  bool vec256 = EverCrypt_AutoConfig2_has_vec256();
  EverCrypt_Hash_state_s s;
  #if HACL_CAN_COMPILE_VEC256
  KRML_PRE_ALIGN(32) Lib_IntVector_Intrinsics_vec256 buf0[4U] KRML_POST_ALIGN(32) = { 0U };
  uint64_t buf[16U] = { 0U };
  if (vec256)
  {
    s = ((EverCrypt_Hash_state_s){ .tag = Blake2B_256_s, { .case_Blake2B_256_s = buf0 } });
  }
  else
  {
    s = ((EverCrypt_Hash_state_s){ .tag = Blake2B_s, { .case_Blake2B_s = buf } });
  }
  #else
  uint64_t buf[16U] = { 0U };
  s = ((EverCrypt_Hash_state_s){ .tag = Blake2B_s, { .case_Blake2B_s = buf } });
  #endif
  EverCrypt_Hash_state_s tmp_block_state = s;
  copy(block_state, &tmp_block_state);
  uint64_t prev_len = total_len - (uint64_t)r;
  uint32_t ite;
  if (r % block_len(Spec_Hash_Definitions_Blake2B) == (uint32_t)0U && r > (uint32_t)0U)
  {
    ite = block_len(Spec_Hash_Definitions_Blake2B);
  }
  else
  {
    ite = r % block_len(Spec_Hash_Definitions_Blake2B);
  }
  uint8_t *buf_last = buf_1 + r - ite;
  uint8_t *buf_multi = buf_1;
  update_multi(&tmp_block_state, prev_len, buf_multi, (uint32_t)0U);
  uint64_t prev_len_last = total_len - (uint64_t)r;
  update_last(&tmp_block_state, prev_len_last, buf_last, r);
  finish(&tmp_block_state, output);
}

/**
Perform a run-time test to determine which algorithm was chosen for the given piece of state.
*/
Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(EverCrypt_Hash_Incremental_state_t *s)
{
  EverCrypt_Hash_Incremental_state_t scrut = *s;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  return alg_of_state(block_state);
}

/**
Write the resulting hash into `output`, an array whose length is
algorithm-specific. You can use the macros defined earlier in this file to
allocate a destination buffer of the right length. The state remains valid after
a call to `digest`, meaning the user may feed more data into the hash via
`update`. (The finish function operates on an internal copy of the state and
therefore does not invalidate the client-held state.)
*/
void
EverCrypt_Hash_Incremental_digest(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output)
{
  Spec_Hash_Definitions_hash_alg a1 = EverCrypt_Hash_Incremental_alg_of_state(state);
  switch (a1)
  {
    case Spec_Hash_Definitions_MD5:
      {
        digest_md5(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        digest_sha1(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        digest_sha224(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        digest_sha256(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        digest_sha384(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        digest_sha512(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        digest_sha3_224(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        digest_sha3_256(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        digest_sha3_384(state, output);
        break;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        digest_sha3_512(state, output);
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        digest_blake2s(state, output);
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        digest_blake2b(state, output);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

/**
Free a state previously allocated with `create_in`.
*/
void EverCrypt_Hash_Incremental_free(EverCrypt_Hash_Incremental_state_t *state)
{
  EverCrypt_Hash_Incremental_state_t scrut = *state;
  uint8_t *buf = scrut.buf;
  EverCrypt_Hash_state_s *block_state = scrut.block_state;
  free_(block_state);
  KRML_HOST_FREE(buf);
  KRML_HOST_FREE(state);
}

void EverCrypt_Hash_Incremental_hash_256(uint8_t *output, uint8_t *input, uint32_t input_len)
{
  uint32_t
  s[8U] =
    {
      (uint32_t)0x6a09e667U, (uint32_t)0xbb67ae85U, (uint32_t)0x3c6ef372U, (uint32_t)0xa54ff53aU,
      (uint32_t)0x510e527fU, (uint32_t)0x9b05688cU, (uint32_t)0x1f83d9abU, (uint32_t)0x5be0cd19U
    };
  uint32_t blocks_n0 = input_len / (uint32_t)64U;
  uint32_t blocks_n1;
  if (input_len % (uint32_t)64U == (uint32_t)0U && blocks_n0 > (uint32_t)0U)
  {
    blocks_n1 = blocks_n0 - (uint32_t)1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * (uint32_t)64U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_256(s, output);
}

static void hash_224(uint8_t *output, uint8_t *input, uint32_t input_len)
{
  uint32_t
  s[8U] =
    {
      (uint32_t)0xc1059ed8U, (uint32_t)0x367cd507U, (uint32_t)0x3070dd17U, (uint32_t)0xf70e5939U,
      (uint32_t)0xffc00b31U, (uint32_t)0x68581511U, (uint32_t)0x64f98fa7U, (uint32_t)0xbefa4fa4U
    };
  uint32_t blocks_n0 = input_len / (uint32_t)64U;
  uint32_t blocks_n1;
  if (input_len % (uint32_t)64U == (uint32_t)0U && blocks_n0 > (uint32_t)0U)
  {
    blocks_n1 = blocks_n0 - (uint32_t)1U;
  }
  else
  {
    blocks_n1 = blocks_n0;
  }
  uint32_t blocks_len0 = blocks_n1 * (uint32_t)64U;
  uint8_t *blocks0 = input;
  uint32_t rest_len0 = input_len - blocks_len0;
  uint8_t *rest0 = input + blocks_len0;
  uint32_t blocks_n = blocks_n1;
  uint32_t blocks_len = blocks_len0;
  uint8_t *blocks = blocks0;
  uint32_t rest_len = rest_len0;
  uint8_t *rest = rest0;
  EverCrypt_Hash_update_multi_256(s, blocks, blocks_n);
  EverCrypt_Hash_update_last_256(s, (uint64_t)blocks_len, rest, rest_len);
  Hacl_Hash_Core_SHA2_finish_224(s, output);
}

/**
Hash `input`, of len `input_len`, into `output`, an array whose length is determined by
your choice of algorithm `a` (see Hacl_Spec.h). You can use the macros defined
earlier in this file to allocate a destination buffer of the right length. This
API will automatically pick the most efficient implementation, provided you have
called EverCrypt_AutoConfig2_init() before. 
*/
void
EverCrypt_Hash_Incremental_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len
)
{
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        Hacl_Hash_MD5_hash_oneshot(output, input, input_len);
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        Hacl_Hash_SHA1_hash_oneshot(output, input, input_len);
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        hash_224(output, input, input_len);
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        EverCrypt_Hash_Incremental_hash_256(output, input, input_len);
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        Hacl_Hash_SHA2_hash_384(output, input, input_len);
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        Hacl_Hash_SHA2_hash_512(output, input, input_len);
        break;
      }
    case Spec_Hash_Definitions_SHA3_224:
      {
        Hacl_SHA3_sha3_224(input_len, input, output);
        break;
      }
    case Spec_Hash_Definitions_SHA3_256:
      {
        Hacl_SHA3_sha3_256(input_len, input, output);
        break;
      }
    case Spec_Hash_Definitions_SHA3_384:
      {
        Hacl_SHA3_sha3_384(input_len, input, output);
        break;
      }
    case Spec_Hash_Definitions_SHA3_512:
      {
        Hacl_SHA3_sha3_512(input_len, input, output);
        break;
      }
    case Spec_Hash_Definitions_Blake2S:
      {
        bool vec128 = EverCrypt_AutoConfig2_has_vec128();
        #if HACL_CAN_COMPILE_VEC128
        if (vec128)
        {
          Hacl_Hash_Blake2s_Simd128_hash_with_key(output,
            (uint32_t)32U,
            input,
            input_len,
            NULL,
            (uint32_t)0U);
          return;
        }
        #endif
        Hacl_Hash_Blake2s_hash_with_key(output,
          (uint32_t)32U,
          input,
          input_len,
          NULL,
          (uint32_t)0U);
        break;
      }
    case Spec_Hash_Definitions_Blake2B:
      {
        bool vec256 = EverCrypt_AutoConfig2_has_vec256();
        #if HACL_CAN_COMPILE_VEC256
        if (vec256)
        {
          Hacl_Hash_Blake2b_Simd256_hash_with_key(output,
            (uint32_t)64U,
            input,
            input_len,
            NULL,
            (uint32_t)0U);
          return;
        }
        #endif
        Hacl_Hash_Blake2b_hash_with_key(output,
          (uint32_t)64U,
          input,
          input_len,
          NULL,
          (uint32_t)0U);
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

