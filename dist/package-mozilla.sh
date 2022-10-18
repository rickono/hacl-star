#!/bin/bash

set -o pipefail
set -e

FILES=" \
  Hacl_Bignum25519_51 \
  Hacl_Chacha20 \
  Hacl_Chacha20Poly1305_128 \
  Hacl_Chacha20Poly1305_256 \
  Hacl_Chacha20Poly1305_32 \
  Hacl_Chacha20_Vec128 \
  Hacl_Chacha20_Vec256 \
  Hacl_Curve25519_51 \
  Hacl_Curve25519_64 \
  Hacl_Hash_SHA1 \
  Hacl_IntTypes_Intrinsics \
  Hacl_IntTypes_Intrinsics_128 \
  Hacl_Krmllib \
  Hacl_Lib \
  Hacl_Poly1305_128 \
  Hacl_Poly1305_256 \
  Hacl_Poly1305_32 \
  Hacl_SHA3 \
  Hacl_Streaming_SHA1 \
  Lib_Memzero0 \
  TestLib \
  Vale \
  curve25519-inline \
  curve25519-x86_64-darwin \
  curve25519-x86_64-linux \
  curve25519-x86_64-mingw \
  curve25519-x86_64-msvc \
  libintvector"

mkdir -p mozilla/internal
cp Makefile.mozilla.config mozilla/Makefile.config
cp config.mozilla.h mozilla/config.h
cp gcc-compatible/Makefile mozilla/
cp gcc-compatible/Makefile.basic mozilla/
cp gcc-compatible/Hacl_Streaming_SHA2.h mozilla/
cp gcc-compatible/Hacl_Hash_SHA2.h mozilla/
for f in $FILES; do
  [ -f gcc-compatible/$f.h ] && cp gcc-compatible/$f.h mozilla/ || true
  [ -f gcc-compatible/$f.c ] && cp gcc-compatible/$f.c mozilla/ || true
  [ -f gcc-compatible/internal/$f.h ] && cp gcc-compatible/internal/$f.h mozilla/internal || true
done

cat <<EOF > mozilla/Makefile.include
USER_TARGET=libevercrypt.a
USER_CFLAGS=-Wno-unused
USER_C_FILES=Lib_Memzero0.c
ALL_C_FILES=$(ls mozilla/*.c | xargs basename -a | xargs echo)
ALL_H_FILES=$(ls mozilla/*.h | xargs basename -a | xargs echo)
EOF

cat <<EOF > mozilla/evercrypt_targetconfig.h
#include "config.h"
EOF
