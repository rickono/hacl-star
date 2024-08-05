module Hacl.Spec.MLkem.Zq
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod
open FStar.Math.Euclid

open Hacl.Spec.MLkem.Unity

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let nonzero_size_nat = x:size_nat{x > 0}
// let n: nonzero_size_nat = 256
let q: x:nat{is_prime x} = 7681
// let m: int = (pow2 32) / q
let zq = nat_mod q

// root is a root of unity mod m if: root^n = 1 mod m
let test_root_of_unity (#m:prime) (#n:nat) (root:nat_mod m): bool =
  (pow root n) % m = 1 && root <> 0

// Returns true if there is no smaller exponent satisfying the property
let rec test_primitive (#m:prime) (#n:pos) (root:nat_mod m): bool =
  if n = 1 then
    true
  else
    test_primitive #m #(n-1) root && ((pow root (n-1) % m) <> 1)

// root is a primitive root of unity mod m if root^n = 1 mod m and there are no integers < root l where root^l = 1 mod m
let test_primitive_root_of_unity (#m:prime) (#n:nat{n > 0}) (root:nat_mod m): bool = 
  test_root_of_unity #m #n root && test_primitive #m #n root

#reset-options "--z3rlimit 50 --fuel 2 --ifuel 2 --split_queries always"
// Proof that primitive is a valid test for primitive, that is 
//      test_primitive #m #n root ==> is_primitive #m #n root
let rec lemma_primitive_ok (#m:prime{m > 2}) (#n:nat{n > 0}) (root:nat_mod m):
  Lemma (requires test_primitive #m #n root)
        (ensures is_primitive #m #n root)
= if n > 1 then 
    let minus_one:pos = n - 1 in
    assert (test_primitive #m #(n-1) root && (pow root (n-1) % m <> 1));
    lemma_primitive_ok #m #(n-1) root;
    lemma_pow_mod #m root (n-1)

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"
// Proof that we have a valid test for primitive root of unity, that is 
//      test_primitive_root_of_unity #m #n root ==> is_primitive_nth_root_of_unity_mod #m #n root
let lemma_test_primitive_root_of_unity_ok (#m:prime{m > 2}) (#n:nat{n > 0}) (root:nat_mod m): 
  Lemma (requires test_primitive_root_of_unity #m #n root)
        (ensures is_primitive_nth_root_of_unity_mod #m n root)
  = 
    lemma_pow_mod #m root n;
    assert (is_nth_root_of_unity_mod #m n root);
    lemma_primitive_ok #m #n root


// Use the test and the lemma to prove that 62 is a 512th root of unity mod 7681
#reset-options "--z3rlimit 50 --fuel 2 --ifuel 2 --split_queries always --query_stats"
let root_of_unity_kyber: primitive_nth_root_of_unity_mod #q 512 =
  assert_norm (test_primitive_root_of_unity #q #512 62);
  lemma_test_primitive_root_of_unity_ok #q #512 62;
  62

let root_of_unity_256: primitive_nth_root_of_unity_mod #q 256 =
  let omega = pow_mod root_of_unity_kyber 2 in
  nth_root_squared_is_primitive_root #q 512 root_of_unity_kyber;
  omega

let root_of_unity_128: primitive_nth_root_of_unity_mod #q 128 =
  let omega = pow_mod root_of_unity_256 2 in
  nth_root_squared_is_primitive_root #q 256 root_of_unity_256;
  omega

let root_of_unity_64: primitive_nth_root_of_unity_mod #q 64 =
  let omega = pow_mod root_of_unity_128 2 in
  nth_root_squared_is_primitive_root #q 128 root_of_unity_128;
  omega

let root_of_unity_32: primitive_nth_root_of_unity_mod #q 32 =
  let omega = pow_mod root_of_unity_64 2 in
  nth_root_squared_is_primitive_root #q 64 root_of_unity_64;
  omega

let root_of_unity_16: primitive_nth_root_of_unity_mod #q 16 =
  let omega = pow_mod root_of_unity_32 2 in
  nth_root_squared_is_primitive_root #q 32 root_of_unity_32;
  omega

let root_of_unity_8: primitive_nth_root_of_unity_mod #q 8 =
  let omega = pow_mod root_of_unity_16 2 in
  nth_root_squared_is_primitive_root #q 16 root_of_unity_16;
  omega

let root_of_unity_4: primitive_nth_root_of_unity_mod #q 4 =
  let omega = pow_mod root_of_unity_8 2 in
  nth_root_squared_is_primitive_root #q 8 root_of_unity_8;
  omega

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"
val int_to_zq: x:int -> zq
let int_to_zq x = x % q

val add_zq: a:zq -> b:zq -> zq
let add_zq a b = add_mod #q a b

val mul_zq: a:zq -> b:zq -> zq
let mul_zq a b = mul_mod #q a b

val neg_zq: a:zq -> zq
let neg_zq a = 
  if a = 0 then 0
  else q - a

val sub_zq: a:zq -> b:zq -> zq
let sub_zq a b = sub_mod #q a b

unfold
let (+%) = add_zq

unfold
let (-%) = sub_zq

unfold
let (%*) = mul_zq

val lemma_add_zq_assoc: a:zq -> b:zq -> c:zq -> 
  Lemma ((a +% b) +% c = a +% (b +% c))
  [SMTPat ((a +% b) +% c); SMTPat (a +% (b +% c))]
let lemma_add_zq_assoc a b c = 
  lemma_add_mod_assoc #q a b c

val lemma_add_zq_comm: a:zq -> b:zq -> 
  Lemma (a +% b = b +% a)
  [SMTPat (a +% b); SMTPat (b +% a)]
let lemma_add_zq_comm a b =
  lemma_add_mod_comm #q a b

val lemma_mul_zq_assoc: a:zq -> b:zq -> c:zq -> 
  Lemma ((a %* b) %* c = a %* (b %* c))
  [SMTPat ((a %* b) %* c); SMTPat (a %* (b %* c))]
let lemma_mul_zq_assoc a b c =
  lemma_mul_mod_assoc #q a b c

val lemma_mul_zq_comm: a:zq -> b:zq ->
  Lemma (a %* b = b %* a)
  [SMTPat (a %* b); SMTPat (b %* a)]
let lemma_mul_zq_comm a b =
  lemma_mul_mod_comm #q a b

val lemma_mul_zq_id: a:zq -> 
  Lemma (a %* 1 = a)
  [SMTPat (a %* 1)]
let lemma_mul_zq_id a = ()