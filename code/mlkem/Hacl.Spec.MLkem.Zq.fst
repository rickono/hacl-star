module Hacl.Spec.MLkem.Zq
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod
open FStar.Math.Euclid
open Hacl.Spec.MLkem.Sums

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let nonzero_size_nat = x:size_nat{x > 0}
let n: nonzero_size_nat = 256
let q: x:nat{is_prime x} = 7681
let m: int = (pow2 32) / q
let zq = nat_mod q

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

let sum_of_zqs = sum_of_modint #q

let rewrite_sum_of_zqs_lemma (start stop:int) (f g:int -> zq): Lemma
    (requires (forall (i:int).{:pattern (f i)} start <= i /\ i < stop ==> f i == g i))
    (ensures (sum_of_zqs start stop f) == (sum_of_zqs start stop g))
    [SMTPat (sum_of_zqs start stop f)]
= sum_rewrite_lemma #q start stop f g

let lemma_sum_none_zq (start:int) (f:int -> zq) : Lemma
  (0 == (sum_of_zqs start start f))
  [SMTPat (sum_of_zqs start start f)]
  =
  lemma_sum_none #q start f

let sum_mul_lemma_zq (a:zq) (start stop:int) (f:int -> zq): Lemma
    (ensures a %* (sum_of_zqs start stop f) == sum_of_zqs start stop (fun i -> a %* (f i)))
    [SMTPat (sum_of_modint #m start stop (fun i -> a %* (f i)))]
= sum_mul_lemma #q a start stop f;
  assert (a %* (sum_of_zqs start stop f) == sum_of_zqs start stop (fun i -> a `mul_mod #q` (f i)));
  let aux (i:int): Lemma (a `mul_mod #q` (f i) == a %* (f i)) = () in
  Classical.forall_intro aux;
  rewrite_sum_of_zqs_lemma start stop (fun i -> a `mul_mod #q` (f i)) (fun i -> a %* (f i));
  calc (==) {
    a %* (sum_of_zqs start stop f);
    (==) {}
    sum_of_zqs start stop (fun i -> a `mul_mod #q` (f i));
    (==) {}
    sum_of_zqs start stop (fun i -> a %* (f i));
  }