module Hacl.Spec.MLkem.Unity

open FStar.Mul
open Lib.NatMod
module Fermat = FStar.Math.Fermat
open FStar.Math.Lemmas
module Euclid = FStar.Math.Euclid
open Hacl.Spec.MLkem.PowModInt 

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let nth_root_of_unity_mod (#m:prime{m > 2}) (n:nat{n > 0}) = root:nat_mod m{pow_mod #m root n = 1 && root % m <> 0}
let is_primitive (#m:prime{m > 2}) (#n:nat{n > 0}) (a:nth_root_of_unity_mod #m n) = 
  (forall (k:nat{k < n}). pow_mod #m a k <> 1)
let primitive_nth_root_of_unity_mod (#m:prime{m > 2}) (n:nat{n > 0}) = root:nth_root_of_unity_mod #m n{is_primitive #m #n root}

#reset-options "--z3rlimit 10 --fuel 1 --ifuel 0"
val lemma_unity_pow_reduce:
    #m:prime{m > 2}
  -> #n:nat{n > 0}
  -> a:nth_root_of_unity_mod #m n
  -> b:int
  -> Lemma (pow_mod_int #m a b == pow_mod_int #m a (b % n))
let lemma_unity_pow_reduce #m #n a b =
  let k:int = b / n in
  assert (b == k * n + (b % n));
  calc (==) {
    pow_mod_int #m a b;
    (==) {}
    pow_mod_int #m a (k * n + (b % n));
    (==) {lemma_pow_mod_int_add #m a (k * n) (b % n)}
    pow_mod_int #m a (n * k) * pow_mod_int #m a (b % n) % m;
    (==) {lemma_pow_mod_int_mul #m a n k}
    pow_mod_int #m (pow_mod_int #m a n) k * pow_mod_int #m a (b % n) % m;
    (==) {}
    pow_mod_int #m (1) k  * pow_mod_int #m a (b % n) % m;
    (==) {lemma_pow_mod_int_one #m k}
    1 * pow_mod_int #m a (b % n) % m;
    (==) {}
    pow_mod_int #m a (b % n) % m;
    (==) {small_mod (pow_mod_int #m a (b % n)) m}
    pow_mod_int #m a (b % n);
  }

val lemma_unit_roots_:
    #m:prime{m > 2}
  -> x:nat_mod m
  -> Lemma (pow_mod_int #m x 2 == 1 ==> (pow_mod_int #m x 2 - 1) % m == 0)
let lemma_unit_roots_ #m x = ()

val lemma_unit_roots_1:
    #m:prime{m > 2}
  -> x:nat_mod m
  -> Lemma (((x * x % m) - 1) % m == (x * x - 1) % m)
let lemma_unit_roots_1 #m x = 
  calc (==) {
    ((x * x % m) - 1) % m;
    (==) {}
    ((-1) + (x * x % m)) % m;
    (==) {lemma_mod_add_distr (-1) (x * x) m}
    ((-1) + (x * x)) % m;
  }

val lemma_unit_roots_2:
    #m:prime{m > 2}
  -> x:nat_mod m
  -> Lemma ((x * x - 1) == (x - 1) * (x + 1))
let lemma_unit_roots_2 #m x =
  calc (==) {
    (x - 1) * (x + 1);
    (==) {distributivity_add_right (x - 1) x 1}
    (x - 1) * x + (x - 1);
    (==) {distributivity_add_left x 1 x}
    x * x + (-x) + x - 1;
  }

val lemma_unit_roots:
    #m:prime{m > 2}
  -> x:nat_mod m
  -> Lemma (pow_mod_int #m x 2 == 1 ==> x == (1 % m) \/ x == ((-1) % m))
let lemma_unit_roots #m x =
  calc (==>) {
    pow_mod_int #m x 2 == 1;
    (==>) {lemma_unit_roots_ #m x}
    ((pow_mod_int #m x 2) - 1) % m == 0;
    (==>) {lemma_pow_mod x 2}
    ((pow x 2 % m) - 1) % m == 0;
    (==>) {lemma_pow_unfold x 2; lemma_pow1 x}
    ((x * x % m) - 1) % m == 0;
    (==>) {lemma_unit_roots_1 #m x}
    ((x * x - 1) % m) == 0;
    (==>) {lemma_unit_roots_2 #m x}
    ((x - 1) * (x + 1) % m) == 0;
    // (==>) {Euclid.mod_divides ((x - 1) * (x + 1)) m}
    // (Euclid.divides m ((x - 1) * (x + 1)));
    (==>) {Euclid.euclid_prime m (x - 1) (x + 1)}
    (x - 1) % m == 0 \/ (x + 1) % m == 0;
    (==>) {}
    (x == 1 % m) \/ (x == (-1) % m);
  }

val lemma_primitive_unity_half_n:
    #m:prime{m > 2}
  -> #n:nat{n > 0}
  -> a:primitive_nth_root_of_unity_mod #m n
  -> Lemma (requires n % 2 == 0) (ensures pow_mod_int #m a (n / 2) == (-1) % m) 
let lemma_primitive_unity_half_n #m #n a = 
  let k = n / 2 in
  let lhs = pow_mod_int #m a (n / 2) in
  calc (==) {
    1; 
    (==) {}
    pow_mod_int #m a (n);
    (==) {}
    pow_mod_int #m a (k * 2);
    (==) {lemma_pow_mod_int_mul #m a k 2}
    pow_mod_int #m (pow_mod_int #m a k) 2;
  };
  // Need some lemma to say x^2 = 1 ==> x = -1 or 1
  lemma_unit_roots #m (pow_mod_int #m a k);
  assert (pow_mod_int #m a k == (1 % m) \/ pow_mod_int #m a k == ((-1) % m))