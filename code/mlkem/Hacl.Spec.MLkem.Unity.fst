module Hacl.Spec.MLkem.Unity

open FStar.Mul
open Lib.NatMod
module Fermat = FStar.Math.Fermat
open FStar.Math.Lemmas
module Euclid = FStar.Math.Euclid
open Hacl.Spec.MLkem.PowModInt 

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"

let is_nth_root_of_unity_mod (#m:prime{m > 2}) (n:nat{n > 0}) (root:nat_mod m) = pow_mod #m root n == 1 /\ root % m <> 0
let nth_root_of_unity_mod (#m:prime{m > 2}) (n:nat{n > 0}) = root:nat_mod m{is_nth_root_of_unity_mod #m n root}
let is_primitive (#m:prime{m > 2}) (#n:nat{n > 0}) (a:nat_mod m) = 
  (forall (k:nat{k < n}). pow_mod #m a k <> 1)
let is_primitive_nth_root_of_unity_mod (#m:prime{m > 2}) (n:nat{n > 0}) (root:nat_mod m) = is_nth_root_of_unity_mod #m n root /\ is_primitive #m #n root
let primitive_nth_root_of_unity_mod (#m:prime{m > 2}) (n:nat{n > 0}) = root:nat_mod m{is_primitive_nth_root_of_unity_mod #m n root}

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
  lemma_unit_roots #m (pow_mod_int #m a k);
  assert (pow_mod_int #m a k == (1 % m) \/ pow_mod_int #m a k == ((-1) % m))

let distributivity_nth_root (m: prime{m > 2}) (k r:nat): 
  Lemma ((k * m + r) * (k * m + r) == (k * k * m * m) + (2 * (k * m * r)) + (r * r))
= 
  calc (==) {
    (k * m + r) * (k * m + r);
    (==) {distributivity_add_left (k * m) r (k * m + r)}
    (((k * m) * (k * m + r)) + (r * (k * m + r)));
    (==) {distributivity_add_right (k * m) (k * m) r}
    (((((k * m) * (k * m)) + ((k * m) * r))) + (r * (k * m + r)));
    (==) {distributivity_add_right r (k * m) r}
    ((((k * m * (k * m)) + (k * m * r))) + (r * (k * m) + r * r));
    (==) {paren_mul_right (k * m) k m}
    (((k * m * k * m) + (k * m * r)) + (r * (k * m) + r * r));
    (==) {paren_mul_right r k m}
    ((k * m * k * m) + (k * m * r) + (r * k * m + r * r));
    (==) {paren_add_right ((k * m * k * m) + (k * m * r)) (r * k * m) (r * r)}
    ((k * m * k * m) + (k * m * r) + r * k * m + r * r);
    (==) {paren_mul_right r k m}
    ((k * m * k * m) + (k * m * r) + (r * (k * m)) + r * r);
    (==) {swap_mul r (k * m)}
    ((k * m * k * m) + (k * m * r) + (k * m * r) + r * r);
    (==) {}
    ((k * m * k * m) + 2 * (k * m * r) + r * r);
  }

let distributivity_nth_root_mod (m: prime{m > 2}) (a b c:nat): 
  Lemma ((a + b + c) % m == ((a % m + b % m + c % m) % m))
= 
  calc (==) {
    (a + b + c) % m;
    (==) {modulo_distributivity (a + b) c m}
    ((a + b) % m + c % m) % m;
    (==) {modulo_distributivity a b m}
    ((a % m + b % m) % m + c % m) % m;
    (==) {lemma_mod_plus_distr_l (a % m + b % m) (c % m) m}
    ((a % m + b % m) + c % m) % m;
  }

let nth_root_squared_is_root_rewrite (#m:prime{m > 2}) (n:nat{n > 0}) (root:nat_mod m): 
  Lemma 
    (requires n >= 2 /\ n % 2 == 0 /\ is_nth_root_of_unity_mod #m n root)
    (ensures pow_mod #m root 2 == (root % m) * (root % m) % m)
= 
  let k = root / m in 
  let r = root % m in
  assert (root = k * m + r);
  calc (==) {
    pow_mod #m (k * m + r) 2;
    (==) {lemma_pow_mod #m (k * m + r) 2}
    pow (k * m + r) 2 % m;
    (==) {lemma_pow_unfold (k * m + r) 2}
    (k * m + r) * (pow (k * m + r) 1) % m;
    (==) {lemma_pow1 (k * m + r)}
    (k * m + r) * (k * m + r) % m;
    (==) {distributivity_nth_root m k r}
    ((k * k * m * m) + (2 * (k * m * r)) + (r * r)) % m;
    (==) {distributivity_nth_root_mod m (k * k * m * m) (2 * (k * m * r)) (r * r)}
    ((k * k * m * m) % m + (2 * (k * m * r) % m) + (r * r % m)) % m;
    (==) {multiple_modulo_lemma (k * k * m) m}
    (0 + (2 * (k * m * r) % m) + (r * r % m)) % m;
    (==) {multiple_modulo_lemma (2 * (k * r)) m}
    (0 + 0 + (r * r % m)) % m;
    (==) {} 
    (r * r % m) % m;
    (==) {lemma_mod_twice (r * r) m}
    r * r % m;
  }

let nth_root_squared_is_root' (#m:prime{m > 2}) (n:nat{n > 0}) (root:nat_mod m): 
  Lemma 
    (requires n >= 2 /\ n % 2 == 0 /\ is_nth_root_of_unity_mod #m n root)
    (ensures pow_mod #m root 2 <> 0)
= 
  let k = root / m in 
  let r = root % m in
  calc (==) {
    pow_mod #m root 2;
    (==) {nth_root_squared_is_root_rewrite #m n root}
    (r * r % m);
  };
  // Contradiction: if r * r % m = 0, then it would mean that r % m = 0
  if ((r * r) % m = 0) then begin
    Euclid.euclid_prime m r r;
    assert (False)
  end

let nth_root_squared_is_root (#m:prime{m > 2}) (n:nat{n > 0}) (root:nat_mod m): 
  Lemma 
    (requires n >= 2 /\ n % 2 == 0 /\ is_nth_root_of_unity_mod #m n root)
    (ensures is_nth_root_of_unity_mod #m (n/2) (pow_mod #m root 2))
= 
  let omega = pow_mod #m root 2 in
  calc (==) {
    pow_mod #m omega (n / 2);
    (==) {lemma_pow_mod_int_mul #m root 2 (n / 2)}
    pow_mod #m root n;
    (==) {}
    1;
  };
  nth_root_squared_is_root' #m n root

let nth_root_squared_is_primitive_root_aux (#m:prime{m > 2}) (n:nat{n > 0}) (root:nat_mod m) (k:nat{k < n/2}):
  Lemma 
    (requires n >= 2 /\ n % 2 == 0 /\ is_primitive_nth_root_of_unity_mod #m n root)
    (ensures pow_mod #m (pow_mod #m root 2) k <> 1)
= 
  let omega = pow_mod #m root 2 in
  if pow_mod #m omega k = 1 then begin 
    calc (==) {
      pow_mod #m omega k;
      (==) {}
      pow_mod #m (pow_mod #m root 2) k;
      (==) {lemma_pow_mod_int_mul #m root 2 k}
      pow_mod #m root (2 * k);
    };
    assert (False)
  end

let nth_root_squared_is_primitive_root (#m:prime{m > 2}) (n:nat{n > 0}) (root:nat_mod m): 
  Lemma 
    (requires n >= 2 /\ n % 2 == 0 /\ is_primitive_nth_root_of_unity_mod #m n root)
    (ensures is_primitive_nth_root_of_unity_mod #m (n/2) (pow_mod #m root 2))
=
  let omega = pow_mod #m root 2 in
  nth_root_squared_is_root #m n root;
  assert (forall (k:nat{k < n}). pow_mod #m root k <> 1);
  Classical.forall_intro (Classical.move_requires (nth_root_squared_is_primitive_root_aux #m n root))