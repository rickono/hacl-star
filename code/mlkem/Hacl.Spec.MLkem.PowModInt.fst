module Hacl.Spec.MLkem.PowModInt
open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.NatMod
module Fermat = FStar.Math.Fermat
open FStar.Math.Lemmas
open Hacl.Spec.MLkem.Zq
module Euclid = FStar.Math.Euclid
open Hacl.Spec.MLkem.Zq

#reset-options "--z3rlimit 10 --fuel 0 --ifuel 0"
val pow_mod_int: 
    #(m:prime) 
  -> (a:nat_mod m) 
  -> (b:int)
  -> nat_mod m
let pow_mod_int #m a b =
  if b >= 0 then 
    pow_mod #m a b
  else 
    pow_mod #m a ((-b) * (m - 2))

val neg_sign_swap:
    a:int{a < 0} -> Lemma ((-a) > 0)
let neg_sign_swap a = ()

#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
val lemma_pow_mod_int_zero:
    #m:prime
  -> b:pos
  -> Lemma (pow_mod_int #m 0 b == 0)
let lemma_pow_mod_int_zero #m b =
  lemma_pow_mod #m 0 b

val lemma_pow_mod_int_one:
    #m:prime 
  -> b:int 
  -> Lemma (pow_mod_int #m 1 b == 1)
let lemma_pow_mod_int_one #m b =
  if b >= 0 then 
    calc (==) {
      pow_mod_int #m 1 b;
      (==) {lemma_pow_mod #m 1 b}
      pow 1 b % m;
      (==) {lemma_pow_one b}
      1 % m;
    }
  else 
    calc (==) {
      pow_mod_int #m 1 b;
      (==) {lemma_pow_mod #m 1 ((-b) * (m - 2))}
      pow 1 ((-b) * (m - 2)) % m;
      (==) {lemma_pow_one ((-b) * (m - 2))}
      1 % m;
    }

#push-options "--fuel 1"
val lemma_pow_eq_fermat_pow:
    a:int
  -> k:nat 
  -> Lemma (pow a k == Fermat.pow a k)
let rec lemma_pow_eq_fermat_pow a k = 
  if k = 0 then ()
  else lemma_pow_eq_fermat_pow a (k-1)
#pop-options

val lemma_mul_def:
    a:int 
  -> b:int 
  -> Lemma (a + a * b == a * (b + 1))
let lemma_mul_def a b = ()

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
#push-options "--split_queries always"
val lemma_pow_mod_inv_def:
    #m:prime 
  -> a:nat_mod m{a % m <> 0}
  -> b:nat
  -> Lemma (pow_mod_int #m a b * pow_mod_int #m a (-b) % m == 1)
let lemma_pow_mod_inv_def #m a b =
  calc (==) {
    pow_mod_int #m a b * pow_mod_int #m a (-b) % m;
    (==) {}
    pow_mod #m a b * pow_mod #m a (b * (m - 2)) % m;
    (==) {lemma_pow_mod a b; lemma_pow_mod a (b * (m - 2))}
    (pow a b % m) * (pow a (b * (m - 2)) % m) % m;
    (==) {lemma_mod_mul_distr_r (pow a b) (pow a (b * (m - 2))) m;
          lemma_mod_mul_distr_l (pow a b) (pow a (b * (m - 2)) % m) m}
    (pow a b) * (pow a (b * (m - 2))) % m;
    (==) {lemma_pow_add a b (b * (m - 2))}
    (pow a (b + b * (m - 2))) % m;
    (==) {lemma_mul_def b (m - 2); swap_mul b (m-1)}
    (pow a ((m - 1) * b)) % m;
    (==) {lemma_pow_mul a (m - 1) b; lemma_pow_eq_fermat_pow a (m - 1)}
    (pow (Fermat.pow a (m - 1)) b) % m;
    (==) {lemma_pow_mod_base (Fermat.pow a (m - 1)) b m}
    (pow (Fermat.pow a (m - 1) % m) b) % m;
    (==) {Fermat.fermat_alt m a}
    (pow 1 b) % m;
    (==) {lemma_pow_one b}
    1 % m;
  }
#pop-options

val lemma_pow_mod_inv_twice_:
    #m:prime 
  -> a:nat_mod m 
  -> b:nat{b > 0}
  -> c:nat
  -> d:nat
  -> Lemma 
      (requires pow_mod #m a b == 1 /\ c % b == d)
      (ensures pow_mod #m a c == pow_mod #m a d)
let lemma_pow_mod_inv_twice_ #m a b c d =
  let k:nat = c / b in 
  assert (k * b + d == c);
  calc (==) {
    pow_mod #m a c;
    (==) {lemma_pow_mod #m a c}
    pow a c % m;
    (==) {}
    pow a (k * b + d) % m;
    (==) {lemma_pow_add a (k * b) d}
    (pow a (k * b) * pow a d) % m;
    (==) {lemma_pow_mul a b k}
    (pow (pow a b) k * pow a d) % m;
    (==) {lemma_mod_mul_distr_r (pow (pow a b) k) (pow a d) m;
          lemma_mod_mul_distr_l (pow (pow a b) k) (pow a d % m) m}
    ((pow (pow a b) k) % m) * (pow a d % m) % m;
    (==) {lemma_pow_mod_base (pow a b) k m}
    ((pow (pow a b % m) k) % m) * (pow a d % m) % m;
    (==) {lemma_pow_mod #m a b}
    (pow 1 k % m) * (pow a d % m) % m;
    (==) {lemma_pow_one k}
    (1 % m) * (pow a d % m) % m;
    (==) {lemma_mod_mul_distr_l 1 (pow a d) m;
          lemma_mod_mul_distr_r (1 % m) (pow a d) m}
    1 * (pow a d) % m;
    (==) {lemma_pow_mod #m a d}
    pow_mod #m a d;
  }

val lemma_double_inverse_mod:
  #m:prime{m > 2}
  -> Lemma ((m * m - 4 * m + 4) % (m - 1) == 1)
let lemma_double_inverse_mod #m =
  assert (m % (m - 1) == 1);
  calc (==) {
    m * m % (m - 1);
    (==) {lemma_mod_mul_distr_r m m (m - 1);
          lemma_mod_mul_distr_l m (m % (m - 1)) (m - 1)}
    (m % (m - 1)) * (m % (m - 1)) % (m - 1);
    (==) {}
    1 * 1 % (m - 1);
    (==) {}
    1;
  };
  calc (==) {
    (-4) * m % (m - 1);
    (==) {lemma_mod_mul_distr_r (-4) m (m - 1)}
    (-4) * (m % (m - 1)) % (m - 1);
    (==) {}
    (-4) % (m - 1);
  };
  calc (==) {
    (m * m - 4 * m + 4) % (m - 1);
    (==) {}
    (4 - 4 * m + m * m) % (m - 1);
    (==) {lemma_mod_add_distr (4 - 4 * m) (m * m) (m - 1)}
    (4 - 4 * m + (m * m) % (m - 1)) % (m - 1);
    (==) {}
    (5 + (- 4 * m)) % (m - 1);
    (==) {lemma_mod_add_distr 5 (-4 * m) (m - 1)}
    (5 + (- 4 * m) % (m - 1)) % (m - 1);
    (==) {}
    (5 + (-4) % (m - 1)) % (m - 1);
    (==) {lemma_mod_add_distr 5 (-4) (m - 1)}
    (5 + (-4)) % (m - 1);
    (==) {}
    1 % (m - 1);
  }

val lemma_pow_mod_inv_twice_zero:
    #m:prime{m > 2}
  -> Lemma (pow_mod_int #m (pow_mod_int #m 0 (-1)) (-1) == 0)
let lemma_pow_mod_inv_twice_zero #m =
  calc (==) {
    pow_mod_int #m (pow_mod_int #m 0 (-1)) (-1);
    (==) {lemma_pow_mod #m 0 (m - 2); lemma_pow_zero (m - 2)}
    pow_mod_int #m 0 (-1);
    (==) {lemma_pow_mod #m 0 (m - 2); lemma_pow_zero (m - 2)}
    0;
  }

val lemma_pow_mod_inv_twice_nonzero:
    #m:prime{m > 2}
  -> a:nat_mod m{a <> 0}
  -> Lemma (pow_mod_int #m (pow_mod_int #m a (-1)) (-1) == a)
let lemma_pow_mod_inv_twice_nonzero #m a = 
  Fermat.fermat_alt m a;
  lemma_double_inverse_mod #m;
  lemma_pow_eq_fermat_pow a (m - 1);
  lemma_pow_mod #m a (m - 1);
  assert (pow_mod #m a (m - 1) == 1);
  assert ((m - 2) * (m - 2) == (m * m - 4 * m + 4));
  assert ((m - 2) * (m - 2) % (m - 1) == 1);
  calc (==) {
    pow_mod_int #m (pow_mod_int #m a (-1)) (-1);
    (==) {lemma_pow_mod (pow_mod_int #m a (-1)) (m - 2);
          lemma_pow_mod a (m - 2)}
    pow (pow a (m - 2) % m) (m - 2) % m;
    (==) {lemma_pow_mod_base (pow a (m - 2)) (m - 2) m}
    pow (pow a (m - 2)) (m - 2) % m;
    (==) {lemma_pow_mul a (m - 2) (m - 2)}
    pow a ((m - 2) * (m - 2)) % m;
    (==) {lemma_pow_mod #m a ((m - 2) * (m - 2))}
    pow_mod #m a ((m - 2) * (m - 2));
    (==) {lemma_pow_mod_inv_twice_ #m a (m - 1) ((m - 2) * (m - 2)) 1}
    pow_mod #m a 1;
    (==) {lemma_pow_mod #m a 1}
    pow a 1 % m;
    (==) {lemma_pow1 a}
    a % m;
    (==) {small_mod a m}
    a;
  } 

#push-options "--split_queries always"
val lemma_pow_mod_inv_twice:
    #m:prime{m > 2}
  -> a:nat_mod m
  -> Lemma (pow_mod_int #m (pow_mod_int #m a (-1)) (-1) == a)
let lemma_pow_mod_inv_twice #m a = 
  if a = 0 then
    lemma_pow_mod_inv_twice_zero #m
  else
    lemma_pow_mod_inv_twice_nonzero #m a
#pop-options

val lemma_pow_mod_int_mul_pos_pos:
    #m:prime
  -> a:nat_mod m 
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma (pow_mod_int #m (pow_mod_int #m a b) c == pow_mod_int #m a (b * c))
let lemma_pow_mod_int_mul_pos_pos #m a b c = 
  calc (==) {
    pow_mod_int #m a (b * c);
    (==) {lemma_pow_mod a (b * c)}
    pow a (b * c) % m;
    (==) {lemma_pow_mul a b c}
    pow (pow a b) c % m;
    (==) {lemma_pow_mod_base (pow a b) c m}
    pow (pow a b % m) c % m;
    (==) {lemma_pow_mod #m (pow a b % m) c;
          lemma_pow_mod #m a b}
    pow_mod_int #m (pow_mod_int #m a b) c;
  }

val lemma_pow_mod_int_mul_pos_neg:
    #m:prime
  -> a:nat_mod m 
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma (pow_mod_int #m (pow_mod_int #m a (-b)) c == pow_mod_int #m a (-b * c))
let lemma_pow_mod_int_mul_pos_neg #m a b c =
  calc (==) {
    pow_mod_int #m (pow_mod_int #m a (-b)) c;
    (==) {lemma_pow_mod #m (pow_mod_int #m a (-b)) c; lemma_pow_mod #m a (b * (m - 2))}
    pow (pow a (b * (m - 2)) % m) c % m;
    (==) {lemma_pow_mod_base (pow a (b * (m - 2))) c m}
    pow (pow a (b * (m - 2))) c % m;
    (==) {lemma_pow_mul a (b * (m - 2)) c}
    pow a (b * (m - 2) * c) % m;
    (==) {swap_mul (m - 2) c}
    pow a (b * c * (m - 2)) % m;
    (==) {lemma_pow_mod #m a (b * c * (m - 2))}
    pow_mod_int #m a (-b * c);
  }

val lemma_pow_mod_int_mul_neg_pos:
    #m:prime
  -> a:nat_mod m 
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma (pow_mod_int #m (pow_mod_int #m a b) (-c) == pow_mod_int #m a (b * (-c)))
let lemma_pow_mod_int_mul_neg_pos #m a b c =
  calc (==) {
    pow_mod_int #m (pow_mod_int #m a b) (-c);
    (==) {lemma_pow_mod #m (pow_mod_int #m a b) (c * (m - 2))}
    pow ((pow_mod_int #m a b)) (c * (m - 2)) % m;
    (==) {lemma_pow_mod #m a b}
    pow ((pow a b % m)) (c * (m - 2)) % m;
    (==) {lemma_pow_mod_base (pow a b) (c * (m - 2)) m}
    pow (pow a b) (c * (m - 2)) % m;
    (==) {lemma_pow_mul a b (c * (m - 2))}
    pow a (b * (c * (m - 2))) % m;
    (==) {lemma_pow_mod #m a (b * c * (m - 2))}
    pow_mod_int #m a (b * (-c));
  }

val rearrange_aux:
    a:int
  -> b:int 
  -> c:int 
  -> d:int 
  -> Lemma ((a * b) * (c * d) == (a * c) * (b * d))
let rearrange_aux a b c d = ()

#push-options "--split_queries always"
val lemma_pow_mod_int_mul_neg_neg:
    #m:prime{m > 2}
  -> a:nat_mod m
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma (pow_mod_int #m (pow_mod_int #m a (-b)) (-c) == pow_mod_int #m a ((-b) * (-c)))
let lemma_pow_mod_int_mul_neg_neg #m a b c = 
  calc (==) {
    pow_mod_int #m (pow_mod_int #m a (-b)) (-c);
    (==) {lemma_pow_mod #m a (b * (m - 2));
          lemma_pow_mod #m (pow a (b * (m - 2)) % m) (c * (m - 2))}
    pow (pow a (b * (m - 2)) % m) (c * (m - 2)) % m;
    (==) {lemma_pow_mod_base (pow a (b * (m - 2))) (c * (m - 2)) m}
    pow (pow a (b * (m - 2))) (c * (m - 2)) % m;
    (==) {lemma_pow_mul a (b * (m - 2)) (c * (m - 2))}
    pow a ((b * (m - 2)) * (c * (m - 2))) % m;
    (==) {rearrange_aux b (m-2) c (m - 2)}
    pow a ((b * c) * ((m - 2) * (m - 2))) % m;
    (==) {lemma_pow_mul a (b * c) ((m - 2) * (m - 2))}
    pow (pow a (b * c)) ((m - 2) * (m - 2)) % m;
    (==) {lemma_pow_mul (pow a (b * c)) (m - 2) (m - 2)}
    pow (pow (pow a (b * c)) (m - 2)) (m - 2) % m;
    (==) {lemma_pow_mod_base (pow (pow a (b * c)) (m - 2)) (m - 2) m}
    pow (pow (pow a (b * c)) (m - 2) % m) (m - 2) % m;
    (==) {lemma_pow_mod_base (pow a (b * c)) (m - 2) m}
    pow (pow (pow a (b * c) % m) (m - 2) % m) (m - 2) % m;
    (==) {lemma_pow_mod #m a (b * c);
          lemma_pow_mod #m (pow_mod_int #m a (b * c)) (m - 2);
          lemma_pow_mod #m (pow_mod_int #m (pow_mod_int #m a (b * c)) (-1)) (m - 2)}
    pow_mod_int #m (pow_mod_int #m (pow_mod_int #m a (b * c)) (-1)) (-1);
    (==) {lemma_pow_mod_inv_twice #m (pow_mod_int #m a (b * c))}
    pow_mod_int #m a (b * c);
    (==) {}
    pow_mod_int #m a ((-b) * (-c));
  }
#pop-options 

val lemma_pow_mod_int_mul_zero:
    #m:prime
  -> a:nat_mod m 
  -> b:int 
  -> c:int 
  -> Lemma (requires b = 0 || c = 0) (ensures pow_mod_int #m (pow_mod_int #m a b) c == pow_mod_int #m a (b * c))
let lemma_pow_mod_int_mul_zero #m a b c = 
  lemma_pow_mod a 0;
  lemma_pow0 a;
  if b = 0 then 
    calc (==) {
      pow_mod_int #m (pow_mod_int #m a b) c;
      (==) {lemma_pow_mod #m a b}
      pow_mod_int #m (pow a b % m) c;
      (==) {lemma_pow0 a}
      pow_mod_int #m (1 % m) c;
      (==) {small_mod 1 m}
      pow_mod_int #m 1 c;
      (==) {lemma_pow_mod_int_one #m c}
      1;
    }
  else
    calc (==) {
      pow_mod_int #m (pow_mod_int #m a b) c;
      (==) {lemma_pow_mod (pow_mod_int #m a b) c}
      pow (pow_mod_int #m a b) c % m;
      (==) {lemma_pow0 (pow_mod_int #m a b)}
      1 % m;
    }

val lemma_pow_mod_int_mul:
    #m:prime{m > 2}
  -> a:nat_mod m 
  -> b:int 
  -> c:int 
  -> Lemma (pow_mod_int #m (pow_mod_int #m a b) c == pow_mod_int #m a (b * c))
let lemma_pow_mod_int_mul #m a b c =
  if b > 0 && c > 0 then 
    lemma_pow_mod_int_mul_pos_pos a b c
  else if b < 0 && c > 0 then 
    lemma_pow_mod_int_mul_pos_neg a (-b) c 
  else if b > 0 && c < 0 then
    lemma_pow_mod_int_mul_neg_pos a b (-c)
  else if b < 0 && c < 0 then 
    lemma_pow_mod_int_mul_neg_neg a (-b) (-c)
  else lemma_pow_mod_int_mul_zero #m a b c

  
val lemma_pow_mod_int_add_pos_pos:
    #m:prime
  -> a:nat_mod m 
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma ((pow_mod_int #m a b * pow_mod_int #m a c) % m == pow_mod_int #m a (b + c))
let lemma_pow_mod_int_add_pos_pos #m a b c =
  calc (==) {
    (pow_mod_int #m a b * pow_mod_int #m a c) % m;
    (==) {lemma_pow_mod a b; lemma_pow_mod a c}
    (pow a b % m) * (pow a c % m) % m;
    (==) {lemma_mod_mul_distr_l (pow a b) (pow a c) m;
          lemma_mod_mul_distr_r (pow a b % m) (pow a c) m}
    (pow a b) * (pow a c) % m;
    (==) {lemma_pow_add a b c}
    (pow a (b + c)) % m;
    (==) {lemma_pow_mod #m a (b + c)}
    pow_mod_int #m a (b + c);
  }

val lemma_pow_mod_int_add_neg_neg:
    #m:prime 
  -> a:nat_mod m 
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma ((pow_mod_int #m a (-b) * pow_mod_int #m a (-c)) % m == pow_mod_int #m a ((-b) + (-c)))
let lemma_pow_mod_int_add_neg_neg #m a b c = 
  calc (==) {
    (pow_mod_int #m a (-b) * pow_mod_int #m a (-c)) % m;
    (==) {lemma_pow_mod #m a (b * (m - 2)); lemma_pow_mod #m a (c * (m - 2))}
    (pow a (b * (m - 2)) % m) * (pow a (c * (m - 2)) % m) % m;
    (==) {lemma_mod_mul_distr_l (pow a (b * (m - 2))) (pow a (c * (m - 2))) m;
          lemma_mod_mul_distr_r (pow a (b * (m - 2)) % m) (pow a (c * (m - 2))) m}
    (pow a (b * (m - 2))) * (pow a (c * (m - 2))) % m;
    (==) {lemma_pow_add a (b * (m - 2)) (c * (m - 2))}
    (pow a (b * (m - 2) + c * (m - 2))) % m;
    (==) {}
    (pow a ((b + c) * (m - 2))) % m;
    (==) {lemma_pow_mod #m a ((b + c) * (m - 2))}
    pow_mod_int #m a (-(b + c));
  }


val lemma_pow_mod_int_exp_mod_congr_pos:
  #m:prime
  -> a:nat_mod m{a % m <> 0}
  -> b:int{b >= 0}
  -> Lemma (pow_mod_int #m a (b % (m - 1)) == pow_mod_int #m a b)
let lemma_pow_mod_int_exp_mod_congr_pos #m a b =
  let x:nat = b % (m - 1) in
  let k:nat = b / (m - 1) in 
  assert (b == k * (m - 1) + x);
  calc (==) {
    pow_mod_int #m a b;
    (==) {lemma_pow_mod #m a b}
    pow a (k * (m - 1) + x) % m;
    (==) {lemma_pow_add a (k * (m - 1)) x}
    (pow a (k * (m - 1))) * (pow a x) % m;
    (==) {lemma_mod_mul_distr_l (pow a (k * (m - 1))) (pow a x) m}
    (pow a (k * (m - 1)) % m) * (pow a x) % m;
    (==) {lemma_pow_mul a (m - 1) k}
    (pow (pow a (m - 1)) k % m) * (pow a x) % m;
    (==) {lemma_pow_mod_base (pow a (m - 1)) k m}
    (pow (pow a (m - 1) % m) k % m) * (pow a x) % m;
    (==) {lemma_pow_eq_fermat_pow a (m - 1); Fermat.fermat_alt m a}
    (pow 1 k % m) * (pow a x) % m;
    (==) {lemma_pow_one k}
    (1 % m) * (pow a x) % m;
    (==) {lemma_mod_mul_distr_l 1 (pow a x) m}
    1 * (pow a x) % m;
    (==) {lemma_pow_mod #m a x}
    pow_mod_int #m a x;
  }

val b_c_mod_m_minus_one:
    #m:prime
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma ((b + c * (m - 2)) % (m - 1) == (b - c) % (m - 1))
let b_c_mod_m_minus_one #m b c = 
  assert ((m - 2) % (m - 1) == (-1) % (m - 1));
  calc (==) {
    (b + c * (m - 2)) % (m - 1);
    (==) {modulo_distributivity b (c * (m - 2)) (m - 1)}
    (b % (m - 1) + (c * (m - 2)) % (m - 1)) % (m - 1);
    (==) {lemma_mod_mul_distr_r c (m - 2) (m - 1)}
    (b % (m - 1) + (c * ((m - 2) % (m - 1))) % (m - 1)) % (m - 1);
    (==) {}
    (b % (m - 1) + (c * ((-1) % (m - 1))) % (m - 1)) % (m - 1);
    (==) {lemma_mod_mul_distr_r c (-1) (m - 1)}
    (b % (m - 1) + (c * (-1)) % (m - 1)) % (m - 1);
    (==) {modulo_distributivity b (c * (-1)) (m - 1)}
    (b + (c * (-1))) % (m - 1);
  }

val lemma_pow_mod_int_add_neg_pos_res_pos:
    #m:prime 
  -> a:nat_mod m{a % m <> 0}
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma 
      (requires b - c > 0) 
      (ensures (pow_mod_int #m a b * pow_mod_int #m a (-c)) % m == pow_mod_int #m a (b - c))
let lemma_pow_mod_int_add_neg_pos_res_pos #m a b c = 
  calc (==) {
    (pow_mod_int #m a b * pow_mod_int #m a (-c)) % m;
    (==) {lemma_pow_mod #m a b; lemma_pow_mod #m a (c * (m - 2))}
    (pow a b % m) * (pow a (c * (m - 2)) % m) % m;
    (==) {lemma_mod_mul_distr_l (pow a b) (pow a (c * (m - 2))) m;
          lemma_mod_mul_distr_r (pow a b % m) (pow a (c * (m - 2))) m}
    (pow a b) * (pow a (c * (m - 2))) % m;
    (==) {lemma_pow_add a b (c * (m - 2))}
    (pow a (b + c * (m - 2))) % m;
    (==) {lemma_pow_mod a (b + c * (m - 2))}
    (pow_mod_int #m a (b + c * (m - 2)));
    (==) {lemma_pow_mod_int_exp_mod_congr_pos #m a (b + c * (m - 2))}
    (pow_mod_int #m a ((b + c * (m - 2)) % (m - 1)));
    (==) {b_c_mod_m_minus_one #m b c}
    (pow_mod_int #m a ((b - c) % (m - 1)));
    (==) {lemma_pow_mod_int_exp_mod_congr_pos #m a (b - c)}
    (pow_mod_int #m a (b - c));
  }

#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0 --split_queries always"
val lemma_pow_mod_int_add_negnat_pos_res_pos:
    #m:prime 
  -> a:nat_mod m{a % m <> 0}
  -> b:int{b > 0}
  -> c:nat
  -> Lemma 
      (requires b - c > 0) 
      (ensures (pow_mod_int #m a b * pow_mod_int #m a (-c)) % m == pow_mod_int #m a (b - c))
let lemma_pow_mod_int_add_negnat_pos_res_pos #m a b c =
  if c <> 0 then lemma_pow_mod_int_add_neg_pos_res_pos #m a b c
  else
    calc (==) {
      pow_mod_int #m a b * pow_mod_int #m a (-c) % m;
      (==) {lemma_pow_mod #m a 0}
      pow_mod_int #m a b * (pow a 0 % m) % m;
      (==) {lemma_pow0 a}
      pow_mod_int #m a b * (1 % m) % m;
      (==) {small_mod 1 m}
      pow_mod_int #m a b * 1 % m;
    }

val lemma_pow_mod_int_exp_mod_congr_neg:
  #m:prime{m > 2}
  -> a:nat_mod m{a % m <> 0}
  -> b:int{b > 0}
  -> Lemma (pow_mod_int #m a ((-b) % (m - 1)) == pow_mod_int #m a (-b))
let lemma_pow_mod_int_exp_mod_congr_neg #m a b =
  let x:nat = (-b) % (m - 1) in
  let k:int = (-b) / (m - 1) in
  assert (k <= 0);
  assert ((-b) = k * (m - 1) + x);
  assert (b = (-k) * (m - 1) - x);
  calc (==) {
    pow_mod_int #m a (-b);
    (==) {lemma_pow_mod #m a (b * (m - 2))}
    pow a (((-k) * (m - 1) - x) * (m - 2)) % m;
    (==) {lemma_pow_mul a ((-k) * (m - 1) - x) (m - 2)}
    pow (pow a ((-k) * (m - 1) - x)) (m - 2) % m;
    (==) {lemma_pow_mod_base (pow a ((-k) * (m - 1) - x)) (m - 2) m}
    pow (pow a ((-k) * (m - 1) - x) % m) (m - 2) % m;
    (==) {lemma_pow_mod #m a ((-k) * (m - 1) - x)}
    pow (pow_mod_int #m a ((-k) * (m - 1) - x)) (m - 2) % m;
    (==) {lemma_pow_mod_int_add_negnat_pos_res_pos #m a ((-k) * (m - 1)) x}
    pow ((pow_mod_int #m a ((-k) * (m - 1))) * (pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {lemma_pow_mod #m a ((-k) * (m - 1))}
    pow (((pow a ((-k) * (m - 1))) % m) * (pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {swap_mul (-k) (m - 1)}
    pow (((pow a ((m - 1) * (-k))) % m) * (pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {lemma_pow_mul a (m - 1) (-k)}
    pow (((pow (pow a (m - 1)) (-k)) % m) * (pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {lemma_pow_mod_base (pow a (m - 1)) (-k) m}
    pow (((pow (pow a (m - 1) % m) (-k)) % m) * (pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {lemma_pow_eq_fermat_pow a (m - 1); Fermat.fermat_alt m a}
    pow (((pow (1) (-k)) % m) * (pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {lemma_pow_one (-k)}
    pow ((1 % m) * (pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {small_mod 1 m}
    pow ((pow_mod_int #m a (-x)) % m) (m-2) % m;
    (==) {lemma_pow_mod_base (pow_mod_int #m a (-x)) (m - 2) m}
    pow (pow_mod_int #m a (-x)) (m-2) % m;
    (==) {lemma_pow_mod #m (pow_mod_int #m a (-x)) (m - 2)}
    pow_mod_int #m (pow_mod_int #m a (-x)) (-1);
    (==) {lemma_pow_mod_int_mul #m a x (-1)}
    pow_mod_int #m (pow_mod_int #m (pow_mod_int #m a x) (-1)) (-1);
    (==) {lemma_pow_mod_inv_twice #m (pow_mod_int #m a x)}
    pow_mod_int #m a x;
  }

#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
val lemma_pow_mod_int_exp_mod_congr:
  #m:prime{m > 2}
  -> a:nat_mod m{a % m <> 0}
  -> b:int
  -> Lemma (pow_mod_int #m a (b % (m - 1)) == pow_mod_int #m a b)
let lemma_pow_mod_int_exp_mod_congr #m a b =
  if b < 0 then lemma_pow_mod_int_exp_mod_congr_neg a (-b)
  else if b > 0 then lemma_pow_mod_int_exp_mod_congr_pos a b
  else ()

val lemma_fermat_congr:
    #m:prime{m > 2}
  -> a:nat_mod m{a % m <> 0}
  -> b:int
  -> c:int
  -> Lemma (requires b % (m - 1) = c % (m - 1)) (ensures pow_mod_int #m a b == pow_mod_int #m a c)
let lemma_fermat_congr #m a b c =
  calc (==) {
    pow_mod_int #m a b;
    (==) {lemma_pow_mod_int_exp_mod_congr a b}
    pow_mod_int #m a (b % (m - 1));
    (==) {}
    pow_mod_int #m a (c % (m - 1));
    (==) {lemma_pow_mod_int_exp_mod_congr a c}
    pow_mod_int #m a c;
  }

val lemma_pow_mod_int_add_neg_pos:
    #m:prime{m > 2}
  -> a:nat_mod m{a % m <> 0}
  -> b:int{b > 0}
  -> c:int{c > 0}
  -> Lemma ((pow_mod_int #m a b * pow_mod_int #m a (-c)) % m == pow_mod_int #m a (b - c))
let lemma_pow_mod_int_add_neg_pos #m a b c = 
  b_c_mod_m_minus_one #m b c;
  calc (==) {
    (pow_mod_int #m a b * pow_mod_int #m a (-c)) % m;
    (==) {lemma_pow_mod #m a b; lemma_pow_mod #m a (c * (m - 2))}
    (pow a b % m) * (pow a (c * (m - 2)) % m) % m;
    (==) {lemma_mod_mul_distr_l (pow a b) (pow a (c * (m - 2))) m;
          lemma_mod_mul_distr_r (pow a b % m) (pow a (c * (m - 2))) m}
    (pow a b) * (pow a (c * (m - 2))) % m;
    (==) {lemma_pow_add a b (c * (m - 2))}
    (pow a (b + c * (m - 2))) % m;
    (==) {lemma_pow_mod #m a (b + c * (m - 2))}
    pow_mod_int #m a (b + c * (m - 2));
    (==) {lemma_fermat_congr #m a (b + c * (m - 2)) (b - c)}
    pow_mod_int #m a (b - c);
  }

val lemma_pow_mod_int_add:
    #m:prime{m > 2}
  -> a:nat_mod m{a % m <> 0}
  -> b:int 
  -> c:int 
  -> Lemma ((pow_mod_int #m a b * pow_mod_int #m a c) % m == pow_mod_int #m a (b + c))
let lemma_pow_mod_int_add #m a b c =
  if b > 0 && c > 0 then lemma_pow_mod_int_add_pos_pos #m a b c
  else if b > 0 && c < 0 then lemma_pow_mod_int_add_neg_pos #m a b (-c)
  else if b < 0 && c > 0 then lemma_pow_mod_int_add_neg_pos #m a c (-b)
  else if b < 0 && c < 0 then lemma_pow_mod_int_add_neg_neg #m a (-b) (-c)
  else if b = 0 then
    calc (==) {
      (pow_mod_int #m a b * pow_mod_int #m a c) % m;
      (==) {lemma_pow_mod #m a b}
      ((pow a 0 % m) * (pow_mod_int #m a c)) % m;
      (==) {lemma_pow0 a}
      ((1 % m) * (pow_mod_int #m a c)) % m;
      (==) {small_mod 1 m}
      (pow_mod_int #m a c);
    }
  else 
    calc (==) {
      (pow_mod_int #m a b * pow_mod_int #m a c) % m;
      (==) {lemma_pow_mod #m a c}
      (pow_mod_int #m a b) * (pow a c % m) % m;
      (==) {lemma_pow0 a}
      (pow_mod_int #m a b) * (1 % m) % m;
      (==) {small_mod 1 m}
      (pow_mod_int #m a b);
    }

let pow_mod_int_neg_one (#m:nat{m > 1}) (n:int): nat_mod m =
  // pow_mod #q (neg_zq 1) (int_to_zq n)
  if n % 2 = 0 then 1 else ((-1) % m)

val lemma_pow_mod_int_neg_one:
    #m:nat{m > 1}
  -> n:int
  -> Lemma (pow_mod_int_neg_one #m n == ((-1) % m) * pow_mod_int_neg_one #m (n-1) % m
         /\ pow_mod_int_neg_one #m n == ((-1) % m) * pow_mod_int_neg_one #m (n+1) % m)
let lemma_pow_mod_int_neg_one #m n =
  if n % 2 = 0 then 
    calc (==) {
      ((-1) % m) * pow_mod_int_neg_one #m (n-1) % m;
      (==) {}
      ((-1) % m) * ((-1) % m) % m;
      (==) {lemma_mod_mul_distr_l (-1) (-1) m;
            lemma_mod_mul_distr_r ((-1) % m) (-1) m}
      (-1) * (-1) % m;
    }
  else 
    calc (==) {
      ((-1) % m) * pow_mod_int_neg_one #m (n-1) % m;
      (==) {}
      ((-1) % m) * 1 % m;
    }


val lemma_pow_mod_int_pow1:
    #m:prime{m > 2}
  -> a:nat_mod m
  -> Lemma (pow_mod_int #m a 1 == a)
let lemma_pow_mod_int_pow1 #m a =
  calc (==) {
    pow_mod_int #m a 1;
    (==) {lemma_pow_mod #m a 1}
    pow a 1 % m;
    (==) {lemma_pow1 a}
    a % m;
  }

val lemma_pow_mod_neg_one_eq_pow_mod_base:
    #m:prime{m > 2}
  -> n:int{n = 1 \/ n = 0}
  -> Lemma (pow_mod_int #m ((-1) % m) n == pow_mod_int_neg_one #m n)
let lemma_pow_mod_neg_one_eq_pow_mod_base #m n =
  if n = 0 then 
    calc (==) {
      pow_mod_int #m ((-1) % m) 0;
      (==) {lemma_pow_mod #m ((-1) % m) 0}
      1;
    }
  else 
    calc (==) {
      pow_mod_int #m ((-1) % m) 1;
      (==) {lemma_pow_mod_int_pow1 #m ((-1) % m)}
      (-1) % m;
    }

val lemma_pow_mod_neg_one_eq_pow_mod_pos:
    #m:prime{m > 2}
  -> n:nat
  -> Lemma (pow_mod_int #m ((-1) % m) n == pow_mod_int_neg_one #m n)
let rec lemma_pow_mod_neg_one_eq_pow_mod_pos #m n =
  assert ((-1) % m = m - 1);
  if n = 0 || n = 1 then 
    lemma_pow_mod_neg_one_eq_pow_mod_base #m n
  else 
    calc (==) {
      pow_mod_int #m (m - 1) n;
      (==) {lemma_pow_mod #m (m - 1) n}
      pow (m - 1) n % m;
      (==) {lemma_pow_unfold (m - 1) n}
      (m - 1) * (pow (m - 1) (n - 1)) % m;
      (==) {lemma_mod_mul_distr_l (m - 1) (pow (m - 1) (n - 1)) m;
            lemma_mod_mul_distr_r ((m - 1) % m) (pow (m - 1) (n - 1)) m}
      ((m - 1) % m) * (pow (m - 1) (n - 1) % m) % m;
      (==) {lemma_pow_mod #m (m - 1) (n - 1)}
      ((m - 1) % m) * (pow_mod_int #m (m - 1) (n - 1)) % m;
      (==) {}
      ((m - 1) % m) * (pow_mod_int #m ((-1) % m) (n - 1)) % m;
      (==) {lemma_pow_mod_neg_one_eq_pow_mod_pos #m (n - 1)}
      ((m - 1) % m) * (pow_mod_int_neg_one #m (n - 1)) % m;
      (==) {lemma_pow_mod_int_neg_one #m n}
      pow_mod_int_neg_one #m n;
    }

val lemma_pow_mod_neg_one_eq_pow_mod_base_neg_0:
    #m:prime{m > 2}
  -> Lemma (pow_mod_int #m ((-1) % m) 0 == pow_mod_int_neg_one #m 0)
let lemma_pow_mod_neg_one_eq_pow_mod_base_neg_0 #m =
  calc (==) {
    pow_mod_int #m ((-1) % m) 0;
    (==) {lemma_pow_mod #m ((-1) % m) 0}
    1;
  }

val lemma_pow_mod_neg_one_eq_pow_mod_base_neg_1:
    #m:prime{m > 2}
  -> Lemma (pow_mod_int #m ((-1) % m) (-1) == pow_mod_int_neg_one #m (-1))
let lemma_pow_mod_neg_one_eq_pow_mod_base_neg_1 #m =
  lemma_pow_mod_inv_def #m ((-1) % m) 1;
  calc (==>) {
    pow_mod_int #m ((-1) % m) 1 * pow_mod_int #m ((-1) % m) (-1) % m == 1;
    (==>) {lemma_pow_mod_int_pow1 #m ((-1) % m)}
    ((-1) % m) * pow_mod_int #m ((-1) % m) (-1) % m == 1;
    (==>) {lemma_mod_mul_distr_l (-1) (pow_mod_int #m ((-1) % m) (-1)) m}
    (-1) * pow_mod_int #m ((-1) % m) (-1) % m == 1;
    (==>) {}
    (-1) * pow_mod_int #m ((-1) % m) (-1) % m * (-1) == -1;
    (==>) {}
    (-1) * pow_mod_int #m ((-1) % m) (-1) % m * (-1) % m == (-1) % m;
    (==>) {lemma_mod_mul_distr_l ((-1) * pow_mod_int #m ((-1) % m) (-1)) (-1) m}
    (-1) * pow_mod_int #m ((-1) % m) (-1) * (-1) % m == (-1) % m;
    (==>) {swap_mul (pow_mod_int #m ((-1) % m) (-1)) (-1)}
    (-1) * (-1) * pow_mod_int #m ((-1) % m) (-1) % m == (-1) % m;
    (==>) {}
    pow_mod_int #m ((-1) % m) (-1) == (-1) % m;
  }
  

#reset-options "--z3rlimit 50 --fuel 1 --ifuel 0"
val lemma_pow_mod_neg_one_eq_pow_mod_base_neg:
    #m:prime{m > 2}
  -> n:int{n = 1 \/ n = 0}
  -> Lemma (pow_mod_int #m ((-1) % m) (-n) == pow_mod_int_neg_one #m (-n))
let lemma_pow_mod_neg_one_eq_pow_mod_base_neg #m n =
  if n = 0 then lemma_pow_mod_neg_one_eq_pow_mod_base_neg_0 #m
  else lemma_pow_mod_neg_one_eq_pow_mod_base_neg_1 #m

#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
val lemma_pow_mod_neg_one_eq_pow_mod_neg:
    #m:prime{m > 2}
  -> n:nat
  -> Lemma 
      (ensures pow_mod_int #m ((-1) % m) (-n) == pow_mod_int_neg_one #m (-n))
      (decreases n)
let rec lemma_pow_mod_neg_one_eq_pow_mod_neg #m n =
  // assert ((-1) % m = m - 1);
  assert ((-1) % m = m - 1);
  if n = 0 || n = 1 then 
    lemma_pow_mod_neg_one_eq_pow_mod_base_neg #m n
  else
    calc (==) {
      pow_mod_int #m (m - 1) (-n);
      (==) {lemma_pow_mod_int_add #m (m - 1) (-(n - 1)) (-1)}
      pow_mod_int #m (m - 1) (-(n - 1)) * pow_mod_int #m (m - 1) (-1) % m;
      (==) {lemma_pow_mod_neg_one_eq_pow_mod_neg #m (n - 1)}
      pow_mod_int_neg_one #m (-(n - 1)) * pow_mod_int #m ((-1) % m) (-1) % m;
      (==) {lemma_pow_mod_neg_one_eq_pow_mod_base_neg #m 1}
      pow_mod_int_neg_one #m (-(n - 1)) * pow_mod_int_neg_one #m (-1) % m;
      (==) {}
      pow_mod_int_neg_one #m (-(n - 1)) * ((-1) % m) % m;
      (==) {lemma_pow_mod_int_neg_one #m (-(n - 2))}
      pow_mod_int_neg_one #m (-n) % m;
    }

val lemma_pow_mod_neg_one_eq_pow_mod:
    #m:prime{m > 2}
  -> n:int
  -> Lemma (pow_mod_int #m ((-1) % m) n == pow_mod_int_neg_one #m n)
let lemma_pow_mod_neg_one_eq_pow_mod #m n =
  if n >= 0 then lemma_pow_mod_neg_one_eq_pow_mod_pos #m n
  else lemma_pow_mod_neg_one_eq_pow_mod_neg #m (-n)
  