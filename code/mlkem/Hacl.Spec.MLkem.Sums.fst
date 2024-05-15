module Hacl.Spec.MLkem.Sums

open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod

// let a = 1 `add_mod #(3)` 2

// sum_of_modint is sum_{i=start}^{stop-1} f(i)
let rec sum_of_modint (#m:pos{m > 1}) (start:int) (stop:int) (f:(i:int -> nat_mod m)): Tot (nat_mod m) (decreases stop - start) =
  if start >= stop then 0
  else f (stop - 1) `add_mod #m` (sum_of_modint #m start (stop - 1) f)

// Lemmas about sum

#reset-options "--z3rlimit 10"
let lemma_sum_none (#m:pos{m > 1}) (start:int) (f:int -> nat_mod m) : Lemma
  (requires True)
  (ensures 0 == (sum_of_modint #m start start f))
  =
  ()

// f = g ==> sum f = sum g
let rec sum_rewrite_lemma (#m:pos{m > 1})  (start stop:int) (f g:int -> nat_mod m): Lemma
    (requires (forall (i:int).{:pattern (f i)} start <= i /\ i < stop ==> f i == g i))
    (ensures (sum_of_modint #m start stop f) == (sum_of_modint #m start stop g))
    (decreases (stop - start))
    =
  if start < stop then sum_rewrite_lemma start (stop - 1) f g

#reset-options "--z3rlimit 15 --fuel 1"
let double_sum_rewrite_lemma (#m:pos{m > 1}) (start1 stop1 start2 stop2:int) (f g:int -> int -> nat_mod m): Lemma 
  (requires (forall (i j:int). start1 <= i /\ i < stop1 /\ start2 <= j /\ j < stop2 ==> f i j == g i j))
  (ensures sum_of_modint #m start1 stop1 (fun i -> sum_of_modint #m start2 stop2 (fun j -> f i j)) 
        == sum_of_modint #m start1 stop1 (fun i -> sum_of_modint #m start2 stop2 (fun j -> g i j))) =
  let original_f = (fun i -> sum_of_modint #m start2 stop2 (fun j -> f i j)) in 
  let goal_f = (fun i -> sum_of_modint #m start2 stop2 (fun j -> g i j)) in
  let lemma_aux (i:int{start1 <= i /\ i < stop1}): Lemma (original_f i == goal_f i) = 
    sum_rewrite_lemma start2 stop2 (fun j -> f i j) (fun j -> g i j) in
  Classical.forall_intro lemma_aux;
  sum_rewrite_lemma start1 stop1 original_f goal_f

#reset-options "--z3rlimit 15"
// sum_{i=start}^{stop-1} a * f(i) = a * sum_{i=start}^{stop-1} f(i)
// = a * sum_{i=start}^{stop-1} f'(i)
let rec sum_mul_lemma (#m:pos{m > 1}) (a:nat_mod m) (start stop:int) (f:int -> nat_mod m): Lemma
    // (requires start <= stop)
    (ensures a `mul_mod #m` (sum_of_modint #m start stop f) == sum_of_modint #m start stop (fun i -> a `mul_mod #m` (f i)))
    (decreases (stop - start)) =
  if start < stop then (
    sum_mul_lemma a start (stop - 1) f;
    calc (==) {
      a `mul_mod #m` (sum_of_modint #m start stop f);
      (==) {}
      a `mul_mod #m` ((sum_of_modint #m start (stop - 1) f) `add_mod #m` f (stop - 1));
      (==) {lemma_mod_distributivity_add_right #m a (sum_of_modint #m start (stop - 1) f) (f (stop - 1))}
      (a `mul_mod #m` (sum_of_modint #m start (stop - 1) f)) `add_mod #m` (a `mul_mod #m` f (stop - 1));
    }
  )

let double_sum_mul_lemma_ (#m:pos{m > 1}) (start1 stop1 start2 stop2:int) (f_i:int -> nat_mod m) (f_j:int -> int -> nat_mod m) (i:int{i >= start1 && i < stop1}): Lemma 
  (ensures (f_i i `mul_mod #m` sum_of_modint #m start2 stop2 (f_j i)) == sum_of_modint #m start2 stop2 (fun j -> f_i i `mul_mod #m` (f_j i) j)) =
  sum_mul_lemma (f_i i) start2 stop2 (f_j i)


let double_sum_mul_lemma (#m:pos{m > 1}) (start1 stop1 start2 stop2:int) (f_i:int -> nat_mod m) (f_j:int -> int -> nat_mod m): Lemma 
  (ensures sum_of_modint #m start1 stop1 (fun i -> (f_i i `mul_mod #m` sum_of_modint #m start2 stop2 (f_j i))) 
        == sum_of_modint #m start1 stop1 (fun i -> sum_of_modint #m start2 stop2 (fun j -> f_i i `mul_mod #m` (f_j i) j))) =
  let f = (fun i -> (f_i i `mul_mod #m` sum_of_modint #m start2 stop2 (f_j i))) in
  let f' = (fun i -> sum_of_modint #m start2 stop2 (fun j -> f_i i `mul_mod #m` (f_j i) j)) in
  Classical.forall_intro (double_sum_mul_lemma_ start1 stop1 start2 stop2 f_i f_j);
  assert (forall (i:int).{:pattern (f i)} start1 <= i /\ i < stop1 ==> f i == f' i);
  sum_rewrite_lemma start1 stop1 f f'

let unfold_sum (#m:pos{m > 1}) (start stop:int) (f:int -> nat_mod m): Lemma 
    (requires stop > start)
    (ensures (sum_of_modint #m start stop f) == ((sum_of_modint #m start (stop-1) f) `add_mod #m` f (stop - 1))) = 
  ()

let lemma_rearrange (#m:pos{m > 1}) (a b c d:nat_mod m) : Lemma
    (ensures a `add_mod #m` b `add_mod #m` c `add_mod #m` d == a `add_mod #m` c `add_mod #m` b `add_mod #m` d) =
  lemma_add_mod_comm #m b c;
  assert (b `add_mod #m` c == c `add_mod #m` b);
  calc (==) {
    a `add_mod #m` b `add_mod #m` c `add_mod #m` d;
    (==) {lemma_add_mod_assoc #m a b c}
    a `add_mod #m` (b `add_mod #m` c) `add_mod #m` d;
    (==) {}
    a `add_mod #m` (c `add_mod #m` b) `add_mod #m` d;
    (==) {lemma_add_mod_assoc #m a c b}
    a `add_mod #m` c `add_mod #m` b `add_mod #m` d;
  }

let lemma_mul_rearrange (#m:pos{m > 1}) (a b c d:nat_mod m) : Lemma 
  (ensures a `mul_mod #m` b `mul_mod #m` c `mul_mod #m` d == c `mul_mod #m` a `mul_mod #m` b `mul_mod #m` d) =
  assert (b `mul_mod #m` c == c `mul_mod #m` b);
  calc (==) {
    a `mul_mod #m` b `mul_mod #m` c `mul_mod #m` d;
    (==) {lemma_mul_mod_assoc #m a b c}
    a `mul_mod #m` (b `mul_mod #m` c) `mul_mod #m` d;
    (==) {lemma_mul_mod_comm #m b c}
    a `mul_mod #m` (c `mul_mod #m` b) `mul_mod #m` d;
    (==) {lemma_mul_mod_assoc #m a c b}
    a `mul_mod #m` c `mul_mod #m` b `mul_mod #m` d;
    (==) {lemma_mul_mod_comm #m a c}
    c `mul_mod #m` a `mul_mod #m` b `mul_mod #m` d;
  }

let lemma_mul_assoc_big (#m:pos{m > 1}) (a b c d:nat_mod m): Lemma 
  (ensures a `mul_mod #m` (b `mul_mod #m` c `mul_mod #m` d) == a `mul_mod #m` b `mul_mod #m` c `mul_mod #m` d) =
  calc (==) {
    a `mul_mod #m` (b `mul_mod #m` c `mul_mod #m` d);
    (==) {lemma_mul_mod_assoc #m a (b `mul_mod #m` c) d}
    (a `mul_mod #m` (b `mul_mod #m` c)) `mul_mod #m` d;
    (==) {lemma_mul_mod_assoc #m a b c}
    a `mul_mod #m` b `mul_mod #m` c `mul_mod #m` d;
  }

let lemma_mul_assoc_bigger (#m:pos{m > 1}) (a b c d e:nat_mod m): 
  Lemma 
    (a `mul_mod #m` (b `mul_mod #m` c `mul_mod #m` d `mul_mod #m` e) 
  == a `mul_mod #m` b `mul_mod #m` c `mul_mod #m` d `mul_mod #m` e) 
=
  calc (==) {
    a `mul_mod #m` (b `mul_mod #m` c `mul_mod #m` d `mul_mod #m` e);
    (==) {lemma_mul_mod_assoc #m a (b `mul_mod #m` c `mul_mod #m` d) e}
    (a `mul_mod #m` (b `mul_mod #m` c `mul_mod #m` d)) `mul_mod #m` e;
    (==) {lemma_mul_assoc_big #m a b c d}
    (a `mul_mod #m` b `mul_mod #m` c `mul_mod #m` d) `mul_mod #m` e;
  }

#reset-options "--z3rlimit 15 --fuel 1 --split_queries always"
let rec distribute_sum_lemma (#m:pos{m > 1}) (start stop:int) (f:int -> nat_mod m) (g:int -> nat_mod m): Lemma
    (ensures sum_of_modint #m start stop (fun i -> f i `add_mod #m` g i) == sum_of_modint #m start stop f `add_mod #m` sum_of_modint #m start stop g)
    (decreases stop - start) =
  if start < stop then (
    distribute_sum_lemma start (stop - 1) f g;
    calc (==) {
      sum_of_modint #m start stop (fun i -> f i `add_mod #m` g i);
      (==) {}
      sum_of_modint #m start (stop-1) (fun i -> f i `add_mod #m` g i) `add_mod #m` (f (stop-1) `add_mod #m` g (stop-1));
      (==) {lemma_add_mod_assoc #m (sum_of_modint #m start (stop-1) (fun i -> f i `add_mod #m` g i)) (f (stop-1)) (g (stop-1))}
      sum_of_modint #m start (stop-1) (fun i -> f i `add_mod #m` g i) `add_mod #m` f (stop-1) `add_mod #m` g (stop-1);
      (==) {}
      sum_of_modint #m start (stop-1) f `add_mod #m` sum_of_modint #m start (stop-1) g `add_mod #m` f (stop-1) `add_mod #m` g (stop-1);
    };
    calc (==) {
      sum_of_modint #m start stop f `add_mod #m` sum_of_modint #m start stop g;
      (==) {}
      (sum_of_modint #m start (stop-1) f `add_mod #m` f (stop-1)) `add_mod #m` (sum_of_modint #m start (stop-1) g `add_mod #m` g (stop-1));
      (==) {lemma_add_mod_assoc #m (sum_of_modint #m start (stop-1) f) (f (stop-1)) (sum_of_modint #m start (stop-1) g `add_mod #m` g (stop-1))}
      sum_of_modint #m start (stop-1) f `add_mod #m` f (stop-1) `add_mod #m` (sum_of_modint #m start (stop-1) g `add_mod #m` g (stop-1));
      (==) {lemma_add_mod_assoc #m (sum_of_modint #m start (stop-1) f `add_mod #m` f (stop-1)) (sum_of_modint #m start (stop-1) g) (g (stop-1))}
      sum_of_modint #m start (stop-1) f `add_mod #m` f (stop-1) `add_mod #m` sum_of_modint #m start (stop-1) g `add_mod #m` g (stop-1);
      (==) { lemma_rearrange (sum_of_modint #m start (stop-1) f) (f (stop-1)) (sum_of_modint #m start (stop-1) g) (g (stop-1))}
      sum_of_modint #m start (stop-1) f `add_mod #m` sum_of_modint #m start (stop-1) g `add_mod #m` f (stop-1) `add_mod #m` g (stop-1);
    }
  )

#reset-options "--z3rlimit 15"
let unfold_double_sum_inner (#m:pos{m > 1}) (start1 start2 stop1 stop2:int) (f:int -> int -> nat_mod m): Lemma 
    (requires stop2 > start2)
    (ensures sum_of_modint #m start1 stop1 (fun i -> sum_of_modint #m start2 stop2 (fun j -> f i j)) 
         ==  sum_of_modint #m start1 stop1 (fun i -> (sum_of_modint #m start2 (stop2-1) (fun j -> f i j)) `add_mod #m` (f i (stop2-1)))) = 
  let inner_f = (fun i -> sum_of_modint #m start2 stop2 (fun j -> f i j)) in
  let inner_f_unfolded = (fun i -> (sum_of_modint #m start2 (stop2-1) (fun j -> f i j)) `add_mod #m` f i (stop2-1)) in
  sum_rewrite_lemma start1 stop1 inner_f inner_f_unfolded

// Unfolding a double sum should give us:
// sum^n sum^m (f i j) = (sum^n-1 sum^m-1 (f i j)) + (sum^n-1 (f i m)) + (sum^m-1 (f n j)) + (f n m)
// Call it sum^n sum^m (f i j) = A + B + C + D
let unfold_double_sum (#m:pos{m > 1}) (start1 start2 stop1 stop2:int) (f:int -> int -> nat_mod m): Lemma
    (requires stop1 > start1 /\ stop2 > start2)
    (ensures sum_of_modint #m start1 stop1 (fun i -> sum_of_modint #m start2 stop2 (fun j -> f i j)) 
              ==  sum_of_modint #m start1 (stop1-1) (fun i -> 
                    (sum_of_modint #m start2 (stop2-1) (fun j -> f i j)) `add_mod #m` (f i (stop2-1))) 
                  `add_mod #m` (sum_of_modint #m start1 (stop1-1) (fun j -> f (stop1-1) j)) 
                  `add_mod #m` f (stop1-1) (stop2-1)) =
  let a = sum_of_modint #m start1 (stop1-1) (fun i -> sum_of_modint #m start2 (stop2-1) (fun j -> f i j)) in
  let b = sum_of_modint #m start1 (stop1-1) (fun i -> f i (stop2-1)) in
  let c = sum_of_modint #m start1 (stop1-1) (fun j -> f (stop1-1) j) in
  let d = f (stop1-1) (stop2-1) in
  let initial_sum = sum_of_modint #m start1 stop1 (fun i -> sum_of_modint #m start2 stop2 (fun j -> f i j)) in
  unfold_double_sum_inner start1 start2 stop1 stop2 f;
  let unfolded_inner_f = (fun i -> (sum_of_modint #m start2 (stop2-1) (fun j -> f i j)) `add_mod #m` (f i (stop2-1))) in
  assert (initial_sum == sum_of_modint #m start1 stop1 (fun i -> unfolded_inner_f i));
  unfold_sum start1 stop1 unfolded_inner_f;
  assert (initial_sum == sum_of_modint #m start1 (stop1-1) (fun i -> unfolded_inner_f i) `add_mod #m` unfolded_inner_f (stop1-1));
  let a_f = (fun i -> sum_of_modint #m start2 (stop2-1) (fun j -> f i j)) in
  let b_f = (fun i -> f i (stop2-1)) in
  distribute_sum_lemma start1 stop1 a_f b_f;
  // assert (sum_of_modint #m start1 (stop1-1));
  // assert (initial_sum == sum_of_modint #m start1 (stop1-1) (fun i -> sum_of_modint #m start2 (stop2-1) (fun j -> f i j)) `add_mod #m` sum_of_modint #m start1 (stop1-1) (fun i -> f i (stop2-1)) `add_mod #m` unfolded_inner_f (stop1-1));
  admit()
  // assert (sum_of_modint #m start1 (stop1-1) (fun i -> unfolded_inner_f i)
  //      == sum_of_modint #m start1 (stop1-1) (fun i -> (sum_of_modint #m start2 (stop2-1) (fun j -> f i j))) `add_mod #m`
  //           sum_of_modint #m start1 (stop1-1) (fun i -> f i (stop2-1)));
  // admit()
  // admit()


let rec swap_sum_order (#m:pos{m > 1}) (start1 stop1 start2 stop2:int) (f:int -> int -> nat_mod m): Lemma
    // (requires True)
    (ensures sum_of_modint #m start1 stop1 (fun i -> sum_of_modint #m start2 stop2 (fun j -> f i j)) 
          == sum_of_modint #m start2 stop2 (fun j -> sum_of_modint #m start1 stop1 (fun i -> f i j)))
    (decreases (stop1 - start1)) =
  admit()
