module Hacl.Spec.MLkem.Sums

open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod
open Hacl.Spec.MLkem.Zq

// sum_of_zqs is sum_{i=start}^{stop-1} f(i)
let rec sum_of_zqs (start:int) (stop:int) (f:(i:int -> zq)): Tot zq (decreases stop - start) =
  if start >= stop then 0
  else f (stop - 1) +% (sum_of_zqs start (stop - 1) f)

// Lemmas about sum

#reset-options "--z3rlimit 10"
let lemma_sum_none (start:int) (f:int -> zq) : Lemma
  (requires True)
  (ensures 0 == (sum_of_zqs start start f))
  [SMTPat (sum_of_zqs start start f)]
  =
  ()

// f = g ==> sum f = sum g
let rec sum_rewrite_lemma (start stop:int) (f g:int -> zq): Lemma
    (requires (forall (i:int).{:pattern (f i)} start <= i /\ i < stop ==> f i == g i))
    (ensures (sum_of_zqs start stop f) == (sum_of_zqs start stop g))
    (decreases (stop - start))
    [SMTPat (sum_of_zqs start stop f)] 
    =
  if start < stop then sum_rewrite_lemma start (stop - 1) f g

let double_sum_rewrite_lemma (start1 stop1 start2 stop2:int) (f g:int -> int -> zq): Lemma 
  (requires (forall (i j:int). start1 <= i /\ i < stop1 /\ start2 <= j /\ j < stop2 ==> f i j == g i j))
  (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
        == sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> g i j))) =
  let original_f = (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) in 
  let goal_f = (fun i -> sum_of_zqs start2 stop2 (fun j -> g i j)) in
  let lemma_aux (i:int{start1 <= i /\ i < stop1}): Lemma (original_f i == goal_f i) = 
    sum_rewrite_lemma start2 stop2 (fun j -> f i j) (fun j -> g i j) in
  Classical.forall_intro lemma_aux;
  sum_rewrite_lemma start1 stop1 original_f goal_f

// sum_{i=start}^{stop-1} a * f(i) = a * sum_{i=start}^{stop-1} f(i)
// = a * sum_{i=start}^{stop-1} f'(i)
let rec sum_mul_lemma (a:zq) (start stop:int) (f:int -> zq): Lemma
    // (requires start <= stop)
    (ensures mul_zq a (sum_of_zqs start stop f) == sum_of_zqs start stop (fun i -> mul_zq a (f i)))
    (decreases (stop - start))
    [SMTPat (sum_of_zqs start stop (fun i -> a %* (f i)))] =
  if start < stop then (
    sum_mul_lemma a start (stop - 1) f;
    calc (==) {
      mul_zq a (sum_of_zqs start stop f);
      (==) {}
      a %* ((sum_of_zqs start (stop - 1) f) +% f (stop - 1));
      (==) {lemma_mod_distributivity_add_right #q a (sum_of_zqs start (stop - 1) f) (f (stop - 1))}
      (a %* (sum_of_zqs start (stop - 1) f)) +% (a %* f (stop - 1));
    }
  )

let double_sum_mul_lemma_ (start1 stop1 start2 stop2:int) (f_i:int -> zq) (f_j:int -> int -> zq) (i:int{i >= start1 && i < stop1}): Lemma 
  (ensures (f_i i %* sum_of_zqs start2 stop2 (f_j i)) == sum_of_zqs start2 stop2 (fun j -> f_i i %* (f_j i) j)) =
  sum_mul_lemma (f_i i) start2 stop2 (f_j i)


let double_sum_mul_lemma (start1 stop1 start2 stop2:int) (f_i:int -> zq) (f_j:int -> int -> zq): Lemma 
  (ensures sum_of_zqs start1 stop1 (fun i -> (f_i i %* sum_of_zqs start2 stop2 (f_j i))) 
        == sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f_i i %* (f_j i) j))) =
  let f = (fun i -> (f_i i %* sum_of_zqs start2 stop2 (f_j i))) in
  let f' = (fun i -> sum_of_zqs start2 stop2 (fun j -> f_i i %* (f_j i) j)) in
  Classical.forall_intro (double_sum_mul_lemma_ start1 stop1 start2 stop2 f_i f_j);
  assert (forall (i:int).{:pattern (f i)} start1 <= i /\ i < stop1 ==> f i == f' i);
  sum_rewrite_lemma start1 stop1 f f'

let unfold_sum (start stop:int) (f:int -> zq): Lemma 
    (requires stop > start)
    (ensures (sum_of_zqs start stop f) == ((sum_of_zqs start (stop-1) f) +% f (stop - 1))) = 
  ()

let lemma_rearrange (a b c d:zq) : Lemma
    (ensures a +% b +% c +% d == a +% c +% b +% d) =
  lemma_add_mod_comm #q b c;
  assert (b +% c == c +% b);
  calc (==) {
    a +% b +% c +% d;
    (==) {lemma_add_mod_assoc #q a b c}
    a +% (b +% c) +% d;
    (==) {}
    a +% (c +% b) +% d;
    (==) {lemma_add_mod_assoc #q a c b}
    a +% c +% b +% d;
  }

let lemma_mul_rearrange (a b c d:zq) : Lemma 
  (ensures a %* b %* c %* d == c %* a %* b %* d) =
  assert (b %* c == c %* b);
  calc (==) {
    a %* b %* c %* d;
    (==) {}
    a %* (b %* c) %* d;
    (==) {}
    a %* c %* b %* d;
  }

let lemma_mul_assoc_big (a b c d:zq): Lemma 
  (ensures a %* (b %* c %* d) == a %* b %* c %* d) =
  calc (==) {
    a %* (b %* c %* d);
    (==) {}
    a %* (b %* (c %* d));
    (==) {}
    a %* b %* (c %* d);
  }

let lemma_mul_assoc_bigger (a b c d e:zq): Lemma 
  (ensures a %* (b %* c %* d %* e) == a %* b %* c %* d %* e) =
  lemma_mul_assoc_big b c d e;
  assert (b %* c %* d %* e == b %* (c %* d %* e));
  calc (==) {
    a %* (b %* c %* d %* e);
    (==) {}
    a %* (b %* (c %* d %* e));
    (==) {}
    a %* b %* (c %* d %* e);
    (==) {}
    a %* b %* (c %* (d %* e));
    (==) {}
    a %* b %* c %* (d %* e);
  }

let rec distribute_sum_lemma (start stop:int) (f:int -> zq) (g:int -> zq): Lemma
    (ensures sum_of_zqs start stop (fun i -> f i +% g i) == sum_of_zqs start stop f +% sum_of_zqs start stop g)
    (decreases stop - start) =
  if start < stop then (
    distribute_sum_lemma start (stop - 1) f g;
    calc (==) {
      sum_of_zqs start stop (fun i -> f i +% g i);
      (==) {}
      sum_of_zqs start (stop-1) (fun i -> f i +% g i) +% (f (stop-1) +% g (stop-1));
      (==) {lemma_add_mod_assoc #q (sum_of_zqs start (stop-1) (fun i -> f i +% g i)) (f (stop-1)) (g (stop-1))}
      sum_of_zqs start (stop-1) (fun i -> f i +% g i) +% f (stop-1) +% g (stop-1);
      (==) {}
      sum_of_zqs start (stop-1) f +% sum_of_zqs start (stop-1) g +% f (stop-1) +% g (stop-1);
    };
    calc (==) {
      sum_of_zqs start stop f +% sum_of_zqs start stop g;
      (==) {}
      (sum_of_zqs start (stop-1) f +% f (stop-1)) +% (sum_of_zqs start (stop-1) g +% g (stop-1));
      (==) {lemma_add_mod_assoc #q (sum_of_zqs start (stop-1) f) (f (stop-1)) (sum_of_zqs start (stop-1) g +% g (stop-1))}
      sum_of_zqs start (stop-1) f +% f (stop-1) +% (sum_of_zqs start (stop-1) g +% g (stop-1));
      (==) {lemma_add_mod_assoc #q (sum_of_zqs start (stop-1) f +% f (stop-1)) (sum_of_zqs start (stop-1) g) (g (stop-1))}
      sum_of_zqs start (stop-1) f +% f (stop-1) +% sum_of_zqs start (stop-1) g +% g (stop-1);
      (==) { lemma_rearrange (sum_of_zqs start (stop-1) f) (f (stop-1)) (sum_of_zqs start (stop-1) g) (g (stop-1))}
      sum_of_zqs start (stop-1) f +% sum_of_zqs start (stop-1) g +% f (stop-1) +% g (stop-1);
    }
  )

let unfold_double_sum_inner (start1 start2 stop1 stop2:int) (f:int -> int -> zq): Lemma 
    (requires stop2 > start2)
    (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
         ==  sum_of_zqs start1 stop1 (fun i -> (sum_of_zqs start2 (stop2-1) (fun j -> f i j)) +% (f i (stop2-1)))) = 
  let inner_f = (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) in
  let inner_f_unfolded = (fun i -> (sum_of_zqs start2 (stop2-1) (fun j -> f i j)) +% f i (stop2-1)) in
  sum_rewrite_lemma start1 stop1 inner_f inner_f_unfolded

// Unfolding a double sum should give us:
// sum^n sum^m (f i j) = (sum^n-1 sum^m-1 (f i j)) + (sum^n-1 (f i m)) + (sum^m-1 (f n j)) + (f n m)
// Call it sum^n sum^m (f i j) = A + B + C + D
let unfold_double_sum (start1 start2 stop1 stop2:int) (f:int -> int -> zq): Lemma
    (requires stop1 > start1 /\ stop2 > start2)
    (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
              ==  sum_of_zqs start1 (stop1-1) (fun i -> 
                    (sum_of_zqs start2 (stop2-1) (fun j -> f i j)) +% (f i (stop2-1))) 
                  +% (sum_of_zqs start1 (stop1-1) (fun j -> f (stop1-1) j)) 
                  +% f (stop1-1) (stop2-1)) =
  let a = sum_of_zqs start1 (stop1-1) (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j)) in
  let b = sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1)) in
  let c = sum_of_zqs start1 (stop1-1) (fun j -> f (stop1-1) j) in
  let d = f (stop1-1) (stop2-1) in
  let initial_sum = sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) in
  unfold_double_sum_inner start1 start2 stop1 stop2 f;
  let unfolded_inner_f = (fun i -> (sum_of_zqs start2 (stop2-1) (fun j -> f i j)) +% (f i (stop2-1))) in
  assert (initial_sum == sum_of_zqs start1 stop1 (fun i -> unfolded_inner_f i));
  unfold_sum start1 stop1 unfolded_inner_f;
  assert (initial_sum == sum_of_zqs start1 (stop1-1) (fun i -> unfolded_inner_f i) +% unfolded_inner_f (stop1-1));
  let a_f = (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j)) in
  let b_f = (fun i -> f i (stop2-1)) in
  distribute_sum_lemma start1 stop1 a_f b_f;
  // assert (sum_of_zqs start1 (stop1-1));
  // assert (initial_sum == sum_of_zqs start1 (stop1-1) (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j)) +% sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1)) +% unfolded_inner_f (stop1-1));
  admit()
  // assert (sum_of_zqs start1 (stop1-1) (fun i -> unfolded_inner_f i)
  //      == sum_of_zqs start1 (stop1-1) (fun i -> (sum_of_zqs start2 (stop2-1) (fun j -> f i j))) +%
  //           sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1)));
  // admit()
  // admit()


let rec swap_sum_order (start1 stop1 start2 stop2:int) (f:int -> int -> zq): Lemma
    // (requires True)
    (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
          == sum_of_zqs start2 stop2 (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j)))
    (decreases (stop1 - start1)) =
  admit()
