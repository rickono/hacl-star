module Hacl.Spec.MLkem.Sums

open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod
open Hacl.Spec.MLkem.Zq
open FStar.Math.Lemmas
open Hacl.Spec.MLkem.PowModInt

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
    (ensures mul_zq a (sum_of_zqs start stop f) == sum_of_zqs start stop (fun i -> mul_zq a (f i)))
    (decreases (stop - start))
    // [SMTPat (sum_of_zqs start stop (fun i -> a %* (f i)))] 
    =
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

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
let unfold_double_sum_a_b_distribute (start1 start2 stop1 stop2:int) (f:int -> int -> zq): 
  Lemma
    (requires stop1 > start1 /\ stop2 > start2)
    (ensures sum_of_zqs start1 (stop1-1) (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j) +% f i (stop2-1))
          == sum_of_zqs start1 (stop1-1) (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j))
             +% sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1)))
= 
  let fun1 = (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j)) in
  let fun2 = (fun i -> f i (stop2-1)) in
  let orig_fun = (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j) +% f i (stop2-1)) in
  distribute_sum_lemma start1 (stop1-1) fun1 fun2

let unfold_double_sum_inner_flipped_aux (start1 start2 stop1 stop2:int) (f:int -> int -> zq) (j:int): 
  Lemma 
    (requires stop2 > start2)
    (ensures sum_of_zqs start2 stop2 (fun i -> f i j) == (sum_of_zqs start2 (stop2-1) (fun i -> f i j)) +% (f (stop2-1) j))
= unfold_sum start2 stop2 (fun i -> f i j)

let unfold_double_sum_inner_flipped (start1 start2 stop1 stop2:int) (f:int -> int -> zq): Lemma 
    (requires stop2 > start2)
    (ensures sum_of_zqs start1 stop1 (fun j -> sum_of_zqs start2 stop2 (fun i -> f i j)) 
         ==  sum_of_zqs start1 stop1 (fun j -> (sum_of_zqs start2 (stop2-1) (fun i -> f i j)) +% (f (stop2-1) j))) = 
  let inner_f = (fun j -> sum_of_zqs start2 stop2 (fun i -> f i j)) in
  let inner_f_unfolded = (fun j -> (sum_of_zqs start2 (stop2-1) (fun i -> f i j)) +% (f (stop2-1) j)) in
  Classical.forall_intro (Classical.move_requires (unfold_double_sum_inner_flipped_aux start1 start2 stop1 stop2 f))

let unfold_double_sum_a_b_distribute_flipped (start1 start2 stop1 stop2:int) (f:int -> int -> zq): 
  Lemma
    (requires stop1 > start1 /\ stop2 > start2)
    (ensures sum_of_zqs start1 (stop1-1) (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j) +% f (stop2-1) j)
          == sum_of_zqs start1 (stop1-1) (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j))
             +% sum_of_zqs start1 (stop1-1) (fun j -> f (stop2-1) j))
= 
  let fun1 = (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j)) in
  let fun2 = (fun j -> f (stop2-1) j) in
  // let orig_fun = (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j) +% f i (stop2-1)) in
  distribute_sum_lemma start1 (stop1-1) fun1 fun2

// Unfolding a double sum should give us:
// sum^n sum^m (f i j) = (sum^n-1 sum^m-1 (f i j)) + (sum^n-1 (f i m)) + (sum^m-1 (f n j)) + (f n m)
// Call it sum^n sum^m (f i j) = A + B + C + D
let unfold_double_sum_flipped (start1 start2 stop1 stop2:int) (f:int -> int -> zq): Lemma
    (requires stop1 > start1 /\ stop2 > start2)
    (ensures sum_of_zqs start1 stop1 (fun j -> sum_of_zqs start2 stop2 (fun i -> f i j)) 
              ==  sum_of_zqs start1 (stop1-1) (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j))
               +% sum_of_zqs start1 (stop1-1) (fun j -> f (stop2-1) j)
               +% sum_of_zqs start2 (stop2-1) (fun i -> f i (stop1-1))
               +% f (stop2-1) (stop1-1)) =
  let a = sum_of_zqs start1 (stop1-1) (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j)) in
  let b = sum_of_zqs start1 (stop1-1) (fun j -> f (stop2-1) j) in
  let c = sum_of_zqs start2 (stop2-1) (fun i -> f i (stop1-1)) in
  let d = f (stop2-1) (stop1-1) in
  calc (==) {
    sum_of_zqs start1 stop1 (fun j -> sum_of_zqs start2 stop2 (fun i -> f i j));
    (==) {unfold_double_sum_inner_flipped start1 start2 stop1 stop2 f}
    sum_of_zqs start1 stop1 (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j) +% f (stop2-1) j);
    (==) {unfold_sum start1 stop1 (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j) +% f (stop2-1) j)}
    sum_of_zqs start1 (stop1-1) (fun j -> sum_of_zqs start2 (stop2-1) (fun i -> f i j) +% f (stop2-1) j) +% c +% d;
    (==) {unfold_double_sum_a_b_distribute_flipped start1 start2 stop1 stop2 f}
    a +% b +% c +% d;
  }


// Unfolding a double sum should give us:
// sum^n sum^m (f i j) = (sum^n-1 sum^m-1 (f i j)) + (sum^n-1 (f i m)) + (sum^m-1 (f n j)) + (f n m)
// Call it sum^n sum^m (f i j) = A + B + C + D
let unfold_double_sum (start1 start2 stop1 stop2:int) (f:int -> int -> zq): Lemma
    (requires stop1 > start1 /\ stop2 > start2)
    (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
              ==  sum_of_zqs start1 (stop1-1) (fun i -> (sum_of_zqs start2 (stop2-1) (fun j -> f i j)))
                  +% (sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1)))
                  +% (sum_of_zqs start2 (stop2-1) (fun j -> f (stop1-1) j)) 
                  +% f (stop1-1) (stop2-1)) =
  let a = sum_of_zqs start1 (stop1-1) (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j)) in
  let b = sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1)) in
  let c = sum_of_zqs start2 (stop2-1) (fun j -> f (stop1-1) j) in
  let d = f (stop1-1) (stop2-1) in
  calc (==) {
    sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j));
    (==) {unfold_double_sum_inner start1 start2 stop1 stop2 f}
    sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j) +% f i (stop2-1));
    (==) {unfold_sum start1 stop1 (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j) +% f i (stop2-1))}
    sum_of_zqs start1 (stop1-1) (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j) +% f i (stop2-1)) +% c +% d;
    (==) {unfold_double_sum_a_b_distribute start1 start2 stop1 stop2 f}
    a +% b +% c +% d;
  }

#reset-options "--z3rlimit 10 --fuel 1 --ifuel 0"
let swap_sum_order_base_1 (start1 stop1 start2 stop2:int) (f:int -> int -> zq): Lemma 
  (requires start1 + 1 = stop1)
  (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
        == sum_of_zqs start2 stop2 (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j))) 
=
  calc (==) {
    sum_of_zqs start1 (start1+1) (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j));
    (==) {unfold_sum start1 (start1+1) (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j))}
    sum_of_zqs start1 start1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) +% sum_of_zqs start2 stop2 (fun j -> f start1 j);
    (==) {lemma_sum_none start1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j))}
    sum_of_zqs start2 stop2 (fun j -> f start1 j);
  };
  calc (==) {
    sum_of_zqs start2 stop2 (fun j -> sum_of_zqs start1 (start1+1) (fun i -> f i j));
    (==) {unfold_double_sum_inner_flipped start2 start1 stop2 (start1+1) f}
    sum_of_zqs start2 stop2 (fun j -> sum_of_zqs start1 start1 (fun i -> f i j) +% f start1 j);
    (==) {}
    sum_of_zqs start2 stop2 (fun j -> f start1 j);
  }

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
let swap_sum_order_base_2 (start1 stop1 start2 stop2:int) (f:int -> int -> zq): Lemma 
  (requires start2 + 1 = stop2)
  (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
        == sum_of_zqs start2 stop2 (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j))) 
=
  calc (==) {
    sum_of_zqs start2 (start2+1) (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j));
    (==) {unfold_sum start2 (start2+1) (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j))}
    sum_of_zqs start2 start2 (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j)) +% sum_of_zqs start1 stop1 (fun i -> f i start2);
    (==) {lemma_sum_none start2 (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j))}
    sum_of_zqs start1 stop1 (fun i -> f i start2);
  };
  calc (==) {
    sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 (start2+1) (fun j -> f i j));
    (==) {unfold_double_sum_inner start1 start2 stop1 (start2+1) f}
    sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 start2 (fun j -> f i j) +% f i start2);
    (==) {}
    sum_of_zqs start1 stop1 (fun i -> f i start2);
  }

let rec swap_sum_order (start1 stop1 start2 stop2:int) (f:int -> int -> zq): Lemma
    (requires stop1 > start1 /\ stop2 > start2)
    (ensures sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j)) 
          == sum_of_zqs start2 stop2 (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j)))
    (decreases (stop1 - start1)) =
  if start1 + 1 = stop1 then swap_sum_order_base_1 start1 stop1 start2 stop2 f
  else if start2 + 1 = stop2 then swap_sum_order_base_2 start1 stop1 start2 stop2 f
  else
    calc (==) {
      sum_of_zqs start1 stop1 (fun i -> sum_of_zqs start2 stop2 (fun j -> f i j));
      (==) {unfold_double_sum start1 start2 stop1 stop2 f}
      sum_of_zqs start1 (stop1-1) (fun i -> sum_of_zqs start2 (stop2-1) (fun j -> f i j))
          +% sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1))
          +% sum_of_zqs start2 (stop2-1) (fun j -> f (stop1-1) j) 
          +% f (stop1-1) (stop2-1);
      (==) {swap_sum_order start1 (stop1-1) start2 (stop2-1) f}
      sum_of_zqs start2 (stop2-1) (fun j -> sum_of_zqs start1 (stop1-1) (fun i -> f i j))
          +% sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1))
          +% sum_of_zqs start2 (stop2-1) (fun j -> f (stop1-1) j) 
          +% f (stop1-1) (stop2-1);
      (==) {lemma_rearrange (sum_of_zqs start2 (stop2-1) (fun j -> sum_of_zqs start1 (stop1-1) (fun i -> f i j)))
                            (sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1)))
                            (sum_of_zqs start2 (stop2-1) (fun j -> f (stop1-1) j))
                            (f (stop1-1) (stop2-1))}
      sum_of_zqs start2 (stop2-1) (fun j -> sum_of_zqs start1 (stop1-1) (fun i -> f i j))
          +% sum_of_zqs start2 (stop2-1) (fun j -> f (stop1-1) j) 
          +% sum_of_zqs start1 (stop1-1) (fun i -> f i (stop2-1))
          +% f (stop1-1) (stop2-1);
      (==) {unfold_double_sum_flipped start2 start1 stop2 stop1 f}
      sum_of_zqs start2 stop2 (fun j -> sum_of_zqs start1 stop1 (fun i -> f i j));
    }

let rec lemma_sum_join (i j k:int) (f:int -> zq): Lemma
  (requires i <= j /\ j <= k)
  (ensures sum_of_zqs i k f == sum_of_zqs i j f +% sum_of_zqs j k f)
  (decreases (k - j)) =
if j < k then 
  calc (==) {
    sum_of_zqs i j f +% sum_of_zqs j k f;
    (==) {unfold_sum j k f}
    sum_of_zqs i j f +% sum_of_zqs j (k - 1) f +% f (k - 1);
    (==) {lemma_sum_join i j (k - 1) f}
    sum_of_zqs i (k - 1) f +% f (k - 1);
  }

let rec lemma_sum_shift (start stop:int) (shift:int) (f g:int -> zq): Lemma 
  (requires (forall (i:int). start <= i /\ i < stop ==> f i == g (i + shift)))
  (ensures sum_of_zqs start stop f == sum_of_zqs (start + shift) (stop + shift) g)
  (decreases (stop - start)) =
  if start < stop then lemma_sum_shift start (stop - 1) shift f g

let rewrite_shifted_idx_aux (stop:pos) (f:int -> zq) (j i:int): Lemma
  (f ((i - j) % stop) == f ((i - (j % stop)) % stop))
= 
  calc (==) {
    (i - j) % stop;
    (==) {lemma_mod_sub_distr i j stop}
    (i - j % stop) % stop;
  }

let rewrite_shifted_idx (stop:pos) (f:int -> zq) (j:int): Lemma
  (sum_of_zqs 0 stop (fun i -> f ((i - j) % stop))
  == sum_of_zqs 0 stop (fun i -> f ((i - (j % stop)) % stop)))
= 
  Classical.forall_intro (rewrite_shifted_idx_aux stop f j)

let lemma_sum_shift_mod_sum1_aux (stop:pos) (f:int -> zq) (r:nat_mod stop) (i:int): Lemma
  (requires 0 <= i /\ i < r)
  (ensures f ((i - r) % stop) == f (i - r + stop))
= ()

let lemma_sum_shift_mod_sum1 (stop:pos) (f:int -> zq) (r:nat_mod stop): Lemma
    (sum_of_zqs 0 r (fun i -> f ((i - r) % stop))
  == sum_of_zqs 0 r (fun i -> f (i - r + stop)))
= 
  Classical.forall_intro (Classical.move_requires (lemma_sum_shift_mod_sum1_aux stop f r))

let lemma_sum_shift_mod_sum2_aux (stop:pos) (f:int -> zq) (r:nat_mod stop) (i:int): Lemma 
  (requires r <= i /\ i < stop)
  (ensures f ((i - r) % stop) == f (i - r))
= ()

let lemma_sum_shift_mod_sum2 (stop:pos) (f:int -> zq) (r:nat_mod stop): Lemma 
    (sum_of_zqs r stop (fun i -> f ((i - r) % stop))
  == sum_of_zqs r stop (fun i -> f (i - r)))
= Classical.forall_intro (Classical.move_requires (lemma_sum_shift_mod_sum2_aux stop f r))

let lemma_sum_shift_mod_sum1_shift (stop:pos) (f:int -> zq) (r:nat_mod stop): Lemma 
    (sum_of_zqs 0 r (fun i -> f (i - r + stop))
  == sum_of_zqs (stop - r) stop f)
= 
  let shifted_f = (fun i -> f (i - r + stop)) in
  // assert (forall (i:int). 0 <= i /\ i < r ==> f i == shifted_f (i + r - stop));
  calc (==) {
    sum_of_zqs (stop - r) stop f;
    (==) {lemma_sum_shift (stop - r) stop (r - stop) f shifted_f}
    sum_of_zqs 0 r shifted_f;
  }

let lemma_sum_shift_mod_sum2_shift (stop:pos) (f:int -> zq) (r:nat_mod stop): Lemma 
    (sum_of_zqs r stop (fun i -> f (i - r))
  == sum_of_zqs 0 (stop - r) f)
= 
  let shifted_f = (fun i -> f (i - r)) in
  assert (forall (i:int). 0 <= i /\ i < r ==> f i == shifted_f (i + r));
  calc (==) {
    sum_of_zqs 0 (stop - r) f;
    (==) {lemma_sum_shift 0 (stop - r) r f shifted_f}
    sum_of_zqs r stop shifted_f;
  }

let lemma_sum_shift_mod (stop:nat{stop > 0}) (j:int) (f:int -> zq): 
Lemma 
  (sum_of_zqs 0 stop f == sum_of_zqs 0 stop (fun i -> f ((i - j) % stop)))
= 
  let q = j / stop in
  let r = j % stop in
  calc (==) {
    sum_of_zqs 0 stop (fun i -> f ((i - j) % stop));
    (==) {rewrite_shifted_idx stop f j}
    sum_of_zqs 0 stop (fun i -> f ((i - r) % stop));
    (==) {lemma_sum_join 0 r stop (fun i -> f ((i - r) % stop))}
    sum_of_zqs 0 r (fun i -> f ((i - r) % stop)) +% sum_of_zqs r stop (fun i -> f ((i - r) % stop));
    (==) {lemma_sum_shift_mod_sum1 stop f r}
    sum_of_zqs 0 r (fun i -> f (i - r + stop)) +% sum_of_zqs r stop (fun i -> f ((i - r) % stop));
    (==) {lemma_sum_shift_mod_sum2 stop f r}
    sum_of_zqs 0 r (fun i -> f (i - r + stop)) +% sum_of_zqs r stop (fun i -> f (i - r));
    (==) {lemma_sum_shift_mod_sum1_shift stop f r}
    sum_of_zqs (stop - r) stop f +% sum_of_zqs r stop (fun i -> f (i - r));
    (==) {lemma_sum_shift_mod_sum2_shift stop f r}
    sum_of_zqs (stop - r) stop f +% sum_of_zqs 0 (stop - r) f;
    (==) {lemma_sum_join 0 (stop - r) stop f}
    sum_of_zqs 0 stop f;
  }

let lemma_geometric_sum_base a: Lemma
  (requires a % q <> 1)
  (ensures sum_of_zqs 0 1 (fun i -> pow_mod_int #q a i) == (((pow_mod_int #q a 1) - 1) % q) %* (pow_mod_int #q ((a - 1) % q) (-1)))
= 
  calc (==) {
    sum_of_zqs 0 1 (fun i -> pow_mod_int #q a i);
    (==) {}
    pow_mod_int #q a 0;
    (==) {lemma_pow_mod_int_pow0 #q a}
    1;
  };
  calc (==) {
    (((pow_mod_int #q a 1) - 1) % q) %* (pow_mod_int #q ((a - 1) % q) (-1));
    (==) {lemma_pow_mod_int_pow1 #q a}
    (a - 1) % q %* (pow_mod_int #q ((a - 1) % q) (-1));
    (==) {lemma_pow_mod_int_pow1 #q ((a - 1) % q)}
    (pow_mod_int #q ((a - 1) % q) 1) %*  (pow_mod_int #q ((a - 1) % q) (-1));
    (==) {lemma_pow_mod_inv_def #q ((a - 1) % q) 1}
    1;
  }

let lemma_geosum_rearr_for_distr_rearr (a b c:zq): Lemma 
  (ensures (a %* (b %* c)) == (c %* a %* b)) =
calc (==) {
  a %* (b %* c);
  (==) {}
  a %* (c %* b);
  (==) {}
  a %* c %* b;
  (==) {}
  c %* a %* b;
}

let lemma_geosum_rearr_for_distr (stop:pos) (a:zq): Lemma
  (requires a % q <> 1)
  (ensures (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) %* (pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1))
        == (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) %* (pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1)))
= 
  calc (==) {
    (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) %* (pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1));
    (==) {lemma_mul_mod_comm ((pow_mod_int #q a (stop-1) - 1) % q) (pow_mod_int #q ((a - 1) % q) (-1))}
    (pow_mod_int #q ((a - 1) % q) (-1) %* ((pow_mod_int #q a (stop-1) - 1) % q) ) +% pow_mod_int #q a (stop-1) %* (pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1));
    (==) {lemma_geosum_rearr_for_distr_rearr (pow_mod_int #q a (stop-1)) (pow_mod_int #q ((a - 1) % q) (1)) (pow_mod_int #q ((a - 1) % q) (-1))}
    (pow_mod_int #q ((a - 1) % q) (-1) %* ((pow_mod_int #q a (stop-1) - 1) % q) ) +% pow_mod_int #q ((a - 1) % q) (-1) %* pow_mod_int #q a (stop-1) %* (pow_mod_int #q ((a - 1) % q) (1));
  }

let lemma_mod_sub_distr_l (a b:int) (m:pos): Lemma
  ((a - b) % m == (a % m - b) % m)
= 
  calc (==) {
    (a - b) % m;
    (==) {}
    (-b + a) % m;
    (==) {lemma_mod_add_distr (-b) a m}
    (-b + a % m) % m;
    (==) {}
    (a % m - b) % m;
  }

#reset-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let lemma_geosum_distr_inner (stop:pos) (a:zq): Lemma
  (requires a % q <> 1 && stop > 1)
  (ensures pow_mod_int #q a (stop-1) %* pow_mod_int #q ((a - 1) % q) (1)
        == pow_mod_int #q a stop -% pow_mod_int #q a (stop - 1))
= 
  calc (==) {
    pow_mod_int #q a (stop-1) %* pow_mod_int #q ((a - 1) % q) (1);
    (==) {lemma_pow_mod_int_pow1 #q ((a - 1) % q)}
    pow_mod_int #q a (stop-1) %* ((a - 1) % q);
    (==) {}
    pow_mod_int #q a (stop-1) * ((a - 1) % q) % q;
    (==) {lemma_mod_mul_distr_r (pow_mod_int #q a (stop-1)) (a - 1) q}
    pow_mod_int #q a (stop-1) * (a - 1) % q;
    (==) {distributivity_sub_right (pow_mod_int #q a (stop-1)) a 1}
    (pow_mod_int #q a (stop-1) * a - pow_mod_int #q a (stop-1)) % q;
    (==) {lemma_mod_sub_distr_l (pow_mod_int #q a (stop-1) * a) (pow_mod_int #q a (stop-1)) q}
    ((pow_mod_int #q a (stop-1) * a % q) - pow_mod_int #q a (stop-1)) % q;
    (==) {lemma_pow_mod #q a (stop-1)}
    (((pow a (stop-1) % q) * a % q) - pow_mod_int #q a (stop-1)) % q;
    (==) {lemma_mod_mul_distr_l (pow a (stop-1)) a q}
    (((pow a (stop-1)) * a % q) - pow_mod_int #q a (stop-1)) % q;
    (==) {lemma_pow_unfold a stop}
    ((pow a stop % q) - pow_mod_int #q a (stop-1)) % q;
    (==) {lemma_pow_mod #q a stop}
    (pow_mod_int #q a stop - pow_mod_int #q a (stop-1)) % q;
  }

let lemma_geometric_sum_rearrange (stop:pos) (a:zq): Lemma 
  (requires a % q <> 1)
  (ensures  (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1)
        == (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) %* pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1))
= 
  calc (==) {
    (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1);
      (==) {}
      (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) * 1;
      (==) {lemma_pow_mod_inv_def #q ((a - 1) % q) 1}
      (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) %* (pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1));
      (==) {}
      (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) %* pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1);
  }

let lemma_geometric_sum_final_rewrite (stop:pos) (a:zq): Lemma 
  (requires a % q <> 1)
  (ensures  (((pow_mod_int #q a (stop-1) - 1) % q) +% (pow_mod_int #q a stop -% pow_mod_int #q a (stop - 1)))
        == (((pow_mod_int #q a stop) - 1) % q))
= 
  calc (==) {
    ((pow_mod_int #q a (stop-1) - 1) % q) +% (pow_mod_int #q a stop -% pow_mod_int #q a (stop - 1));
    (==) {}
    (((pow_mod_int #q a (stop-1) - 1) % q) + (pow_mod_int #q a stop - pow_mod_int #q a (stop - 1)) % q) % q;
    (==) {}
    ((pow_mod_int #q a (stop-1) - 1) + (pow_mod_int #q a stop - pow_mod_int #q a (stop - 1))) % q;
    (==) {}
    (pow_mod_int #q a (stop-1) - 1 + (pow_mod_int #q a stop - pow_mod_int #q a (stop - 1))) % q;
    (==) {}
    (pow_mod_int #q a (stop-1) - 1 + pow_mod_int #q a stop - pow_mod_int #q a (stop - 1)) % q;
  }

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0"
let rec lemma_geometric_sum (stop:pos) (a:zq): Lemma 
  (requires a % q <> 1)
  (ensures sum_of_zqs 0 stop (fun i -> pow_mod_int #q a i) == ((pow_mod_int #q a stop) -% 1) %* (pow_mod_int #q ((a - 1) % q) (-1)))
  (decreases stop)
= 
  if stop = 1 then lemma_geometric_sum_base a
  else
    calc (==) {
      sum_of_zqs 0 stop (fun i -> pow_mod_int #q a i);
      (==) {}
      sum_of_zqs 0 (stop-1) (fun i -> pow_mod_int #q a i) +% pow_mod_int #q a (stop-1);
      (==) {lemma_geometric_sum (stop-1) a}
      (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1);
      (==) {lemma_geometric_sum_rearrange stop a}
      (((pow_mod_int #q a (stop-1) - 1) % q) %* pow_mod_int #q ((a - 1) % q) (-1)) +% pow_mod_int #q a (stop-1) %* pow_mod_int #q ((a - 1) % q) (1) %* pow_mod_int #q ((a - 1) % q) (-1);
      (==) {lemma_mod_distributivity_add_left #q ((pow_mod_int #q a (stop-1) - 1) % q) (pow_mod_int #q a (stop-1) %* pow_mod_int #q ((a - 1) % q) (1)) (pow_mod_int #q ((a - 1) % q) (-1))}
      (((pow_mod_int #q a (stop-1) - 1) % q) +% (pow_mod_int #q a (stop-1) %* pow_mod_int #q ((a - 1) % q) (1))) %* (pow_mod_int #q ((a - 1) % q) (-1));
      (==) {lemma_geosum_distr_inner stop a}
      (((pow_mod_int #q a (stop-1) - 1) % q) +% (pow_mod_int #q a stop -% pow_mod_int #q a (stop - 1))) %* (pow_mod_int #q ((a - 1) % q) (-1));
      (==) {lemma_geometric_sum_final_rewrite stop a}
      ((pow_mod_int #q a stop) -% 1) %* (pow_mod_int #q ((a - 1) % q) (-1));
    }

let rec lemma_zq_sum_ones (start stop:nat): Lemma 
  (requires start <= stop)
  (ensures sum_of_zqs start stop (fun i -> 1) == (stop - start) % q)
= if start = stop then ()
  else 
    calc (==) {
      sum_of_zqs start stop (fun i -> 1);
      (==) {unfold_sum start stop (fun i -> 1)}
      sum_of_zqs start (stop-1) (fun i -> 1) +% 1;
      (==) {lemma_zq_sum_ones start (stop-1)}
      (((stop-1) - start) % q) +% 1;
      (==) {}
      ((stop - 1) - start + 1) % q;
    }

let lemma_geometric_sum_ones_aux (stop:pos): Lemma
  (ensures sum_of_zqs 0 stop (fun i -> pow_mod_int #q 1 i) == sum_of_zqs 0 stop (fun i -> 1))
= 
  Classical.forall_intro (lemma_pow_mod_int_one #q)

#reset-options "--z3rlimit 15 --fuel 1 --ifuel 0 --query_stats"
let lemma_geometric_sum_ones (stop:pos) (a:zq): Lemma
  (requires a % q = 1)
  (ensures sum_of_zqs 0 stop (fun i -> pow_mod_int #q a i) == stop % q)
= 
  calc (==) {
    sum_of_zqs 0 stop (fun i -> pow_mod_int #q 1 i);
    (==) {lemma_geometric_sum_ones_aux stop}
    sum_of_zqs 0 stop (fun i -> 1);
    (==) {lemma_zq_sum_ones 0 stop}
    stop % q;
  }

let rec lemma_sum_zeros (start stop:nat): Lemma
  (requires start <= stop)
  (ensures sum_of_zqs start stop (fun i -> 0) == 0)
= if start = stop then ()
  else
    calc (==) {
      sum_of_zqs start stop (fun i -> 0);
      (==) {unfold_sum start stop (fun i -> 0)}
      sum_of_zqs start (stop-1) (fun i -> 0) +% 0;
      (==) {lemma_sum_zeros start (stop-1)}
      0 +% 0;
      (==) {}
      0;
    }

let lemma_sum_split_parity_rearrange (a b c d:zq): Lemma (a +% b +% c +% d == (a +% c) +% (b +% d)) =
  calc (==) {
    a +% b +% c +% d;
    (==) {}
    a +% (b +% c) +% d;
    (==) {}
    a +% (c +% b) +% d;
    (==) {}
    a +% c +% b +% d;
  }

let rec lemma_sum_split_parity (stop:nat{stop % 2 = 0}) (f:int -> zq): Lemma 
  (requires stop >= 0)
  (ensures sum_of_zqs 0 stop f == sum_of_zqs 0 (stop/2) (fun i -> f (2 * i)) +% sum_of_zqs 0 (stop/2) (fun i -> f (2 * i + 1)))
= if stop = 0 then ()
  else
    calc (==) {
      sum_of_zqs 0 stop f;
      (==) {unfold_sum 0 stop f}
      sum_of_zqs 0 (stop-1) f +% f (stop-1);
      (==) {unfold_sum 0 (stop-1) f}
      sum_of_zqs 0 (stop-2) f +% f (stop-2) +% f (stop-1);
      (==) {lemma_sum_split_parity (stop-2) f}
      sum_of_zqs 0 ((stop-2)/2) (fun i -> f (2 * i)) +% sum_of_zqs 0 ((stop-2)/2) (fun i -> f (2 * i + 1)) +% f (stop-2) +% f (stop-1);
      (==) {lemma_sum_split_parity_rearrange (sum_of_zqs 0 ((stop-2)/2) (fun i -> f (2 * i))) (sum_of_zqs 0 ((stop-2)/2) (fun i -> f (2 * i + 1))) (f (stop-2)) (f (stop-1))}
      (sum_of_zqs 0 ((stop-2)/2) (fun i -> f (2 * i)) +% f (stop-2)) +% (sum_of_zqs 0 ((stop-2)/2) (fun i -> f (2 * i + 1)) +% f (stop-1));
      (==) {unfold_sum 0 (stop/2) (fun i -> f (2 * i))}
      (sum_of_zqs 0 (stop/2) (fun i -> f (2 * i))) +% (sum_of_zqs 0 ((stop-2)/2) (fun i -> f (2 * i + 1)) +% f (stop-1));
      (==) {unfold_sum 0 (stop/2) (fun i -> f (2 * i + 1))}
      (sum_of_zqs 0 (stop/2) (fun i -> f (2 * i))) +% (sum_of_zqs 0 (stop/2) (fun i -> f (2 * i + 1)));
    }