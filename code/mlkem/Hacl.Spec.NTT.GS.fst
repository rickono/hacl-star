module Hacl.Spec.NTT.GS

open FStar.Mul
open FStar.Seq
unfold let max = FStar.Math.Lib.max

open Lib.IntTypes
open Lib.Sequence
open Lib.NatMod
module Fermat = FStar.Math.Fermat
module Euclid = FStar.Math.Euclid
module ML = FStar.Math.Lemmas
open Hacl.Spec.MLkem.Poly
open Hacl.Spec.MLkem.Zq
open Hacl.Spec.MLkem.Sums
open Hacl.Spec.MLkem.PowModInt
open Hacl.Spec.MLkem.Unity
open Hacl.Spec.NTT.CT

open Hacl.Spec.MLkem.NTT

val poly_lower:
    #n:size_nat
  -> f:lpoly n
  -> lpoly (n / 2)
let poly_lower #n f = createi (n / 2) (fun i -> poly_index #n f i)

val poly_lower_to_poly_idx:
    #n:size_nat
  -> f:lpoly n
  -> i:nat{i < n / 2}
  -> Lemma (poly_index #n f i == poly_index (poly_lower #n f) i)
let poly_lower_to_poly_idx #n f i = ()

val poly_upper:
    #n:size_nat
  -> f:lpoly n
  -> lpoly (n / 2)
let poly_upper #n f = createi (n / 2) (fun i -> poly_index #n f (i + n / 2))

val poly_upper_to_poly_idx:
    #n:size_nat
  -> f:lpoly n
  -> i:nat{i < n / 2}
  -> Lemma (poly_index #n f (i + n/2) == poly_index (poly_upper #n f) i)
let poly_upper_to_poly_idx #n f i = ()

val intt_gs_kth_term:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> zq
let rec intt_gs_kth_term #n #psi f k =
  if n = 1 then (poly_index #n f k)
  else if k < 0 || k >= n then 0 
  else if k % 2 = 0 then begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    (intt_gs_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_lower #n f) (k / 2)
     +% intt_gs_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_upper #n f) (k / 2)) %* pow_mod_int #q psi (-2 * k)
  end else begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    (intt_gs_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_lower #n f) (k / 2)
     -% intt_gs_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_upper #n f) (k / 2)) %* pow_mod_int #q psi (-2 * k)
  end

val intt_kth_term_unscaled:
    #n:power_of_two{n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> zq
let intt_kth_term_unscaled #n #psi f k =
  if k < 0 || k >= n then 0
  else sum_of_zqs 0 n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))

let lemma_scale_intt_unscaled (#n:power_of_two{n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (k:int): 
  Lemma (intt_kth_term #n #psi f k == pow_mod_int #q n (-1) %* intt_kth_term_unscaled #n #psi f k)
  = ()

val intt_gs_kth_term_ok_base:
    #n:power_of_two{n = 1}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k >= 0 && k < n}
  -> Lemma (intt_kth_term #n #psi f k == intt_gs_kth_term #n #psi f k)
let intt_gs_kth_term_ok_base #n #psi f k =
  assert (k = 0);
  calc (==) {
    intt_kth_term #n #psi f k;
    (==) {}
    pow_mod_int #q 1 (-1) %* sum_of_zqs 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
    (==) {lemma_pow_mod_int_one #q (-1)}
    1 %* sum_of_zqs 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
    (==) {}
    sum_of_zqs 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
    (==) {unfold_sum 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))}
    sum_of_zqs 0 0 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1)))) +% mul_zq (poly_index f 0) (pow_mod_int #q psi (-k * (2 * 0 + 1)));
    (==) {lemma_sum_none 0 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))}
    0 +% mul_zq (poly_index f 0) (pow_mod_int #q psi (-k * (2 * 0 + 1)));
    (==) {}
    mul_zq (poly_index f 0) (pow_mod_int #q psi (-0));
    (==) {}
    mul_zq (poly_index f 0) (pow_mod_int #q psi (0));
    (==) {lemma_pow_mod_int_pow0 #q psi}
    (poly_index f 0);
    (==) {}
    intt_gs_kth_term #n #psi f k;
  }

val intt_gs_kth_term_ok_split_sums_shift:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int{k >= 0 && k < n}
  -> Lemma (sum_of_zqs (n/2) n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
        == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))))
let intt_gs_kth_term_ok_split_sums_shift #n #psi f k =
  let f1 = (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))) in
  let f2 = (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1)))) in
  lemma_sum_shift 0 (n / 2) (n / 2) f1 f2

let lemma_neg_assoc (a b:int): Lemma (-a * b == (-a) * b) = ()
let lemma_neg_distr (a:int): Lemma (-a == (-1) * a) = ()

val intt_gs_kth_term_ok_split_sums_simpl_psi_rearr_exp:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int{k >= 0 && k < n}
  -> i:nat{i < n / 2}
  -> Lemma (-k * (2 * (i + n / 2) + 1)
          == n * ((-1) * k) + -k * (2 * i + 1))
let intt_gs_kth_term_ok_split_sums_simpl_psi_rearr_exp #n #psi f k i =
  calc (==) {
    (-k * (2 * (i + n / 2) + 1));
    (==) {}
    (-k * (2 * i + n + 1));
    (==) {}
    (-k * (n + 2 * i + 1));
    (==) {lemma_neg_assoc k (n + 2 * i + 1)}
    ((-k) * (n + 2 * i + 1));
    (==) {ML.distributivity_add_right (-k) n (2 * i + 1)}
    (-k) * n + (-k) * (2 * i + 1);
    (==) {ML.swap_mul (-k) n}
    n * (-k) + (-k) * (2 * i + 1);
    (==) {lemma_neg_distr k}
    n * ((-1) * k) + (-k) * (2 * i + 1);
    (==) {lemma_neg_assoc k (2 * i + 1)}
    n * ((-1) * k) + -k * (2 * i + 1);
  }

val intt_gs_kth_term_ok_split_sums_simpl_psi:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int{k >= 0 && k < n}
  -> i:nat{i < n / 2}
  -> Lemma (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1))
          == pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))
let intt_gs_kth_term_ok_split_sums_simpl_psi #n #psi f k i =
  assert (pow_mod_int_neg_one #q (-1) == (-1) % q);
  calc (==) {
    pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1));
    (==) {intt_gs_kth_term_ok_split_sums_simpl_psi_rearr_exp #n #psi f k i}
    pow_mod_int #q psi (n * ((-1) * k) + -k * (2 * i + 1));
    (==) {lemma_pow_mod_int_add #q psi (n * ((-1) * k)) (-k * (2 * i + 1))}
    pow_mod_int #q psi (n * ((-1) * k)) %* pow_mod_int #q psi (-k * (2 * i + 1));
    (==) {lemma_pow_mod_int_mul #q psi n ((-1) * k)}
    pow_mod_int #q (pow_mod_int #q psi n) ((-1) * k) %* pow_mod_int #q psi (-k * (2 * i + 1));
    (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
    pow_mod_int #q ((-1) % q) ((-1) * k) %* pow_mod_int #q psi (-k * (2 * i + 1));
    (==) {lemma_pow_mod_int_mul #q ((-1) % q) (-1) k}
    pow_mod_int #q (pow_mod_int ((-1) % q) (-1)) k %* pow_mod_int #q psi (-k * (2 * i + 1));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q (-1)}
    pow_mod_int #q (pow_mod_int_neg_one #q (-1)) k %* pow_mod_int #q psi (-k * (2 * i + 1));
    (==) {}
    pow_mod_int #q ((-1) % q) k %* pow_mod_int #q psi (-k * (2 * i + 1));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q k}
    pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1));
  }

val intt_gs_kth_term_ok_split_sums_t2:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int{k >= 0 && k < n}
  -> Lemma (sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1))))
        == sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))))
let intt_gs_kth_term_ok_split_sums_t2 #n #psi f k = 
  let aux (i:nat{i < n / 2}): Lemma ((poly_index f (i + n / 2)) %* (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))
                                  == (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))) =
    calc (==) {
      (poly_index f (i + n / 2)) %* (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)));
      (==) {intt_gs_kth_term_ok_split_sums_simpl_psi #n #psi f k i}
      (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)));
    } in
  Classical.forall_intro aux

val intt_gs_kth_term_ok_split_sums:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int{k >= 0 && k < n}
  -> Lemma (intt_kth_term_unscaled #n #psi f k 
         == (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
                            +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1))))))
let intt_gs_kth_term_ok_split_sums #n #psi f k =
  assert (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi ((-k) * (2 * i))))
      == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_lower f) i) (pow_mod_int #q psi ((-k) * (2 * i)))));
  assert (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi ((-k) * (2 * (i + n / 2)))))
      == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_upper f) i) (pow_mod_int #q psi ((-k) * (2 * (i + n / 2))))));
  calc (==) {
    intt_kth_term_unscaled #n #psi f k;
    (==) {}
    sum_of_zqs 0 n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
    (==) {lemma_sum_join 0 (n/2) n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))}
    (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
                            +% sum_of_zqs (n/2) n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1)))));
    (==) {intt_gs_kth_term_ok_split_sums_shift #n #psi f k}
    (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
                            +% sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))));
    (==) {intt_gs_kth_term_ok_split_sums_t2 #n #psi f k}
    (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
                            +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))));
  }

val intt_gs_kth_term_ok_even_t1:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k':int{k' >= 0 && k' < n / 2}
  -> Lemma (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k') * (2 * i + 1))))
          == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_lower f) i) (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))))
let intt_gs_kth_term_ok_even_t1 #n #psi f k' =
  let aux (i:nat{i < n / 2}): Lemma ((poly_index f i) %* (pow_mod_int #q psi (-(2*k') * (2 * i + 1)))
                                  == (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
    = 
    calc (==) {
      -(2*k') * (2 * i + 1);
      (==) {ML.neg_mul_right 2 k'}
      2 * (-k') * (2 * i + 1);
      (==) {ML.paren_mul_right 2 (-k') (2 * i + 1)}
      2 * ((-k') * (2 * i + 1));
      (==) {ML.neg_mul_left k' (2 * i + 1)}
      2 * (-k' * (2 * i + 1));
    };
    calc (==) {
      (poly_index f i) %* (pow_mod_int #q psi (-(2*k') * (2 * i + 1)));
      (==) {}
      (poly_index f i) %* (pow_mod_int #q psi (2 * (-k' * (2 * i + 1))));
      (==) {lemma_pow_mod_int_mul #q psi 2 (-k' * (2 * i + 1))}
      (poly_index f i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
      (==) {poly_lower_to_poly_idx #n f i}
      (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
    } in
  Classical.forall_intro aux

val intt_gs_kth_term_ok_even_t2:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k':int{k' >= 0 && k' < n / 2}
  -> Lemma (sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1))))
          == sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))))
let intt_gs_kth_term_ok_even_t2 #n #psi f k' =
  let aux (i:nat{i < n / 2}): Lemma ((poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)))
                                  == (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
    = 
    calc (==) {
      -(2*k') * (2 * i + 1);
      (==) {ML.neg_mul_right 2 k'}
      2 * (-k') * (2 * i + 1);
      (==) {ML.paren_mul_right 2 (-k') (2 * i + 1)}
      2 * ((-k') * (2 * i + 1));
      (==) {ML.neg_mul_left k' (2 * i + 1)}
      2 * (-k' * (2 * i + 1));
    };
    calc (==) {
      (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)));
      (==) {}
      (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (2 * (-k' * (2 * i + 1))));
      (==) {lemma_pow_mod_int_mul #q psi 2 (-k' * (2 * i + 1))}
      (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
      (==) {lemma_pow_mod_neg_one_eq_pow_mod #q (2*k')}
      (poly_index f (i + n / 2)) %* (pow_mod_int #q ((-1) % q) (2*k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
      (==) {lemma_pow_mod_int_mul #q ((-1) % q) 2 k'}
      (poly_index f (i + n / 2)) %* (pow_mod_int #q (pow_mod_int ((-1) % q) 2) k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
      (==) {lemma_pow_mod_neg_one_eq_pow_mod #q 2}
      (poly_index f (i + n / 2)) %* (pow_mod_int #q (pow_mod_int_neg_one 2) k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
      (==) {}
      (poly_index f (i + n / 2)) %* (pow_mod_int #q 1 k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
      (==) {lemma_pow_mod_int_one #q k'}
      (poly_index f (i + n / 2)) %* 1 %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
      (==) {poly_upper_to_poly_idx #n f i}
      (poly_index (poly_upper f) i) %* 1 %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
      (==) {poly_upper_to_poly_idx #n f i}
      (poly_index (poly_upper f) i) %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
    } in
  Classical.forall_intro aux

val intt_gs_kth_term_ok_even_t1_final:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k':int{k' >= 0 && k' < n / 2}
  -> Lemma (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
           (ensures sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
          == intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) k')
let intt_gs_kth_term_ok_even_t1_final #n #psi f k' = ()

val intt_gs_kth_term_ok_even_t2_final:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k':int{k' >= 0 && k' < n / 2}
  -> Lemma (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
           (ensures sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
          == intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) k')
let intt_gs_kth_term_ok_even_t2_final #n #psi f k' = ()

val intt_gs_kth_term_ok_even:
    #n:power_of_two{2 * n < q /\ n >= 2}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int{k % 2 = 0 /\ k >= 0 && k < n}
  -> Lemma 
      (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
      (ensures intt_kth_term_unscaled #n #psi f k == (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) (k/2)
                              +% intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) (k/2)))
let intt_gs_kth_term_ok_even #n #psi f k =
  let k' = k / 2 in
  assert (k = 2*k');
  assert (k' < n / 2);
  power_of_two_div_two n;
  nth_root_squared_is_primitive_root #q (2 * n) psi;
  calc (==) {
    intt_kth_term_unscaled #n #psi f k;
    (==) {}
    intt_kth_term_unscaled #n #psi f (2*k');
    (==) {intt_gs_kth_term_ok_split_sums #n #psi f (2*k')}
    (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k') * (2 * i + 1))))
                            +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)))));
    (==) {intt_gs_kth_term_ok_even_t1 #n #psi f k'}
    (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_lower f) i) (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
                            +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)))));
    (==) {intt_gs_kth_term_ok_even_t2 #n #psi f k'}
    (sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
                            +% sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))));
    (==) {intt_gs_kth_term_ok_even_t1_final #n #psi f k'}
    (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) k'
                            +% sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))));
    (==) {intt_gs_kth_term_ok_even_t2_final #n #psi f k'}
    (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) k'
                            +% intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) k');
  }

let lemma_rearrange_int (a b c d:int): Lemma (a + b + c + d == a + c + b + d) = ()
let lemma_neg_distributes (a b:int): Lemma (-(a + b) = (-a) + (-b)) = ()

val intt_gs_kth_term_ok_odd_simpl_psi:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k':int{k'>= 0 && k' < n / 2}
  -> i:nat{i < n / 2}
  -> Lemma
      (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
      (ensures (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1))) == pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1)))
let intt_gs_kth_term_ok_odd_simpl_psi #n #psi f k' i =
  calc (==) {
    (2*k'+1) * (2 * i + 1);
    (==) {ML.distributivity_add_right (2*k'+1) (2 * i) 1}
    ((2*k'+1) * (2 * i) + (2 * k' + 1));
    (==) {ML.distributivity_add_left (2*k') 1 (2 * i)}
    (((2*k') * (2 * i)) + (2 * i) + (2 * k' + 1));
    (==) {ML.paren_add_right (((2*k') * (2 * i)) + (2 * i)) (2 * k') 1}
    (((2*k') * (2 * i)) + (2 * i) + 2 * k' + 1);
    (==) {lemma_rearrange_int ((2*k') * (2 * i)) (2 * i) (2 * k') 1}
    (((2*k') * (2 * i)) + 2 * k' + 2 * i + 1);
    (==) {ML.distributivity_add_right (2*k') (2 * i) 1}
    ((2 * k') * (2 * i + 1) + 2 * i + 1);
    (==) {ML.paren_add_right ((2 * k') * (2 * i + 1)) (2 * i) 1}
    ((2 * k') * (2 * i + 1) + (2 * i + 1));
  };
  calc (==) {
    pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1));
    (==) {}
    pow_mod_int #q psi (-((2 * k') * (2 * i + 1) + (2 * i + 1)));
    (==) {lemma_neg_distributes ((2 * k') * (2 * i + 1)) (2 * i + 1)}
    pow_mod_int #q psi ((-(2 * k') * (2 * i + 1)) + (-(2 * i + 1)));
    (==) {lemma_pow_mod_int_add #q psi (-(2 * k') * (2 * i + 1)) (-(2 * i + 1))}
    pow_mod_int #q psi (-(2 * k') * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
    (==) {ML.neg_mul_left (2 * k') (2 * i + 1)}
    pow_mod_int #q psi ((-(2 * k')) * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
    (==) {ML.neg_mul_right 2 k'}
    pow_mod_int #q psi (2 * (-k') * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
    (==) {ML.paren_mul_right 2 (-k') (2 * i + 1)}
    pow_mod_int #q psi (2 * ((-k') * (2 * i + 1))) %* pow_mod_int #q psi (-(2 * i + 1));
    (==) {lemma_pow_mod_int_mul #q psi 2 ((-k') * (2 * i + 1))}
    pow_mod_int #q (pow_mod_int #q psi 2) ((-k') * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
    (==) {lemma_neg_assoc k' (2 * i + 1)}
    pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
  }

val intt_gs_kth_term_ok_odd_t1:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k':int{k'>= 0 && k' < n / 2}
  -> Lemma 
      (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
      (ensures sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1))))
              == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))))
let intt_gs_kth_term_ok_odd_t1 #n #psi f k' =
  let aux (i:nat{i < n / 2}): Lemma ((poly_index f i) %* (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))
                                  == (poly_index f i) %* (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))) =
    calc (==) {
      (poly_index f i) %* (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)));
      (==) {intt_gs_kth_term_ok_odd_simpl_psi #n #psi f k' i}
      (poly_index f i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1)));
    };
    admit() in
  admit()

val intt_gs_kth_term_ok_odd:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int{k % 2 = 1 /\ k >= 0 && k < n}
  -> Lemma 
      (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
      (ensures intt_kth_term_unscaled #n #psi f k == (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) (k/2)
                              -% intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) (k/2)))
let intt_gs_kth_term_ok_odd #n #psi f k =
  let k' = k / 2 in
  assert (k = 2*k'+1);
  assert (k' < n / 2);
  power_of_two_div_two n;
  nth_root_squared_is_primitive_root #q (2 * n) psi;
  calc (==) {
    intt_kth_term_unscaled #n #psi f k;
    (==) {}
    intt_kth_term_unscaled #n #psi f (2*k'+1);
    (==) {intt_gs_kth_term_ok_split_sums #n #psi f (2*k'+1)}
    (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1))))
                            +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k'+1) %* pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))));
  };
  admit()

val intt_gs_kth_term_ok:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> Lemma (intt_gs_kth_term #n #psi f k == intt_kth_term #n #psi f k)
let intt_gs_kth_term_ok #n #psi f k =
  if k < 0 || k >= n then ()
  else if n = 1 then intt_gs_kth_term_ok_base #n #psi f k
  else if k % 2 = 0 then intt_gs_kth_term_ok_even #n #psi f k
  else intt_gs_kth_term_ok_odd #n #psi f k