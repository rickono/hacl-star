module Hacl.Spec.NTT.Fast 

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

open Hacl.Spec.MLkem.NTT

(* 
In Cooley-Tukey, we compute the NTT of a n element polynomial by taking 
the NTT of the even and odd parts of the polynomial, and then combining 
them. This proof shows that splitting and recombining as Cooley-Tukey 
specifies matches the specification of the NTT that we have proven correct.
*)

val poly_even:
    #n:size_nat
  -> f:lpoly n
  -> lpoly (n / 2)
let poly_even #n f = createi (n / 2) (fun i -> poly_index #n f (2 * i))

val poly_even_to_poly_idx:
    #n:size_nat
  -> f:lpoly n
  -> i:nat{i < n / 2}
  -> Lemma (poly_index #n f (2 * i) == poly_index (poly_even #n f) i)
let poly_even_to_poly_idx #n f i = ()

val poly_odd:
    #n:size_nat
  -> f:lpoly n
  -> lpoly (n / 2)
let poly_odd #n f = createi (n / 2) (fun i -> poly_index #n f (2 * i + 1))

val poly_odd_to_poly_idx:
    #n:size_nat 
  -> f:lpoly n 
  -> i:nat{i < n / 2}
  -> Lemma (forall i. poly_index #n f (2 * i + 1) == poly_index (poly_odd #n f) i)
let poly_odd_to_poly_idx #n f i = ()

let power_of_two_div_two (n:power_of_two): Lemma (requires n >= 2) (ensures is_power_of_two (n / 2)) = admit()
let power_of_two_even (n:power_of_two): Lemma (requires n >= 2) (ensures n % 2 == 0) = ()

// The kth term of the NTT can be computed as a sum of two n/2 NTTs
// The same two n/2 NTTs can be used to compute the k+n/2th term
val ntt_ct_kth_term:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
  -> f:lpoly n
  -> k:int
  -> zq
let rec ntt_ct_kth_term #n #psi f k =
  if n = 1 then poly_index #n f k
  else if k < 0 || k >= n then 0 
  else if k < n / 2 then begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k
      +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k
  end else begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    let k' = k - n / 2 in  
    ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
      -% pow_mod_int #q psi (2 * k' + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k'
  end

// let ntt_ct (#n:power_of_two{2 * n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) =
//   createi n (fun k -> ntt_ct_kth_term #n #psi f k)

let rec ntt_ct (#n:power_of_two{2 * n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n): lpoly n =
  if n = 1 then f 
  else begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    let half_n:power_of_two = n / 2 in
    assert (half_n * 2 < q);
    let odds:lpoly (n/2) = poly_odd f in
    let evens:lpoly (n/2) = poly_even f in
    let omega:primitive_nth_root_of_unity_mod #q n = pow_mod #q psi 2 in
    let odd_ntt:lpoly (n/2) = ntt_ct #(half_n) #omega odds in
    let even_ntt:lpoly (n/2) = ntt_ct #(n/2) #omega evens in
    let term_twos:lpoly (n/2) = 
      createi (n/2) (fun k -> pow_mod_int #q psi (2 * k + 1) %* (poly_index #(n/2) odd_ntt k)) in
    createi n (fun k -> 
      if k < n / 2 then poly_index #(n/2) even_ntt k +% poly_index term_twos k
      else poly_index #(n/2) even_ntt (k - n / 2) -% poly_index term_twos (k - n / 2)
    )
  end

val ntt_ct_lemma_low (#n:power_of_two{2 * n < q && n >= 2}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (i:int{i >= 0 && i < n / 2}): 
  Lemma 
    (requires 
      is_power_of_two (n / 2) 
      /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod #q psi 2)
      /\ poly_index (ntt_ct #(n/2) #(pow_mod #q psi 2) (poly_even f)) i == ntt_ct_kth_term #(n/2) #(pow_mod #q psi 2) (poly_even f) i
      /\ poly_index (ntt_ct #(n/2) #(pow_mod #q psi 2) (poly_odd f)) i == ntt_ct_kth_term #(n/2) #(pow_mod #q psi 2) (poly_odd f) i)
    (ensures poly_index (ntt_ct #n #psi f) i == ntt_ct_kth_term #n #psi f i)
#push-options "--split_queries always"
let ntt_ct_lemma_low #n #psi f i = 
  assert (n >= 2);
  power_of_two_div_two n;
  assert (is_power_of_two (n / 2));
  nth_root_squared_is_primitive_root #q (2 * n) psi;
  let coefficient = poly_index (ntt_ct #n #psi f) i in
  let half_n:power_of_two = n / 2 in
  let odds:lpoly (n/2) = poly_odd f in
  let evens:lpoly (n/2) = poly_even f in
  let omega:primitive_nth_root_of_unity_mod #q n = pow_mod #q psi 2 in
  let odd_ntt:lpoly (n/2) = ntt_ct #(half_n) #omega odds in
  let even_ntt:lpoly (n/2) = ntt_ct #(n/2) #omega evens in
  let term_twos:lpoly (n/2) = 
    createi (n/2) (fun k -> pow_mod_int #q psi (2 * k + 1) %* (poly_index #(n/2) odd_ntt k)) in
  calc (==) {
    coefficient;
    (==) {}
    poly_index #(n/2) even_ntt i +% poly_index term_twos i;
  }
#pop-options

val ntt_ct_lemma_high (#n:power_of_two{2 * n < q && n >= 2}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (i:int{i >= n / 2 && i < n}): 
  Lemma 
    (requires 
      is_power_of_two (n / 2) 
      /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod #q psi 2)
      /\ poly_index (ntt_ct #(n/2) #(pow_mod #q psi 2) (poly_even f)) (i - n / 2) == ntt_ct_kth_term #(n/2) #(pow_mod #q psi 2) (poly_even f) (i - n / 2)
      /\ poly_index (ntt_ct #(n/2) #(pow_mod #q psi 2) (poly_odd f)) (i - n / 2) == ntt_ct_kth_term #(n/2) #(pow_mod #q psi 2) (poly_odd f) (i - n / 2))
    (ensures poly_index (ntt_ct #n #psi f) i == ntt_ct_kth_term #n #psi f i)
#push-options "--split_queries always"
let ntt_ct_lemma_high #n #psi f i = 
  assert (n >= 2);
  power_of_two_div_two n;
  assert (is_power_of_two (n / 2));
  nth_root_squared_is_primitive_root #q (2 * n) psi;
  let coefficient = poly_index (ntt_ct #n #psi f) i in
  let half_n:power_of_two = n / 2 in
  let odds:lpoly (n/2) = poly_odd f in
  let evens:lpoly (n/2) = poly_even f in
  let omega:primitive_nth_root_of_unity_mod #q n = pow_mod #q psi 2 in
  let odd_ntt:lpoly (n/2) = ntt_ct #(half_n) #omega odds in
  let even_ntt:lpoly (n/2) = ntt_ct #(n/2) #omega evens in
  let term_twos:lpoly (n/2) = 
    createi (n/2) (fun k -> pow_mod_int #q psi (2 * k + 1) %* (poly_index #(n/2) odd_ntt k)) in
  let k' = i - n / 2 in 
  calc (==) {
    coefficient;
    (==) {}
    poly_index #(n/2) even_ntt k' -% poly_index term_twos k';
  }
#pop-options

    val ntt_ct_lemma (#n:power_of_two{2 * n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (i:int): 
    Lemma (poly_index (ntt_ct #n #psi f) i == ntt_ct_kth_term #n #psi f i)
  [SMTPat (poly_index (ntt_ct #n #psi f) i)]
let rec ntt_ct_lemma #n #psi f i =
  if i < 0 || i >= n then ()
  else if n < 2 then () 
  else begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    let odds:lpoly (n/2) = poly_odd f in
    let evens:lpoly (n/2) = poly_even f in
    let omega:primitive_nth_root_of_unity_mod #q n = pow_mod #q psi 2 in
    if i < n / 2 then begin
      ntt_ct_lemma #(n/2) #omega odds i;
      ntt_ct_lemma #(n/2) #omega evens i;
      ntt_ct_lemma_low #n #psi f i
    end else begin
      ntt_ct_lemma #(n/2) #omega odds (i - n / 2);
      ntt_ct_lemma #(n/2) #omega evens (i - n / 2);
      ntt_ct_lemma_high #n #psi f i
    end
  end


val cooley_tukey_kth_term_ok_base:
    #n:power_of_two{n = 1}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k >= 0 && k < n}
  -> Lemma (ntt_kth_term #n #psi f k == ntt_ct_kth_term #n #psi f k)
let cooley_tukey_kth_term_ok_base #n #psi f k = 
  calc (==) {
    ntt_kth_term #n #psi f k;
    (==) {}
    sum_of_zqs 0 1 (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))));
    (==) {unfold_sum 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1)))); 
          lemma_sum_none 0 (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))))}
    (poly_index f 0) %* (pow_mod_int #q psi (0 * (2 * k + 1)));
    (==) {}
    (poly_index f 0) %* (pow_mod_int #q psi 0);
    (==) {lemma_pow_mod_int_pow0 psi}
    poly_index f 0;
    (==) {}
    ntt_ct_kth_term #n #psi f k;
  }

val cooley_tukey_kth_term_rewrite:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
            == sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))))
let cooley_tukey_kth_term_rewrite #n #psi f k = 
  let aux (j:nat{j < n / 2}): Lemma ((poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))) == 
                          ((poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))) = 
    poly_even_to_poly_idx f j in
  Classical.forall_intro (aux)

val cooley_tukey_kth_term_rewrite_odd:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1))))
            == sum_of_zqs 0 (n/2) (fun j -> (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))))
let cooley_tukey_kth_term_rewrite_odd #n #psi f k = 
  let aux (j:nat{j < n / 2}): Lemma ((poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1))) == 
                          (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))) = 
    calc (==) {
      (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1)));
      (==) {poly_odd_to_poly_idx f j}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1)));
      (==) {ML.distributivity_add_left (2 * j) 1 (2 * k + 1)}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1) + (2 * k + 1)));
      (==) {lemma_pow_mod_int_add #q psi ((2 * j) * (2 * k + 1)) (2 * k + 1)}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)) %* pow_mod_int #q psi (2 * k + 1));
      (==) {lemma_mul_mod_comm (pow_mod_int #q psi ((2 * j) * (2 * k + 1))) (pow_mod_int #q psi (2 * k + 1))}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi (2 * k + 1) %* pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
      (==) {lemma_mul_mod_assoc (poly_index (poly_odd f) j) (pow_mod_int #q psi (2 * k + 1)) (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))}
      (poly_index (poly_odd f) j) %* pow_mod_int #q psi (2 * k + 1) %* pow_mod_int #q psi ((2 * j) * (2 * k + 1));
    } in
  Classical.forall_intro (aux)

val cooley_tukey_kth_term_rewrite_odd_mul:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (sum_of_zqs 0 (n/2) (fun j -> (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
            == (pow_mod_int #q psi (2 * k + 1)) %* sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))))
let cooley_tukey_kth_term_rewrite_odd_mul #n #psi f k =
  sum_mul_lemma (pow_mod_int #q psi (2 * k + 1)) 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))

val lemma_collapse_ntt_half_even:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
        == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k)
let lemma_collapse_ntt_half_even #n #psi f k =
  let aux (j:nat{j < n/2}): Lemma ((poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))
                                == (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)))) =
    calc (==) {
      (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
      (==) {ML.paren_mul_right 2 j (2 * k +1)}
      (poly_index (poly_even f) j) %* (pow_mod_int #q psi (2 * (j * (2 * k + 1))));
      (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
      (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
    } in
  Classical.forall_intro (aux)
  
val lemma_collapse_ntt_half_odd:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
        == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let lemma_collapse_ntt_half_odd #n #psi f k =
  let aux (j:nat{j < n/2}): Lemma ((poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)))
                                == (poly_index (poly_odd f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)))) =
    calc (==) {
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
      (==) {ML.paren_mul_right 2 j (2 * k +1)}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q psi (2 * (j * (2 * k + 1))));
      (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
      (poly_index (poly_odd f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
    } in
  Classical.forall_intro (aux)

val cooley_tukey_kth_term_ok_rewrite:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures ntt_kth_term #n #psi f k == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
                                            +% pow_mod_int #q psi (2 * k + 1) 
                                              %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let cooley_tukey_kth_term_ok_rewrite #n #psi f k = 
  power_of_two_even n;
  calc (==) {
    ntt_kth_term #n #psi f k;
    (==) {}
    sum_of_zqs 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))));
    (==) {lemma_sum_split_parity n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * k + 1))))}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
      +% sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * k + 1))));
    (==) {cooley_tukey_kth_term_rewrite #n #psi f k;
          cooley_tukey_kth_term_rewrite_odd #n #psi f k}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
      +% sum_of_zqs 0 (n/2) (fun j -> (pow_mod_int #q psi (2 * k + 1)) %* (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
    (==) {cooley_tukey_kth_term_rewrite_odd_mul #n #psi f k}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))))
      +% (pow_mod_int #q psi (2 * k + 1)) %* sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
    (==) {lemma_collapse_ntt_half_even #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% (pow_mod_int #q psi (2 * k + 1)) %* sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_odd f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
    (==) {lemma_collapse_ntt_half_odd #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
  }

val ct_second_half_psi_sym_rearr_exp1:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma ((2 * j) * (2 * (k + n / 2) + 1)
          == (n * (2 * j)) + (2 * j * 2 * k) + (2 * j))
let ct_second_half_psi_sym_rearr_exp1 #n #psi k j = 
  calc (==) {
    ((2 * j) * (2 * (k + n / 2) + 1));
    (==) {}
    ((2 * j) * (2 * k + n + 1));
    (==) {ML.distributivity_add_right (2 * j) (2 * k + n) 1}
    ((2 * j) * (2 * k + n) + (2 * j));
    (==) {ML.distributivity_add_right (2 * j) (2 * k) n}
    ((2 * j) * (2 * k) + (2 * j) * n + (2 * j));
    (==) {ML.paren_mul_right (2 * j) 2 k}
    ((2 * j * 2 * k) + (2 * j * n) + (2 * j));
    (==) {ML.swap_mul (2 * j) n}
    ((2 * j * 2 * k) + (n * (2 * j)) + (2 * j));
    (==) {}
    ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j));
  }

#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
val ct_second_half_psi_sym_rearr_base:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma (pow_mod_int #q psi ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j))
            == (pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j))))
let ct_second_half_psi_sym_rearr_base #n #psi k j = 
  assert ((-1) % q = q - 1);
  calc (==) {
    pow_mod_int #q psi ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_add #q psi (n * (2 * j)) ((2 * j * 2 * k) + (2 * j))}
    pow_mod_int #q psi (n * (2 * j)) %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_mul #q psi n (2 * j)}
    pow_mod_int #q (pow_mod_int #q psi n) (2 * j) %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
    pow_mod_int #q ((-1) % q) (2 * j) %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_mul #q ((-1) % q) 2 j}
    pow_mod_int #q (pow_mod_int #q (q - 1) 2) j %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_neg_one_eq_pow_mod #q 2}
    pow_mod_int #q (pow_mod_int_neg_one #q 2) j %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {}
    pow_mod_int #q (1) j %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {lemma_pow_mod_int_one #q j}
    1 %* pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {}
    1 * pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j)) % q;
  }
  
// Symmetry of root of unity
#reset-options "--z3rlimit 20 --fuel 1 --ifuel 0"
val ct_second_half_psi_sym:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))
         == pow_mod_int #q psi ((2 * j) * (2 * k + 1)))
let ct_second_half_psi_sym #n #psi k j = 
  calc (==) {
    pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1));
    (==) {ct_second_half_psi_sym_rearr_exp1 #n #psi k j}
    pow_mod_int #q psi ((n * (2 * j)) + (2 * j * 2 * k) + (2 * j));
    (==) {ct_second_half_psi_sym_rearr_base #n #psi k j}
    pow_mod_int #q psi ((2 * j * 2 * k) + (2 * j));
    (==) {ML.paren_mul_right (2 * j) 2 k}
    pow_mod_int #q psi ((2 * j * (2 * k)) + (2 * j));
    (==) {ML.distributivity_add_right (2 * j) (2 * k) 1}
    pow_mod_int #q psi ((2 * j) * (2 * k + 1));
  }
  
val cooley_tukey_kth_term_ok_rewrite_second_half_t1_aux:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma ((poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)))
          == (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t1_aux #n #psi f k j = 
  ct_second_half_psi_sym #n #psi k j;
  poly_even_to_poly_idx #n f j;
  assert ((poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)))
        == (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1))));
  calc (==) {
    (poly_index (poly_even f) j) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
    (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
    (poly_index (poly_even f) j) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t1':
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))))
            == sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int (pow_mod_int #q psi 2) (j * (2 * k + 1)))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t1' #n #psi f k =
  Classical.forall_intro (cooley_tukey_kth_term_ok_rewrite_second_half_t1_aux #n #psi f k)

val cooley_tukey_kth_term_ok_rewrite_second_half_t1:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))))
            == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k)
let cooley_tukey_kth_term_ok_rewrite_second_half_t1 #n #psi f k =
  power_of_two_div_two n;
  nth_root_squared_is_primitive_root #q (2 * n) psi;
  calc (==) {
    sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))));
    (==) {cooley_tukey_kth_term_ok_rewrite_second_half_t1' #n #psi f k}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index (poly_even f) j) %* (pow_mod_int (pow_mod_int #q psi 2) (j * (2 * k + 1))));
    (==) {}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k;
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t2_aux:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> j:nat{j < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1)))
             == pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t2_aux #n #psi f k j = 
  assert (2 * (k + n / 2) = 2 * k + n);
  calc (==) {
    (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1)));
    (==) {ML.distributivity_add_left (2 * j) 1 (2 * k + n + 1)}
    (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1) + (2 * (k + n / 2) + 1)));
    (==) {lemma_pow_mod_int_add #q psi ((2 * j) * (2 * (k + n / 2) + 1)) (2 * (k + n / 2) + 1)}
    (pow_mod_int #q psi (2 * j * (2 * (k + n / 2) + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1));
  };
  assert ((poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1)))
        == (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1)));
  calc (==) {
    (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1));
    (==) {lemma_mul_mod_comm (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))) (pow_mod_int #q psi (2 * (k + n / 2) + 1))}
    (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))));
    (==) {lemma_mul_mod_assoc (poly_index f (2 * j + 1)) (pow_mod_int #q psi (2 * (k + n / 2) + 1)) (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)))}
    (poly_index f (2 * j + 1)) %* pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)));
    (==) {lemma_mul_mod_comm (poly_index f (2 * j + 1)) (pow_mod_int #q psi (2 * (k + n / 2) + 1))}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1)));
    (==) {ct_second_half_psi_sym #n #psi k j}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j) * (2 * k + 1)));
    (==) {ML.paren_mul_right 2 j (2 * k + 1)}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi (2 * (j * (2 * k + 1))));
    (==) {lemma_pow_mod_int_mul #q psi 2 (j * (2 * k + 1))}
    pow_mod_int #q psi (2 * (k + n / 2) + 1) %* (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)));
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t2':
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))))
            == pow_mod_int #q psi (2 * (k + n / 2) + 1) 
            %* sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1)))))
let cooley_tukey_kth_term_ok_rewrite_second_half_t2' #n #psi f k =
  Classical.forall_intro (Classical.move_requires (cooley_tukey_kth_term_ok_rewrite_second_half_t2_aux #n #psi f k));
  sum_mul_lemma (pow_mod_int #q psi (2 * (k + n / 2) + 1)) 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q (pow_mod_int #q psi 2) (j * (2 * k + 1))))

val psi_symmetry_negates:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> k:nat{k < n / 2}
  -> Lemma (pow_mod_int #q psi (2 * k + n + 1) == ((-1) % q) %* pow_mod_int #q psi (2 * k + 1))
let psi_symmetry_negates #n #psi k =
  calc (==) {
    pow_mod_int #q psi (2 * k + n + 1);
    (==) {}
    pow_mod_int #q psi (n + 2 * k + 1);
    (==) {lemma_pow_mod_int_add #q psi n (2 * k + 1)}
    pow_mod_int #q psi n %* pow_mod_int #q psi (2 * k + 1);
    (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
    ((-1) % q) %* pow_mod_int #q psi (2 * k + 1);
  }

val cooley_tukey_kth_term_ok_rewrite_second_half_t2:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))))
            == ((-1) % q) %* (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let cooley_tukey_kth_term_ok_rewrite_second_half_t2 #n #psi f k =
  cooley_tukey_kth_term_ok_rewrite_second_half_t2' #n #psi f k;
  psi_symmetry_negates #n #psi k

#reset-options "--z3rlimit 50 --fuel 1 --ifuel 1"
val neg_to_minus:
    a:zq
  -> b:zq
  -> Lemma (a +% ((-1) % q) %* b == a -% b)
let neg_to_minus a b =
  calc (==) {
    a +% ((-1) % q) %* b;
    (==) {}
    a +% (q - 1) %* b;
    (==) {}
    a +% ((q - 1) * b) % q;
    (==) {}
    a +% (b * q - b) % q;
  }

#reset-options "--z3rlimit 10 --fuel 1 --ifuel 0"
val cooley_tukey_kth_term_ok_rewrite_second_half:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat{k < n / 2}
  -> Lemma 
      (requires n >= 2 /\ is_power_of_two (n / 2) /\ is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2))
      (ensures ntt_kth_term #n #psi f (k + n / 2) == ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
                                                      -% pow_mod_int #q psi (2 * k + 1)
                                                          %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)
let cooley_tukey_kth_term_ok_rewrite_second_half #n #psi f k = 
  power_of_two_even n;
  calc (==) {
    ntt_kth_term #n #psi f (k + n / 2);
    (==) {}
    sum_of_zqs 0 n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * (k + n / 2) + 1))));
    (==) {lemma_sum_split_parity n (fun j -> mul_zq (poly_index f j) (pow_mod_int #q psi (j * (2 * (k + n / 2) + 1))))}
    sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j)) %* (pow_mod_int #q psi ((2 * j) * (2 * (k + n / 2) + 1))))
      +% sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))));
    (==) {cooley_tukey_kth_term_ok_rewrite_second_half_t1 #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% sum_of_zqs 0 (n/2) (fun j -> (poly_index f (2 * j + 1)) %* (pow_mod_int #q psi ((2 * j + 1) * (2 * (k + n / 2) + 1))));
    (==) {cooley_tukey_kth_term_ok_rewrite_second_half_t2 #n #psi f k}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      +% ((-1) % q) %* (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
    (==) {neg_to_minus (ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k)
                       ((pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k)}
    ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
      -% pow_mod_int #q psi (2 * k + 1) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
  }


val cooley_tukey_kth_term_ok:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (ntt_kth_term #n #psi f k == ntt_ct_kth_term #n #psi f k)
let rec cooley_tukey_kth_term_ok #n #psi f k =
  if k < 0 || k >= n then ()
  else if n = 1 then cooley_tukey_kth_term_ok_base #n #psi f k
  else if k < n / 2 then begin 
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    calc (==) {
      ntt_ct_kth_term #n #psi f k;
      (==) {}
      ntt_ct_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
        +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_even f) k}
      ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
        +% pow_mod_int #q psi (2 * k + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_odd f) k}
      ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_even f) k
        +% (pow_mod_int #q psi (2 * k + 1)) %* ntt_kth_term #(n / 2) #(pow_mod_int #q psi 2) (poly_odd f) k;
      (==) {cooley_tukey_kth_term_ok_rewrite #n #psi f k}
      ntt_kth_term #n #psi f k;
    }
  end else begin 
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    let k' = k - n / 2 in
    calc (==) {
      ntt_ct_kth_term #n #psi f k;
      (==) {}
      ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
        -% pow_mod_int #q psi (2 * k' + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k';
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_even f) k'}
      ntt_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
        -% pow_mod_int #q psi (2 * k' + 1) %* ntt_ct_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k';
      (==) {cooley_tukey_kth_term_ok #(n/2) #(pow_mod_int #q psi 2) (poly_odd f) k'}
      ntt_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_even f) k'
        -% pow_mod_int #q psi (2 * k' + 1) %* ntt_kth_term #(n / 2) #(pow_mod #q psi 2) (poly_odd f) k';
      (==) {cooley_tukey_kth_term_ok_rewrite_second_half #n #psi f k'}
      ntt_kth_term #n #psi f k;
    }
  end

val cooley_tukey_kth_term_lemma:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> k:nat
  -> Lemma (ntt_kth_term #n #psi f k == poly_index (ntt_ct #n #psi f) k)
let cooley_tukey_kth_term_lemma #n #psi f k =
  calc (==) {
    ntt_kth_term #n #psi f k;
    (==) {cooley_tukey_kth_term_ok #n #psi f k}
    ntt_ct_kth_term #n #psi f k;
    (==) {ntt_ct_lemma #n #psi f k}
    poly_index (ntt_ct #n #psi f) k;
  }

val cooley_tukey_ok:
    #n:power_of_two{2 * n < q}
  -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
  -> f:lpoly n
  -> Lemma (equal (ntt #n #psi f) (ntt_ct #n #psi f))
let cooley_tukey_ok #n #psi f = 
  Classical.forall_intro (cooley_tukey_kth_term_lemma #n #psi f)


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

let rec intt_gs (#n:power_of_two{2 * n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n): lpoly n =
  if n = 1 then f 
  else begin
    power_of_two_div_two n;
    nth_root_squared_is_primitive_root #q (2 * n) psi;
    let half_n:power_of_two = n / 2 in
    assert (half_n * 2 < q);
    let low:lpoly (n/2) = poly_lower f in
    let high:lpoly (n/2) = poly_upper f in
    let omega:primitive_nth_root_of_unity_mod #q n = pow_mod #q psi 2 in
    let low_ntt:lpoly (n/2) = intt_gs #(half_n) #omega low in
    let high_ntt:lpoly (n/2) = intt_gs #(n/2) #omega high in
    let term_twos:lpoly (n/2) = 
      createi (n/2) (fun k -> poly_index #(n/2) high_ntt (k / 2) %* pow_mod_int #q psi (-2 * k)) in
    createi n (fun k -> 
      if k % 2 = 0 then poly_index #(n/2) low_ntt k +% poly_index term_twos k
      else poly_index #(n/2) low_ntt (k - n / 2) -% poly_index term_twos (k - n / 2)
    )
  end

// val intt_kth_term_unscaled:
//     #n:power_of_two{n < q}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int
//   -> zq
// let intt_kth_term_unscaled #n #psi f k =
//   if k < 0 || k >= n then 0
//   else sum_of_zqs 0 n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))

// let lemma_scale_intt_unscaled (#n:power_of_two{n < q}) (#psi:primitive_nth_root_of_unity_mod #q (2 * n)) (f:lpoly n) (k:int): 
//   Lemma (intt_kth_term #n #psi f k == pow_mod_int #q n (-1) %* intt_kth_term_unscaled #n #psi f k)
//   = ()

// val intt_gs_kth_term_ok_base:
//     #n:power_of_two{n = 1}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2*n)
//   -> f:lpoly n
//   -> k:nat{k >= 0 && k < n}
//   -> Lemma (intt_kth_term #n #psi f k == intt_gs_kth_term #n #psi f k)
// let intt_gs_kth_term_ok_base #n #psi f k =
//   assert (k = 0);
//   calc (==) {
//     intt_kth_term #n #psi f k;
//     (==) {}
//     pow_mod_int #q 1 (-1) %* sum_of_zqs 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
//     (==) {lemma_pow_mod_int_one #q (-1)}
//     1 %* sum_of_zqs 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
//     (==) {}
//     sum_of_zqs 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
//     (==) {unfold_sum 0 1 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))}
//     sum_of_zqs 0 0 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1)))) +% mul_zq (poly_index f 0) (pow_mod_int #q psi (-k * (2 * 0 + 1)));
//     (==) {lemma_sum_none 0 (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))}
//     0 +% mul_zq (poly_index f 0) (pow_mod_int #q psi (-k * (2 * 0 + 1)));
//     (==) {}
//     mul_zq (poly_index f 0) (pow_mod_int #q psi (-0));
//     (==) {}
//     mul_zq (poly_index f 0) (pow_mod_int #q psi (0));
//     (==) {lemma_pow_mod_int_pow0 #q psi}
//     (poly_index f 0);
//     (==) {}
//     intt_gs_kth_term #n #psi f k;
//   }

// val intt_gs_kth_term_ok_split_sums_shift:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int{k >= 0 && k < n}
//   -> Lemma (sum_of_zqs (n/2) n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
//         == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))))
// let intt_gs_kth_term_ok_split_sums_shift #n #psi f k =
//   let f1 = (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))) in
//   let f2 = (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1)))) in
//   lemma_sum_shift 0 (n / 2) (n / 2) f1 f2

// let lemma_neg_assoc (a b:int): Lemma (-a * b == (-a) * b) = ()
// let lemma_neg_distr (a:int): Lemma (-a == (-1) * a) = ()

// val intt_gs_kth_term_ok_split_sums_simpl_psi_rearr_exp:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int{k >= 0 && k < n}
//   -> i:nat{i < n / 2}
//   -> Lemma (-k * (2 * (i + n / 2) + 1)
//           == n * ((-1) * k) + -k * (2 * i + 1))
// let intt_gs_kth_term_ok_split_sums_simpl_psi_rearr_exp #n #psi f k i =
//   calc (==) {
//     (-k * (2 * (i + n / 2) + 1));
//     (==) {}
//     (-k * (2 * i + n + 1));
//     (==) {}
//     (-k * (n + 2 * i + 1));
//     (==) {lemma_neg_assoc k (n + 2 * i + 1)}
//     ((-k) * (n + 2 * i + 1));
//     (==) {ML.distributivity_add_right (-k) n (2 * i + 1)}
//     (-k) * n + (-k) * (2 * i + 1);
//     (==) {ML.swap_mul (-k) n}
//     n * (-k) + (-k) * (2 * i + 1);
//     (==) {lemma_neg_distr k}
//     n * ((-1) * k) + (-k) * (2 * i + 1);
//     (==) {lemma_neg_assoc k (2 * i + 1)}
//     n * ((-1) * k) + -k * (2 * i + 1);
//   }

// val intt_gs_kth_term_ok_split_sums_simpl_psi:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int{k >= 0 && k < n}
//   -> i:nat{i < n / 2}
//   -> Lemma (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1))
//           == pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))
// let intt_gs_kth_term_ok_split_sums_simpl_psi #n #psi f k i =
//   assert (pow_mod_int_neg_one #q (-1) == (-1) % q);
//   calc (==) {
//     pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1));
//     (==) {intt_gs_kth_term_ok_split_sums_simpl_psi_rearr_exp #n #psi f k i}
//     pow_mod_int #q psi (n * ((-1) * k) + -k * (2 * i + 1));
//     (==) {lemma_pow_mod_int_add #q psi (n * ((-1) * k)) (-k * (2 * i + 1))}
//     pow_mod_int #q psi (n * ((-1) * k)) %* pow_mod_int #q psi (-k * (2 * i + 1));
//     (==) {lemma_pow_mod_int_mul #q psi n ((-1) * k)}
//     pow_mod_int #q (pow_mod_int #q psi n) ((-1) * k) %* pow_mod_int #q psi (-k * (2 * i + 1));
//     (==) {lemma_primitive_unity_half_n #q #(2*n) psi}
//     pow_mod_int #q ((-1) % q) ((-1) * k) %* pow_mod_int #q psi (-k * (2 * i + 1));
//     (==) {lemma_pow_mod_int_mul #q ((-1) % q) (-1) k}
//     pow_mod_int #q (pow_mod_int ((-1) % q) (-1)) k %* pow_mod_int #q psi (-k * (2 * i + 1));
//     (==) {lemma_pow_mod_neg_one_eq_pow_mod #q (-1)}
//     pow_mod_int #q (pow_mod_int_neg_one #q (-1)) k %* pow_mod_int #q psi (-k * (2 * i + 1));
//     (==) {}
//     pow_mod_int #q ((-1) % q) k %* pow_mod_int #q psi (-k * (2 * i + 1));
//     (==) {lemma_pow_mod_neg_one_eq_pow_mod #q k}
//     pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1));
//   }

// val intt_gs_kth_term_ok_split_sums_t2:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int{k >= 0 && k < n}
//   -> Lemma (sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1))))
//         == sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))))
// let intt_gs_kth_term_ok_split_sums_t2 #n #psi f k = 
//   let aux (i:nat{i < n / 2}): Lemma ((poly_index f (i + n / 2)) %* (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))
//                                   == (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))) =
//     calc (==) {
//       (poly_index f (i + n / 2)) %* (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)));
//       (==) {intt_gs_kth_term_ok_split_sums_simpl_psi #n #psi f k i}
//       (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)));
//     } in
//   Classical.forall_intro aux

// val intt_gs_kth_term_ok_split_sums:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int{k >= 0 && k < n}
//   -> Lemma (intt_kth_term_unscaled #n #psi f k 
//          == (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
//                             +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1))))))
// let intt_gs_kth_term_ok_split_sums #n #psi f k =
//   assert (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi ((-k) * (2 * i))))
//       == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_lower f) i) (pow_mod_int #q psi ((-k) * (2 * i)))));
//   assert (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi ((-k) * (2 * (i + n / 2)))))
//       == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_upper f) i) (pow_mod_int #q psi ((-k) * (2 * (i + n / 2))))));
//   calc (==) {
//     intt_kth_term_unscaled #n #psi f k;
//     (==) {}
//     sum_of_zqs 0 n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))));
//     (==) {lemma_sum_join 0 (n/2) n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))}
//     (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
//                             +% sum_of_zqs (n/2) n (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1)))));
//     (==) {intt_gs_kth_term_ok_split_sums_shift #n #psi f k}
//     (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
//                             +% sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f (i + n / 2)) (pow_mod_int #q psi (-k * (2 * (i + n / 2) + 1)))));
//     (==) {intt_gs_kth_term_ok_split_sums_t2 #n #psi f k}
//     (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-k * (2 * i + 1))))
//                             +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q k %* pow_mod_int #q psi (-k * (2 * i + 1)))));
//   }

// val intt_gs_kth_term_ok_even_t1:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k':int{k' >= 0 && k' < n / 2}
//   -> Lemma (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k') * (2 * i + 1))))
//           == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_lower f) i) (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))))
// let intt_gs_kth_term_ok_even_t1 #n #psi f k' =
//   let aux (i:nat{i < n / 2}): Lemma ((poly_index f i) %* (pow_mod_int #q psi (-(2*k') * (2 * i + 1)))
//                                   == (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
//     = 
//     calc (==) {
//       -(2*k') * (2 * i + 1);
//       (==) {ML.neg_mul_right 2 k'}
//       2 * (-k') * (2 * i + 1);
//       (==) {ML.paren_mul_right 2 (-k') (2 * i + 1)}
//       2 * ((-k') * (2 * i + 1));
//       (==) {ML.neg_mul_left k' (2 * i + 1)}
//       2 * (-k' * (2 * i + 1));
//     };
//     calc (==) {
//       (poly_index f i) %* (pow_mod_int #q psi (-(2*k') * (2 * i + 1)));
//       (==) {}
//       (poly_index f i) %* (pow_mod_int #q psi (2 * (-k' * (2 * i + 1))));
//       (==) {lemma_pow_mod_int_mul #q psi 2 (-k' * (2 * i + 1))}
//       (poly_index f i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
//       (==) {poly_lower_to_poly_idx #n f i}
//       (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
//     } in
//   Classical.forall_intro aux

// val intt_gs_kth_term_ok_even_t2:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k':int{k' >= 0 && k' < n / 2}
//   -> Lemma (sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1))))
//           == sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))))
// let intt_gs_kth_term_ok_even_t2 #n #psi f k' =
//   let aux (i:nat{i < n / 2}): Lemma ((poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)))
//                                   == (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
//     = 
//     calc (==) {
//       -(2*k') * (2 * i + 1);
//       (==) {ML.neg_mul_right 2 k'}
//       2 * (-k') * (2 * i + 1);
//       (==) {ML.paren_mul_right 2 (-k') (2 * i + 1)}
//       2 * ((-k') * (2 * i + 1));
//       (==) {ML.neg_mul_left k' (2 * i + 1)}
//       2 * (-k' * (2 * i + 1));
//     };
//     calc (==) {
//       (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)));
//       (==) {}
//       (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (2 * (-k' * (2 * i + 1))));
//       (==) {lemma_pow_mod_int_mul #q psi 2 (-k' * (2 * i + 1))}
//       (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
//       (==) {lemma_pow_mod_neg_one_eq_pow_mod #q (2*k')}
//       (poly_index f (i + n / 2)) %* (pow_mod_int #q ((-1) % q) (2*k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)));
//       (==) {lemma_pow_mod_int_mul #q ((-1) % q) 2 k'}
//       (poly_index f (i + n / 2)) %* (pow_mod_int #q (pow_mod_int ((-1) % q) 2) k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
//       (==) {lemma_pow_mod_neg_one_eq_pow_mod #q 2}
//       (poly_index f (i + n / 2)) %* (pow_mod_int #q (pow_mod_int_neg_one 2) k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
//       (==) {}
//       (poly_index f (i + n / 2)) %* (pow_mod_int #q 1 k') %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
//       (==) {lemma_pow_mod_int_one #q k'}
//       (poly_index f (i + n / 2)) %* 1 %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
//       (==) {poly_upper_to_poly_idx #n f i}
//       (poly_index (poly_upper f) i) %* 1 %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
//       (==) {poly_upper_to_poly_idx #n f i}
//       (poly_index (poly_upper f) i) %* pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1));
//     } in
//   Classical.forall_intro aux

// val intt_gs_kth_term_ok_even_t1_final:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k':int{k' >= 0 && k' < n / 2}
//   -> Lemma (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
//            (ensures sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
//           == intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) k')
// let intt_gs_kth_term_ok_even_t1_final #n #psi f k' = ()

// val intt_gs_kth_term_ok_even_t2_final:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k':int{k' >= 0 && k' < n / 2}
//   -> Lemma (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
//            (ensures sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
//           == intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) k')
// let intt_gs_kth_term_ok_even_t2_final #n #psi f k' = ()

// val intt_gs_kth_term_ok_even:
//     #n:power_of_two{2 * n < q /\ n >= 2}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int{k % 2 = 0 /\ k >= 0 && k < n}
//   -> Lemma 
//       (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
//       (ensures intt_kth_term_unscaled #n #psi f k == (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) (k/2)
//                               +% intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) (k/2)))
// let intt_gs_kth_term_ok_even #n #psi f k =
//   let k' = k / 2 in
//   assert (k = 2*k');
//   assert (k' < n / 2);
//   power_of_two_div_two n;
//   nth_root_squared_is_primitive_root #q (2 * n) psi;
//   calc (==) {
//     intt_kth_term_unscaled #n #psi f k;
//     (==) {}
//     intt_kth_term_unscaled #n #psi f (2*k');
//     (==) {intt_gs_kth_term_ok_split_sums #n #psi f (2*k')}
//     (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k') * (2 * i + 1))))
//                             +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)))));
//     (==) {intt_gs_kth_term_ok_even_t1 #n #psi f k'}
//     (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index (poly_lower f) i) (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
//                             +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k') %* pow_mod_int #q psi (-(2*k') * (2 * i + 1)))));
//     (==) {intt_gs_kth_term_ok_even_t2 #n #psi f k'}
//     (sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_lower f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1))))
//                             +% sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))));
//     (==) {intt_gs_kth_term_ok_even_t1_final #n #psi f k'}
//     (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) k'
//                             +% sum_of_zqs 0 (n/2) (fun i -> (poly_index (poly_upper f) i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)))));
//     (==) {intt_gs_kth_term_ok_even_t2_final #n #psi f k'}
//     (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) k'
//                             +% intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) k');
//   }

// let lemma_rearrange_int (a b c d:int): Lemma (a + b + c + d == a + c + b + d) = ()
// let lemma_neg_distributes (a b:int): Lemma (-(a + b) = (-a) + (-b)) = ()

// val intt_gs_kth_term_ok_odd_simpl_psi:
//     #n:power_of_two{2 * n < q}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k':int{k'>= 0 && k' < n / 2}
//   -> i:nat{i < n / 2}
//   -> Lemma
//       (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
//       (ensures (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1))) == pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1)))
// let intt_gs_kth_term_ok_odd_simpl_psi #n #psi f k' i =
//   calc (==) {
//     (2*k'+1) * (2 * i + 1);
//     (==) {ML.distributivity_add_right (2*k'+1) (2 * i) 1}
//     ((2*k'+1) * (2 * i) + (2 * k' + 1));
//     (==) {ML.distributivity_add_left (2*k') 1 (2 * i)}
//     (((2*k') * (2 * i)) + (2 * i) + (2 * k' + 1));
//     (==) {ML.paren_add_right (((2*k') * (2 * i)) + (2 * i)) (2 * k') 1}
//     (((2*k') * (2 * i)) + (2 * i) + 2 * k' + 1);
//     (==) {lemma_rearrange_int ((2*k') * (2 * i)) (2 * i) (2 * k') 1}
//     (((2*k') * (2 * i)) + 2 * k' + 2 * i + 1);
//     (==) {ML.distributivity_add_right (2*k') (2 * i) 1}
//     ((2 * k') * (2 * i + 1) + 2 * i + 1);
//     (==) {ML.paren_add_right ((2 * k') * (2 * i + 1)) (2 * i) 1}
//     ((2 * k') * (2 * i + 1) + (2 * i + 1));
//   };
//   calc (==) {
//     pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1));
//     (==) {}
//     pow_mod_int #q psi (-((2 * k') * (2 * i + 1) + (2 * i + 1)));
//     (==) {lemma_neg_distributes ((2 * k') * (2 * i + 1)) (2 * i + 1)}
//     pow_mod_int #q psi ((-(2 * k') * (2 * i + 1)) + (-(2 * i + 1)));
//     (==) {lemma_pow_mod_int_add #q psi (-(2 * k') * (2 * i + 1)) (-(2 * i + 1))}
//     pow_mod_int #q psi (-(2 * k') * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
//     (==) {ML.neg_mul_left (2 * k') (2 * i + 1)}
//     pow_mod_int #q psi ((-(2 * k')) * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
//     (==) {ML.neg_mul_right 2 k'}
//     pow_mod_int #q psi (2 * (-k') * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
//     (==) {ML.paren_mul_right 2 (-k') (2 * i + 1)}
//     pow_mod_int #q psi (2 * ((-k') * (2 * i + 1))) %* pow_mod_int #q psi (-(2 * i + 1));
//     (==) {lemma_pow_mod_int_mul #q psi 2 ((-k') * (2 * i + 1))}
//     pow_mod_int #q (pow_mod_int #q psi 2) ((-k') * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
//     (==) {lemma_neg_assoc k' (2 * i + 1)}
//     pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1));
//   }

// val intt_gs_kth_term_ok_odd_t1:
//     #n:power_of_two{2 * n < q}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k':int{k'>= 0 && k' < n / 2}
//   -> Lemma 
//       (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
//       (ensures sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1))))
//               == sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))))
// let intt_gs_kth_term_ok_odd_t1 #n #psi f k' =
//   let aux (i:nat{i < n / 2}): Lemma ((poly_index f i) %* (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))
//                                   == (poly_index f i) %* (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))) =
//     calc (==) {
//       (poly_index f i) %* (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)));
//       (==) {intt_gs_kth_term_ok_odd_simpl_psi #n #psi f k' i}
//       (poly_index f i) %* (pow_mod_int #q (pow_mod_int #q psi 2) (-k' * (2 * i + 1)) %* pow_mod_int #q psi (-(2 * i + 1)));
//     };
//     admit() in
//   admit()

// val intt_gs_kth_term_ok_odd:
//     #n:power_of_two{2 * n < q}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int{k % 2 = 1 /\ k >= 0 && k < n}
//   -> Lemma 
//       (requires is_primitive_nth_root_of_unity_mod #q n (pow_mod_int #q psi 2) /\ is_power_of_two (n / 2))
//       (ensures intt_kth_term_unscaled #n #psi f k == (intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_lower f) (k/2)
//                               -% intt_kth_term_unscaled #(n/2) #(pow_mod_int #q psi 2) (poly_upper f) (k/2)))
// let intt_gs_kth_term_ok_odd #n #psi f k =
//   let k' = k / 2 in
//   assert (k = 2*k'+1);
//   assert (k' < n / 2);
//   power_of_two_div_two n;
//   nth_root_squared_is_primitive_root #q (2 * n) psi;
//   calc (==) {
//     intt_kth_term_unscaled #n #psi f k;
//     (==) {}
//     intt_kth_term_unscaled #n #psi f (2*k'+1);
//     (==) {intt_gs_kth_term_ok_split_sums #n #psi f (2*k'+1)}
//     (sum_of_zqs 0 (n/2) (fun i -> mul_zq (poly_index f i) (pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1))))
//                             +% sum_of_zqs 0 (n/2) (fun i -> (poly_index f (i + n / 2)) %* (pow_mod_int_neg_one #q (2*k'+1) %* pow_mod_int #q psi (-(2*k'+1) * (2 * i + 1)))));
//   };
//   admit()

// val intt_gs_kth_term_ok:
//     #n:power_of_two{2 * n < q}
//   -> #psi:primitive_nth_root_of_unity_mod #q (2 * n)
//   -> f:lpoly n
//   -> k:int
//   -> Lemma (intt_gs_kth_term #n #psi f k == intt_kth_term #n #psi f k)
// let intt_gs_kth_term_ok #n #psi f k =
//   if k < 0 || k >= n then ()
//   else if n = 1 then intt_gs_kth_term_ok_base #n #psi f k
//   else if k % 2 = 0 then intt_gs_kth_term_ok_even #n #psi f k
//   else intt_gs_kth_term_ok_odd #n #psi f k