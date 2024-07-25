open Prims
let (max : Prims.int -> Prims.int -> Prims.int) = FStar_Math_Lib.max
type 'n is_power_of_two = unit
type power_of_two = Prims.nat
let (mul_quotient_ring_kth_term :
  power_of_two ->
    unit Hacl_Spec_MLkem_Poly.lpoly ->
      unit Hacl_Spec_MLkem_Poly.lpoly -> Prims.int -> Hacl_Spec_MLkem_Zq.zq)
  =
  fun n ->
    fun f ->
      fun g ->
        fun k ->
          if (k < Prims.int_zero) || (k >= n)
          then Prims.int_zero
          else
            Hacl_Spec_MLkem_Sums.sum_of_zqs Prims.int_zero n
              (fun j ->
                 Hacl_Spec_MLkem_Zq.mul_zq
                   (Hacl_Spec_MLkem_PowModInt.pow_mod_int_neg_one
                      Hacl_Spec_MLkem_Zq.q ((k - j) / n))
                   (Hacl_Spec_MLkem_Zq.mul_zq
                      (Hacl_Spec_MLkem_Poly.poly_index n f j)
                      (Hacl_Spec_MLkem_Poly.poly_index n g ((k - j) mod n))))
let (mul_quotient_ring :
  power_of_two ->
    unit Hacl_Spec_MLkem_Poly.lpoly ->
      unit Hacl_Spec_MLkem_Poly.lpoly -> unit Hacl_Spec_MLkem_Poly.lpoly)
  =
  fun n ->
    fun f ->
      fun g ->
        Lib_Sequence.createi n (fun k -> mul_quotient_ring_kth_term n f g k)
let (ntt_kth_term :
  power_of_two ->
    (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod ->
      unit Hacl_Spec_MLkem_Poly.lpoly -> Prims.int -> Hacl_Spec_MLkem_Zq.zq)
  =
  fun n ->
    fun psi ->
      fun f ->
        fun k ->
          if (k < Prims.int_zero) || (k >= n)
          then Prims.int_zero
          else
            Hacl_Spec_MLkem_Sums.sum_of_zqs Prims.int_zero n
              (fun j ->
                 Hacl_Spec_MLkem_Zq.mul_zq
                   (Hacl_Spec_MLkem_Poly.poly_index n f j)
                   (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                      Hacl_Spec_MLkem_Zq.q psi
                      (j * (((Prims.of_int (2)) * k) + Prims.int_one))))
let (ntt :
  power_of_two ->
    (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod ->
      unit Hacl_Spec_MLkem_Poly.lpoly ->
        (Hacl_Spec_MLkem_Zq.zq, unit) Lib_Sequence.lseq)
  =
  fun n ->
    fun psi ->
      fun f -> Lib_Sequence.createi n (fun k -> ntt_kth_term n psi f k)
let (intt_kth_term :
  power_of_two ->
    (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod ->
      unit Hacl_Spec_MLkem_Poly.lpoly -> Prims.int -> Hacl_Spec_MLkem_Zq.zq)
  =
  fun n ->
    fun psi ->
      fun f ->
        fun k ->
          if (k < Prims.int_zero) || (k >= n)
          then Prims.int_zero
          else
            Hacl_Spec_MLkem_Zq.mul_zq
              (Hacl_Spec_MLkem_PowModInt.pow_mod_int Hacl_Spec_MLkem_Zq.q n
                 (Prims.of_int (-1)))
              (Hacl_Spec_MLkem_Sums.sum_of_zqs Prims.int_zero n
                 (fun i ->
                    Hacl_Spec_MLkem_Zq.mul_zq
                      (Hacl_Spec_MLkem_Poly.poly_index n f i)
                      (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                         Hacl_Spec_MLkem_Zq.q psi
                         (- (k * (((Prims.of_int (2)) * i) + Prims.int_one))))))
let (intt :
  power_of_two ->
    (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod ->
      unit Hacl_Spec_MLkem_Poly.lpoly ->
        (Hacl_Spec_MLkem_Zq.zq, unit) Lib_Sequence.lseq)
  =
  fun n ->
    fun psi ->
      fun f -> Lib_Sequence.createi n (fun k -> intt_kth_term n psi f k)
let (intt_ntt_kth_term :
  power_of_two ->
    (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod ->
      unit Hacl_Spec_MLkem_Poly.lpoly -> Prims.nat -> Hacl_Spec_MLkem_Zq.zq)
  =
  fun n ->
    fun psi ->
      fun f -> fun k -> Lib_Sequence.index n (intt n psi (ntt n psi f)) k
let (mul_componentwise :
  power_of_two ->
    unit Hacl_Spec_MLkem_Poly.lpoly ->
      unit Hacl_Spec_MLkem_Poly.lpoly ->
        (Hacl_Spec_MLkem_Zq.zq, unit) Lib_Sequence.lseq)
  =
  fun n ->
    fun f ->
      fun g ->
        Lib_Sequence.createi n
          (fun i ->
             Hacl_Spec_MLkem_Zq.mul_zq
               (Hacl_Spec_MLkem_Poly.poly_index n f i)
               (Hacl_Spec_MLkem_Poly.poly_index n g i))