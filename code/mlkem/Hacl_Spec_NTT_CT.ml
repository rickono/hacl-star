open Prims
let (max : Prims.int -> Prims.int -> Prims.int) = FStar_Math_Lib.max
let (poly_even :
  Prims.nat ->
    unit Hacl_Spec_MLkem_Poly.lpoly -> unit Hacl_Spec_MLkem_Poly.lpoly)
  =
  fun n ->
    fun f ->
      Lib_Sequence.createi (n / (Prims.of_int (2)))
        (fun i ->
           Hacl_Spec_MLkem_Poly.poly_index n f ((Prims.of_int (2)) * i))
let (poly_odd :
  Prims.nat ->
    unit Hacl_Spec_MLkem_Poly.lpoly -> unit Hacl_Spec_MLkem_Poly.lpoly)
  =
  fun n ->
    fun f ->
      Lib_Sequence.createi (n / (Prims.of_int (2)))
        (fun i ->
           Hacl_Spec_MLkem_Poly.poly_index n f
             (((Prims.of_int (2)) * i) + Prims.int_one))
let rec (ntt_ct_kth_term :
  Hacl_Spec_MLkem_NTT.power_of_two ->
    (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod ->
      unit Hacl_Spec_MLkem_Poly.lpoly -> Prims.int -> Hacl_Spec_MLkem_Zq.zq)
  =
  fun n ->
    fun psi ->
      fun f ->
        fun k ->
          if n = Prims.int_one
          then Hacl_Spec_MLkem_Poly.poly_index n f k
          else
            if (k < Prims.int_zero) || (k >= n)
            then Prims.int_zero
            else
              if k < (n / (Prims.of_int (2)))
              then
                Hacl_Spec_MLkem_Zq.add_zq
                  (ntt_ct_kth_term (n / (Prims.of_int (2)))
                     (Lib_NatMod.pow_mod Hacl_Spec_MLkem_Zq.q psi
                        (Prims.of_int (2))) (poly_even n f) k)
                  (Hacl_Spec_MLkem_Zq.mul_zq
                     (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                        Hacl_Spec_MLkem_Zq.q psi
                        (((Prims.of_int (2)) * k) + Prims.int_one))
                     (ntt_ct_kth_term (n / (Prims.of_int (2)))
                        (Lib_NatMod.pow_mod Hacl_Spec_MLkem_Zq.q psi
                           (Prims.of_int (2))) (poly_odd n f) k))
              else
                (let k' = k - (n / (Prims.of_int (2))) in
                 Hacl_Spec_MLkem_Zq.sub_zq
                   (ntt_ct_kth_term (n / (Prims.of_int (2)))
                      (Lib_NatMod.pow_mod Hacl_Spec_MLkem_Zq.q psi
                         (Prims.of_int (2))) (poly_even n f) k')
                   (Hacl_Spec_MLkem_Zq.mul_zq
                      (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                         Hacl_Spec_MLkem_Zq.q psi
                         (((Prims.of_int (2)) * k') + Prims.int_one))
                      (ntt_ct_kth_term (n / (Prims.of_int (2)))
                         (Lib_NatMod.pow_mod Hacl_Spec_MLkem_Zq.q psi
                            (Prims.of_int (2))) (poly_odd n f) k')))
let (ntt_ct :
  Hacl_Spec_MLkem_NTT.power_of_two ->
    (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod ->
      unit Hacl_Spec_MLkem_Poly.lpoly ->
        (Hacl_Spec_MLkem_Zq.zq, unit) Lib_Sequence.lseq)
  =
  fun n ->
    fun psi ->
      fun f -> Lib_Sequence.createi n (fun k -> ntt_ct_kth_term n psi f k)