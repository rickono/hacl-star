open Prims
let (max : Prims.int -> Prims.int -> Prims.int) = FStar_Math_Lib.max
let (poly_lower :
  Prims.nat ->
    unit Hacl_Spec_MLkem_Poly.lpoly -> unit Hacl_Spec_MLkem_Poly.lpoly)
  =
  fun n ->
    fun f ->
      Lib_Sequence.createi (n / (Prims.of_int (2)))
        (fun i -> Hacl_Spec_MLkem_Poly.poly_index n f i)
let (poly_upper :
  Prims.nat ->
    unit Hacl_Spec_MLkem_Poly.lpoly -> unit Hacl_Spec_MLkem_Poly.lpoly)
  =
  fun n ->
    fun f ->
      Lib_Sequence.createi (n / (Prims.of_int (2)))
        (fun i ->
           Hacl_Spec_MLkem_Poly.poly_index n f (i + (n / (Prims.of_int (2)))))
let rec (intt_gs_kth_term :
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
              if (k mod (Prims.of_int (2))) = Prims.int_zero
              then
                Hacl_Spec_MLkem_Zq.mul_zq
                  (Hacl_Spec_MLkem_Zq.add_zq
                     (intt_gs_kth_term (n / (Prims.of_int (2)))
                        (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                           Hacl_Spec_MLkem_Zq.q psi (Prims.of_int (2)))
                        (poly_lower n f) (k / (Prims.of_int (2))))
                     (intt_gs_kth_term (n / (Prims.of_int (2)))
                        (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                           Hacl_Spec_MLkem_Zq.q psi (Prims.of_int (2)))
                        (poly_upper n f) (k / (Prims.of_int (2)))))
                  (Hacl_Spec_MLkem_PowModInt.pow_mod_int Hacl_Spec_MLkem_Zq.q
                     psi (- ((Prims.of_int (2)) * k)))
              else
                Hacl_Spec_MLkem_Zq.mul_zq
                  (Hacl_Spec_MLkem_Zq.sub_zq
                     (intt_gs_kth_term (n / (Prims.of_int (2)))
                        (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                           Hacl_Spec_MLkem_Zq.q psi (Prims.of_int (2)))
                        (poly_lower n f) (k / (Prims.of_int (2))))
                     (intt_gs_kth_term (n / (Prims.of_int (2)))
                        (Hacl_Spec_MLkem_PowModInt.pow_mod_int
                           Hacl_Spec_MLkem_Zq.q psi (Prims.of_int (2)))
                        (poly_upper n f) (k / (Prims.of_int (2)))))
                  (Hacl_Spec_MLkem_PowModInt.pow_mod_int Hacl_Spec_MLkem_Zq.q
                     psi (- ((Prims.of_int (2)) * k)))