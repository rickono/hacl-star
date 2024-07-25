open Prims
let (max : Prims.int -> Prims.int -> Prims.int) = FStar_Math_Lib.max
let rec (sum_of_zqs :
  Prims.int ->
    Prims.int ->
      (Prims.int -> Hacl_Spec_MLkem_Zq.zq) -> Hacl_Spec_MLkem_Zq.zq)
  =
  fun start ->
    fun stop ->
      fun f ->
        if start >= stop
        then Prims.int_zero
        else
          Hacl_Spec_MLkem_Zq.add_zq (f (stop - Prims.int_one))
            (sum_of_zqs start (stop - Prims.int_one) f)