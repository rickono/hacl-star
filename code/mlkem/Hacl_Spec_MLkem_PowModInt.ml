open Prims
let (max : Prims.int -> Prims.int -> Prims.int) = FStar_Math_Lib.max
let (pow_mod_int :
  Lib_NatMod.prime ->
    unit Lib_NatMod.nat_mod -> Prims.int -> unit Lib_NatMod.nat_mod)
  =
  fun m ->
    fun a ->
      fun b ->
        if b >= Prims.int_zero
        then Lib_NatMod.pow_mod m a b
        else Lib_NatMod.pow_mod m a ((- b) * (m - (Prims.of_int (2))))
let (pow_mod_int_neg_one : Prims.nat -> Prims.int -> unit Lib_NatMod.nat_mod)
  =
  fun m ->
    fun n ->
      if (n mod (Prims.of_int (2))) = Prims.int_zero
      then Prims.int_one
      else (Prims.of_int (-1)) mod m