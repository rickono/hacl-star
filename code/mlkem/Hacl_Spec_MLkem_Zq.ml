open Prims
let (max : Prims.int -> Prims.int -> Prims.int) = FStar_Math_Lib.max
type nonzero_size_nat = Prims.nat
let (q : Prims.nat) = (Prims.of_int (7681))
type zq = unit Lib_NatMod.nat_mod
let (test_root_of_unity :
  Lib_NatMod.prime -> Prims.nat -> unit Lib_NatMod.nat_mod -> Prims.bool) =
  fun m ->
    fun n ->
      fun root ->
        (((Lib_NatMod.pow root n) mod m) = Prims.int_one) &&
          (root <> Prims.int_zero)
let rec (test_primitive :
  Lib_NatMod.prime -> Prims.pos -> unit Lib_NatMod.nat_mod -> Prims.bool) =
  fun m ->
    fun n ->
      fun root ->
        if n = Prims.int_one
        then true
        else
          (test_primitive m (n - Prims.int_one) root) &&
            (((Lib_NatMod.pow root (n - Prims.int_one)) mod m) <>
               Prims.int_one)
let (test_primitive_root_of_unity :
  Lib_NatMod.prime -> Prims.nat -> unit Lib_NatMod.nat_mod -> Prims.bool) =
  fun m ->
    fun n ->
      fun root -> (test_root_of_unity m n root) && (test_primitive m n root)
let (root_of_unity_kyber :
  (unit, unit) Hacl_Spec_MLkem_Unity.primitive_nth_root_of_unity_mod) =
  (Prims.of_int (62))
let (int_to_zq : Prims.int -> zq) = fun x -> x mod q
let (add_zq : zq -> zq -> zq) = fun a -> fun b -> Lib_NatMod.add_mod q a b
let (mul_zq : zq -> zq -> zq) = fun a -> fun b -> Lib_NatMod.mul_mod q a b
let (neg_zq : zq -> zq) =
  fun a -> if a = Prims.int_zero then Prims.int_zero else q - a
let (sub_zq : zq -> zq -> zq) = fun a -> fun b -> Lib_NatMod.sub_mod q a b
let (op_Plus_Percent : zq -> zq -> zq) = add_zq
let (op_Subtraction_Percent : zq -> zq -> zq) = sub_zq
let (op_Percent_Star : zq -> zq -> zq) = mul_zq