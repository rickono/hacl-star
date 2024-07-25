open Prims
let (max : Prims.int -> Prims.int -> Prims.int) = FStar_Math_Lib.max
type 'deg lpoly = (Hacl_Spec_MLkem_Zq.zq, unit) Lib_Sequence.lseq
let (zero : Prims.nat -> (Prims.int, unit) Lib_Sequence.lseq) =
  fun deg -> Lib_Sequence.create deg Prims.int_zero
let (one : Prims.nat -> (Prims.int, unit) Lib_Sequence.lseq) =
  fun deg -> Lib_Sequence.create deg Prims.int_one
let (poly_index :
  Prims.nat -> unit lpoly -> Prims.int -> Hacl_Spec_MLkem_Zq.zq) =
  fun deg ->
    fun p ->
      fun i ->
        if (Prims.int_zero <= i) && (i < (Lib_Sequence.length p))
        then Lib_Sequence.index deg p i
        else Prims.int_zero
let (add : Prims.nat -> unit lpoly -> unit lpoly -> unit lpoly) =
  fun deg ->
    fun a ->
      fun b ->
        Lib_Sequence.createi deg
          (fun i ->
             Hacl_Spec_MLkem_Zq.add_zq (Lib_Sequence.index deg a i)
               (Lib_Sequence.index deg b i))
type tq = (Hacl_Spec_MLkem_Zq.zq, unit) Lib_Sequence.lseq
let (index_tq : tq -> Prims.nat -> Hacl_Spec_MLkem_Zq.zq) =
  fun t -> fun i -> Lib_Sequence.index (Prims.of_int (256)) t i
let (upd_tq : tq -> Prims.nat -> Hacl_Spec_MLkem_Zq.zq -> tq) =
  fun t -> fun i -> fun v -> Lib_Sequence.upd (Prims.of_int (256)) t i v
let (scalar_mul :
  Prims.nat -> unit lpoly -> Hacl_Spec_MLkem_Zq.zq -> unit lpoly) =
  fun deg ->
    fun p ->
      fun c ->
        Lib_Sequence.createi deg
          (fun i -> Hacl_Spec_MLkem_Zq.mul_zq c (Lib_Sequence.index deg p i))