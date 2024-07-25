open Prims
type 't comm_monoid =
  {
  one: 't ;
  mul: 't -> 't -> 't ;
  lemma_one: unit ;
  lemma_mul_assoc: unit ;
  lemma_mul_comm: unit }
let __proj__Mkcomm_monoid__item__one : 't . 't comm_monoid -> 't =
  fun projectee ->
    match projectee with
    | { one; mul; lemma_one; lemma_mul_assoc; lemma_mul_comm;_} -> one
let __proj__Mkcomm_monoid__item__mul : 't . 't comm_monoid -> 't -> 't -> 't
  =
  fun projectee ->
    match projectee with
    | { one; mul; lemma_one; lemma_mul_assoc; lemma_mul_comm;_} -> mul
let one : 't . 't comm_monoid -> 't =
  fun projectee ->
    match projectee with
    | { one = one1; mul; lemma_one; lemma_mul_assoc; lemma_mul_comm;_} ->
        one1
let mul : 't . 't comm_monoid -> 't -> 't -> 't =
  fun projectee ->
    match projectee with
    | { one = one1; mul = mul1; lemma_one; lemma_mul_assoc; lemma_mul_comm;_}
        -> mul1
let lemma_one : 't . 't comm_monoid -> 't -> unit =
  fun uu___1 -> fun uu___ -> (fun projectee -> Obj.magic ()) uu___1 uu___
let lemma_mul_assoc : 't . 't comm_monoid -> 't -> 't -> 't -> unit =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun projectee -> Obj.magic ()) uu___3 uu___2 uu___1 uu___
let lemma_mul_comm : 't . 't comm_monoid -> 't -> 't -> unit =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ -> (fun projectee -> Obj.magic ()) uu___2 uu___1 uu___
type 't abelian_group =
  {
  cm: 't comm_monoid ;
  inverse: 't -> 't ;
  lemma_inverse: unit }
let __proj__Mkabelian_group__item__cm :
  't . 't abelian_group -> 't comm_monoid =
  fun projectee ->
    match projectee with | { cm; inverse; lemma_inverse;_} -> cm
let __proj__Mkabelian_group__item__inverse :
  't . 't abelian_group -> 't -> 't =
  fun projectee ->
    match projectee with | { cm; inverse; lemma_inverse;_} -> inverse
let cm : 't . 't abelian_group -> 't comm_monoid =
  fun projectee ->
    match projectee with | { cm = cm1; inverse; lemma_inverse;_} -> cm1
let inverse : 't . 't abelian_group -> 't -> 't =
  fun projectee ->
    match projectee with
    | { cm = cm1; inverse = inverse1; lemma_inverse;_} -> inverse1
let lemma_inverse : 't . 't abelian_group -> 't -> unit =
  fun uu___1 -> fun uu___ -> (fun projectee -> Obj.magic ()) uu___1 uu___
let sqr : 't . 't comm_monoid -> 't -> 't =
  fun k ->
    fun a ->
      match k with
      | { one = one1; mul = mul1; lemma_one = lemma_one1;
          lemma_mul_assoc = lemma_mul_assoc1;
          lemma_mul_comm = lemma_mul_comm1;_} -> mul1 a a
let rec pow : 't . 't comm_monoid -> 't -> Prims.nat -> 't =
  fun k ->
    fun x ->
      fun n ->
        if n = Prims.int_zero
        then
          match k with
          | { one = one1; mul = mul1; lemma_one = lemma_one1;
              lemma_mul_assoc = lemma_mul_assoc1;
              lemma_mul_comm = lemma_mul_comm1;_} -> one1
        else
          ((match k with
            | { one = one1; mul = mul1; lemma_one = lemma_one1;
                lemma_mul_assoc = lemma_mul_assoc1;
                lemma_mul_comm = lemma_mul_comm1;_} -> mul1)) x
            (pow k x (n - Prims.int_one))
let pow_neg : 't . 't abelian_group -> 't -> Prims.int -> 't =
  fun k ->
    fun x ->
      fun n ->
        if n >= Prims.int_zero
        then
          pow
            (match k with
             | { cm = cm1; inverse = inverse1;
                 lemma_inverse = lemma_inverse1;_} -> cm1) x n
        else
          ((match k with
            | { cm = cm1; inverse = inverse1;
                lemma_inverse = lemma_inverse1;_} -> inverse1))
            (pow
               (match k with
                | { cm = cm1; inverse = inverse1;
                    lemma_inverse = lemma_inverse1;_} -> cm1) x (- n))