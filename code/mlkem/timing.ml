open Lib_Sequence;;
open Prims;;

let x = of_int (Random.int 7681);;

let gen_poly (degree:Int.t) = createi (of_int degree) (fun i -> of_int (Random.int 7681));;

(* let time_ntt_vs_ct (degree:Int.t) (root:Z.t) =
  let p = gen_poly () in
  let times = (of_int 100) * ((of_int 4096) / (of_int degree)) in
  Printf.printf "Degree %d polynomial multiplication, running %d times\n" degree (Z.to_int times); 
  let total_duration_ntt = ref 0.0 in
  for i = 0 to (Z.to_int times) do
    let start_time_ntt = Unix.gettimeofday () in
    Hacl_Spec_MLkem_NTT.ntt (of_int degree) root p;
    let end_time_ntt = Unix.gettimeofday () in
    let duration_ntt = end_time_ntt -. start_time_ntt in
    total_duration_ntt := !total_duration_ntt +. duration_ntt
  done;
  Printf.printf "Time for NTT: %f seconds\n" !total_duration_ntt;
  let total_duration_ntt_ct = ref 0.0 in
  for i = 0 to (Z.to_int times) do 
    let start_time_ntt_ct = Unix.gettimeofday () in
    Hacl_Spec_NTT_Fast.ntt_ct (of_int degree) root p;
    let end_time_ntt_ct = Unix.gettimeofday () in
    let duration_ntt_ct = end_time_ntt_ct -. start_time_ntt_ct in
    total_duration_ntt_ct := !total_duration_ntt_ct +. duration_ntt_ct
  done;
  Printf.printf "Time for NTT_CT: %f seconds\n" !total_duration_ntt_ct *)

let time_ntt_mul_vs_naive (degree:Int.t) (root:Z.t) =
  let p = gen_poly degree in
  let q = gen_poly degree in
  let times = (of_int 10) * ((of_int 4096) / (of_int degree)) in
  Printf.printf "Degree %d polynomial multiplication, running %d times\n" degree (Z.to_int times); 
  let total_duration_ntt = ref 0.0 in
  for i = 0 to (Z.to_int times) do
    let start_time_ntt = Unix.gettimeofday () in
    Hacl_Spec_MLkem_NTT.mul_quotient_ring (of_int degree) p q;
    let end_time_ntt = Unix.gettimeofday () in
    let duration_ntt = end_time_ntt -. start_time_ntt in
    total_duration_ntt := !total_duration_ntt +. duration_ntt
  done;
  Printf.printf "Time for quotient ring multiplication: %f seconds\n" !total_duration_ntt;
  let total_duration_ntt_ct = ref 0.0 in
  for i = 0 to (Z.to_int times) do 
    let start_time_ntt_ct = Unix.gettimeofday () in
    let ntt_p = Hacl_Spec_NTT_Fast.ntt_ct (of_int degree) root p in
    let ntt_q = Hacl_Spec_NTT_Fast.ntt_ct (of_int degree) root q in
    let ntt_pq = Hacl_Spec_MLkem_NTT.mul_componentwise (of_int degree) ntt_p ntt_q in
    Hacl_Spec_NTT_Fast.ntt_ct (of_int degree) root ntt_pq;
    let end_time_ntt_ct = Unix.gettimeofday () in
    let duration_ntt_ct = end_time_ntt_ct -. start_time_ntt_ct in
    total_duration_ntt_ct := !total_duration_ntt_ct +. duration_ntt_ct
  done;
  Printf.printf "Time for NTT multiplication: %f seconds\n" !total_duration_ntt_ct

let () = 
  (* time_ntt_mul_vs_naive 4096 Hacl_Spec_MLkem_Zq.root_of_unity_kyber; *)
  time_ntt_mul_vs_naive 2048 Hacl_Spec_MLkem_Zq.root_of_unity_kyber
  (* time_ntt_mul_vs_naive 1024 Hacl_Spec_MLkem_Zq.root_of_unity_kyber;
  time_ntt_mul_vs_naive 512 Hacl_Spec_MLkem_Zq.root_of_unity_kyber;
  time_ntt_mul_vs_naive 256 Hacl_Spec_MLkem_Zq.root_of_unity_kyber;
  time_ntt_mul_vs_naive 128 Hacl_Spec_MLkem_Zq.root_of_unity_128;
  time_ntt_mul_vs_naive 64 Hacl_Spec_MLkem_Zq.root_of_unity_64;
  time_ntt_mul_vs_naive 32 Hacl_Spec_MLkem_Zq.root_of_unity_32;
  time_ntt_mul_vs_naive 16 Hacl_Spec_MLkem_Zq.root_of_unity_16;
  time_ntt_mul_vs_naive 8 Hacl_Spec_MLkem_Zq.root_of_unity_8;
  time_ntt_mul_vs_naive 4 Hacl_Spec_MLkem_Zq.root_of_unity_4 *)
  (* time_ntt_mul_vs_quot_ring () *)
