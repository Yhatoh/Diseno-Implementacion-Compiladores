open Asm

(* Environment *)
type slot_env = (string * int64) list
let empty_slot_env : slot_env = []
let extend_slot_env : string -> int64 -> slot_env -> slot_env =
  fun x v slot_env -> (x, v) :: slot_env

let rec slot_env_lookup (var : string) (slot_env : slot_env) : int64 =
  match slot_env with
  | [] -> failwith "Unbound identifier."
  | (n, slot) :: rest -> if n = var then slot else (slot_env_lookup var rest)


let int_to_cc64_reg (n : int) : reg =
  match n with
  | 1 -> RDI
  | 2 -> RSI
  | 3 -> RDX
  | 4 -> RCX
  | 5 -> R8
  | 6 -> R9
  | _ -> failwith "Argument n out of bounds."


let store_arg (n : int) (a : arg) : instruction =
  if (n > 0 && n < 7) then IPush (Reg (int_to_cc64_reg n)) else IPush a

let store_first_6_args : instruction list =
  [
    (store_arg 6 (Reg RAX));
    (store_arg 5 (Reg RAX));
    (store_arg 4 (Reg RAX));
    (store_arg 3 (Reg RAX));
    (store_arg 2 (Reg RAX));
    (store_arg 1 (Reg RAX))
  ]

let move_arg_1_to_6 (n : int) (a : arg) : instruction =
  IMov (Reg (int_to_cc64_reg n), a)

let pop_arg (n : int) : instruction =
  IPop (Reg (int_to_cc64_reg n))

let pop_first_6_args : instruction list =
  [
    pop_arg 1;
    pop_arg 2;
    pop_arg 3;
    pop_arg 4;
    pop_arg 5;
    pop_arg 6
  ]
