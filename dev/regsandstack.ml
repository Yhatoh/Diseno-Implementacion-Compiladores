open Asm
open Printf

(* Environment *)
type slot_env = (string * int64) list
let empty_slot_env : slot_env = []
let extend_slot_env : string -> int64 -> slot_env -> slot_env =
  fun x v slot_env -> (x, v) :: slot_env

let rec slot_env_lookup (var : string) (slot_env : slot_env) : int64 =
  match slot_env with
  | [] -> failwith "Unbound identifier."
  | (n, slot) :: rest -> if n = var then slot else (slot_env_lookup var rest)


(* Function Environment *)
type comp_fun = string * string list
type comp_fenv = comp_fun list
let empty_comp_fenv : comp_fenv = []
let rec lookup_comp_fenv : string -> int -> comp_fenv -> comp_fun =
  fun s total_args fenv -> 
    match fenv with
    | [] -> (failwith (sprintf "Undefined function: %s" s))
    | ((f_name, f_args)::fs) -> if (f_name = s) then
                                  (if (List.length f_args) = total_args then
                                    (f_name, f_args)
                                  else (failwith (sprintf "Expected a total of %d parameters for %s, but got %d" (List.length f_args) s (total_args))))
                                else lookup_comp_fenv s total_args fs

let extend_comp_fenv : string -> string list -> comp_fenv -> comp_fenv =
  fun x v comp_fenv -> (x, v) :: comp_fenv


let int_to_cc64_reg (n : int) : reg =
  match n with
  | 1 -> RDI
  | 2 -> RSI
  | 3 -> RDX
  | 4 -> RCX
  | 5 -> R8
  | 6 -> R9
  | _ -> failwith (sprintf "Argument %d out of bounds." n)


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
