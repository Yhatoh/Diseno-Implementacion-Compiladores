open Ast
open Asm
open Printf
open Regsandstack

let add_int_tag : int64 = 4L
let mul_div_shift_correction : int64 = 2L
let bool_tag : int64 = 2L
let int_tag : int64 = 0L
let tup_tag : int64 = 1L
let lambda_tag : int64 = 3L
let type_mask : int64 = 3L
let one : int64 = 4L

let true_bit_int_64 : int64 = 4L
let false_bit_int_64 : int64 = 0L

let bool_to_int (b : bool) : int64 =
  (Int64.add bool_tag (if b then true_bit_int_64 else false_bit_int_64))

(*let a_normal_form_binop (binop : prim2)*)

let rsp_pointer (slot : int64) : arg = Ptr (RSP, slot)
let rbp_pointer (slot : int64) : arg = Ptr (RBP, slot)

(* Type checking of operations*)
let check_rax_is_type_instr (tp : int64) (slot : int64) : instruction list =
  let label = if tp = int_tag 
                then "error_not_number" 
                else (if tp = bool_tag 
                      then "error_not_boolean"
                      else (if tp = tup_tag 
                            then "error_not_tuple"
                            else "error_not_lambda"))
  in
  [
    iMov_arg_arg (rbp_pointer slot) rax;
    iAnd_arg_const rax type_mask;
    iCmp_arg_const rax tp;
    iMov_arg_to_RAX (rbp_pointer slot);
    i_jne label
  ]

(* NASM code to verify that the value in RAX is an integer in our language *)
let check_rax_is_int_instr (slot : int64) : instruction list = 
  check_rax_is_type_instr int_tag slot

(* NASM code to verify that the value in RAX is a boolean in our language *)  
let check_rax_is_bool_instr (slot : int64) : instruction list = 
  check_rax_is_type_instr bool_tag slot
 
(* NASM code to verify that the value in RAX is a tuple in our language *)
let check_rax_is_tuple_instr (slot : int64) : instruction list =
  check_rax_is_type_instr tup_tag slot

(* NASM code to verify that the value in RAX is a lambda in our language *)
let check_rax_is_lambda_instr (slot : int64) : instruction list =
  check_rax_is_type_instr lambda_tag slot

(* Verifies that the value of the operand of a unary
   operation has a valid type. *)
let type_of_unops (operation : prim1) (slot : int64) : instruction list =
  match operation with
  | Add1 | Sub1 -> check_rax_is_int_instr slot
  | Not -> check_rax_is_bool_instr slot
  | Print -> []

(* Verifies that the values of the operands of a binary
   operation have valid types. *)
let type_of_binops (operation : prim2) (slot : int64) : instruction list =
  match operation with
  | Add | Sub | Mul | Div | Lte -> check_rax_is_int_instr slot
  | And -> check_rax_is_bool_instr slot
  | Get -> []

(* Protocol for setting stack before a function call. *)
let function_start (n_local_vars : int64) : instruction list =
  [
    iPush rbp ;
    iMov_arg_arg rbp rsp ;
    iSub_arg_const rsp (Int64.mul 8L (n_local_vars))
  ]

(* Protocol for recovering scope values
   after an internal function call returns. *)
let function_end : instruction list =
  [
    iMov_arg_arg rsp rbp ;
    iPop rbp;
    IRet
  ]

(* Compile <= *)
let compile_lte (rax: arg) (rbp_ptr: arg) (tag : int) (tag_fun : int): instruction list = 
  let else_label = sprintf "if_false_%d_%d" tag_fun tag in
  let done_label = sprintf "done_%d_%d" tag_fun tag in
  let iMov_bool_to_rax (b : bool) = iMov_arg_const rax (bool_to_int b) in
  [
    iCmp_arg_arg rax rbp_ptr;
    i_jg else_label;
    iMov_bool_to_rax true;
    i_jmp done_label;
    i_label else_label;
    iMov_bool_to_rax false; 
    i_label done_label
  ]

(* Transforms a binary operation to an instruction type structure *)
let binop_to_instr (op : prim2) (slot : int64) (tag : int) (tag_fun : int) : instruction list =
  let rbp_ptr = rbp_pointer slot in
  let as_list (fn : (arg -> arg -> instruction)) : (arg -> arg -> instruction list) =
    let ret_fn (arg1 : arg) (arg2 : arg) : instruction list = [fn arg1 arg2] in
    ret_fn
  in
  let compile_div (e1 : arg) (e2 : arg) : instruction list =
    [ICqo; iDiv_arg_arg e1 e2]
  in
  let compile_lte_with_tag (e1 : arg) (e2 : arg) : instruction list =
    compile_lte e1 e2 tag tag_fun
  in
  let compile_get (rax : arg) (rbp_ptr : arg) : instruction list =
    let r10_ptr = Ptr(R10, 0L) in
    let check_index_range = [
      iCmp_arg_const r11 0L ;
      IJl "index_too_low" ;
      iCmp_arg_arg r11 r10_ptr ;
      IJge "index_too_high"
    ]
    in
    [
      iPush r10 ;
      iPush r11 ;
      iMov_arg_arg r10 rax
      (*iMov_arg_to_RAX r10*)
    ] @(*[iMov_arg_arg rax r10] @*)
    (check_rax_is_tuple_instr (Int64.sub slot 1L)) @
    [
      iSub_arg_const r10 1L ;
      iMov_arg_arg r11 rbp_ptr ;
      iMov_arg_to_RAX rbp_ptr
    ] @(*[iMov_arg_arg rax rbp_ptr] @*)
    (check_rax_is_int_instr slot) @
    [iMov_arg_arg r11 rbp_ptr] @
    check_index_range @
    [
      iSar r11 2L ;
      iAdd_arg_const r11 1L ;
      iSal r11 3L ;
      iAdd_arg_arg r10 r11 ;
      iMov_arg_to_RAX r10_ptr ;
      iPop r11 ;
      iPop r10
    ] 
  in
  let builder =
    match op with
    | Add -> as_list iAdd_arg_arg
    | Sub -> as_list iSub_arg_arg
    | Mul -> as_list iMul_arg_arg
    | Div -> compile_div
    | And -> as_list iAnd_arg_arg
    | Lte -> compile_lte_with_tag
    | Get -> compile_get
  in
  builder rax rbp_ptr

(* Transforms a unary operation to a list of instruction type structures *)
let unop_to_instr_list (op: prim1) : instruction list =
  let iAdd1_arg_list (a : arg) : instruction list = [iAdd_arg_const a one] in
  let iSub1_arg_list (a : arg) : instruction list = [iSub_arg_const a one] in
  let iNot_arg_list (a : arg) : instruction list = [iNot_arg a ; iAdd_arg_const a 2L ; iSub_arg_const a 1L] in
  let iPrint_arg_list (a : arg) : instruction list = 
    store_r10_r11 @
    store_first_6_args @
    [
      move_arg_1_to_6 1 a ;
      iCall_print ;
    ] @
    pop_first_6_args @
    pop_r10_r11 
  in
  let builder =
    match op with
    | Add1 -> iAdd1_arg_list
    | Sub1 -> iSub1_arg_list
    | Not -> iNot_arg_list
    | Print -> iPrint_arg_list
  in
  builder rax

(* Algebraic datatype for tagged expressions *)
type 'a texpr = 
  | TNum of int64 * 'a 
  | TBool of bool * 'a
  | TPrim1 of prim1 * 'a texpr * 'a
  | TPrim2 of prim2 * 'a texpr * 'a texpr * 'a
  | TId of string * 'a
  | TLet of string * 'a texpr * 'a texpr * 'a
  | TSet of 'a texpr * 'a texpr * 'a texpr * 'a
  | TIf of 'a texpr * 'a texpr * 'a texpr * 'a
  | TApply of string * 'a texpr list * 'a
  | TTuple of 'a texpr list * 'a
  | TLambda of string list * 'a texpr * 'a
  | TLamApply of 'a texpr * 'a texpr list * 'a
  | TLetRec of (string * string list * 'a texpr * 'a) list * 'a texpr * 'a

(* Algebraic data type for tagged functions *)
type 'a tfun_def =
  | TDefFun of string * string list * 'a texpr * 'a

type tag = int 

(* Checks whether the variable "name" is a free variable (i.e. is contained in slot_env). *)
let rec exist_var_slot_env (name : string) (slot_env : slot_env): bool =
  match slot_env with
  | [] -> false
  | (n, _) :: rest -> if (n = name) then true else (exist_var_slot_env name rest)

(* Checks whether the identifier "name" is a function parameter. *)
let rec var_is_a_param (name : string) (arg_names : string list) : bool =
  match arg_names with
  | [] -> false
  | n:: rest -> if (n = name) then true else (var_is_a_param name rest)

(* Counts the number of free variables in the scope inner_scope *)
let count_vars (e_l : tag texpr) (inner_scope : string list) (arg_names : string list) (slot_env : slot_env) : int64 * string list =
  let add_int64 (a : int64) (b : int64) : int64 = Int64.add a b in
  let triple_add_int64 (a : int64) (b : int64) (c : int64) : int64 = add_int64 (add_int64 a b) c in
  let rec real_count_vars (e_l : tag texpr) (inner_scope : string list) : int64 * string list =
    match e_l with
    | TId (s, _) -> 
      if (exist_var_slot_env s slot_env)
      then 
        if not (var_is_a_param s arg_names)
        then (if not (var_is_a_param s inner_scope)
              then (1L, [s])
              else (0L, [])) 
        else (0L, [])
      else (0L, [])
    | TNum (_, _) | TBool (_, _) -> (0L, [])
    | TPrim1 (_, n, _) -> 
      let sum, lambda_env = real_count_vars n inner_scope in
      (sum, lambda_env)
    | TLet (nm, e1, e2, _) ->
      let sum1, lambda_env1 = (real_count_vars e1 inner_scope) in
      let sum2, lambda_env2 = (real_count_vars e2 (nm::inner_scope)) in
      (add_int64 sum1 sum2, lambda_env1 @ lambda_env2) 
    | TPrim2 (_, e1, e2, _) ->
      let sum1, lambda_env1 = (real_count_vars e1 inner_scope) in
      let sum2, lambda_env2 = (real_count_vars e2 inner_scope) in
      (add_int64 sum1 sum2, lambda_env1 @ lambda_env2) 
    | TIf(cond, thn, els, _) -> 
      let sum_cond, lambda_env_cond = (real_count_vars cond inner_scope) in
      let sum_thn, lambda_env_thn = (real_count_vars thn inner_scope) in
      let sum_els, lambda_env_els = (real_count_vars els inner_scope) in
      (triple_add_int64 sum_cond sum_thn sum_els, lambda_env_cond @ lambda_env_thn @ lambda_env_els)
    | TApply(_, args, _) -> 
      let rec count_apply_vars (e_list : tag texpr list) : int64 * string list =
        match e_list with
        | [] -> (0L, [])
        | hd::tl -> 
          let sum_hd, lambda_env_hd = (real_count_vars hd inner_scope) in
          let sum_tl, lambda_env_tl = (count_apply_vars tl) in
          (add_int64 sum_hd sum_tl, lambda_env_hd @ lambda_env_tl)
      in
      count_apply_vars args
    | TTuple(attrs, _) -> 
      let rec count_tuple_vars (e_list : tag texpr list) : int64 * string list =
        match e_list with
        | [] -> (0L, [])
        | hd::tl -> 
          let sum_hd, lambda_env_hd = (real_count_vars hd inner_scope) in
          let sum_tl, lambda_env_tl = (count_tuple_vars tl) in
          (add_int64 sum_hd sum_tl, lambda_env_hd @ lambda_env_tl)
      in
      count_tuple_vars attrs
    | TSet(t, pos, value, _) ->
      let sum_t, lambda_env_t = (real_count_vars t inner_scope) in
      let sum_pos, lambda_env_pos = (real_count_vars pos inner_scope) in
      let sum_value, lambda_env_value = (real_count_vars value inner_scope) in
      (triple_add_int64 sum_t sum_pos sum_value, lambda_env_t @ lambda_env_pos @ lambda_env_value)
    | TLambda(_, e, _) ->
      let sum, lambda_env = real_count_vars e inner_scope in
      (sum, lambda_env)  
    | TLamApply(lbd, e, _) ->
      let rec count_apply_vars (e_list : tag texpr list) : int64 * string list =
        match e_list with
        | [] -> (0L, [])
        | hd::tl -> 
          let sum_hd, lambda_env_hd = (real_count_vars hd inner_scope) in
          let sum_tl, lambda_env_tl = (count_apply_vars tl) in
          (add_int64 sum_hd sum_tl, lambda_env_hd @ lambda_env_tl)
      in
      let sum_lbd, lambda_env_lbd = (real_count_vars lbd inner_scope) in
      let sum_e, lambda_env_e = (count_apply_vars e) in
      (add_int64 sum_lbd sum_e, lambda_env_lbd @ lambda_env_e)
    | TLetRec(lbds, e, _) ->
      let rec count_lbds_vars (lbds_list : (string * string list * tag texpr * 'a) list) : int64 * string list =
        match lbds_list with
        | [] -> (0L, [])
        | (_, _, e, _)::tl -> 
          let sum_e, lambda_env_e = (real_count_vars e inner_scope) in
          let sum_tl, lambda_env_tl = (count_lbds_vars tl) in
          (add_int64 sum_e sum_tl, lambda_env_e @ lambda_env_tl)
      in 
      let sum_lbds, lambda_env_lbds = (count_lbds_vars lbds) in
      let sum_e, lambda_env_e = (real_count_vars e inner_scope) in
      (add_int64 sum_lbds sum_e, lambda_env_lbds @ lambda_env_e)
  in 
  real_count_vars e_l inner_scope
  

(* Takes a parsed program and tags all expressions within *)
let tag_expr (e : expr) : tag texpr =
  let rec help (e : expr) (cur : tag) : (tag texpr * tag) =
    let rec tag_list (es : expr list) (sub_cur : tag) =
      match es with
      | [] -> ([], sub_cur)
      | hd :: tl ->
        let (tagged_hd, next_tag1) = help hd (sub_cur + 1) in
        let (tagged_tl, next_tag2) = tag_list tl next_tag1 in
        (tagged_hd :: tagged_tl, next_tag2)
    in
    let rec lbd_list (lbds : (string * string list * expr) list) (sub_cur : tag) = 
      match lbds with
      | [] -> ([], sub_cur)
      | (nm, args, lbd)::tl ->
        let (tagged_lbd, next_tag1) = help lbd (sub_cur + 1) in
        let (tagged_tl, next_tag2) = lbd_list tl next_tag1 in
        ((nm, args, tagged_lbd, sub_cur)::tagged_tl, next_tag2)
    in
    match e with
    | Prim1(op, e) ->
      let (tag_e, next_tag) = help e (cur + 1) in
      (TPrim1(op, tag_e, cur), next_tag)
    | Prim2(op, e1, e2) ->
      let (tag_e1, next_tag1) = help e1 (cur + 1) in
      let (tag_e2, next_tag2) = help e2 (next_tag1) in
      (TPrim2(op, tag_e1, tag_e2, cur), next_tag2)
    | If(e1, e2, e3) ->
      let (tag_e1, next_tag1) = help e1 (cur + 1) in
      let (tag_e2, next_tag2) = help e2 (next_tag1) in
      let (tag_e3, next_tag3) = help e3 (next_tag2) in
      (TIf(tag_e1, tag_e2, tag_e3, cur), next_tag3)
    | Let(name, e1, e2) ->
      let (tag_e1, next_tag1) = help e1 (cur + 1) in
      let (tag_e2, next_tag2) = help e2 (next_tag1) in
      (TLet(name, tag_e1, tag_e2, cur), next_tag2)
    | Set(t, pos, value) ->
      let (tag_t, next_tag1) = help t (cur + 1) in
      let (tag_pos, next_tag2) = help pos (next_tag1) in
      let (tag_value, next_tag3) = help value (next_tag2) in
      (TSet(tag_t, tag_pos, tag_value, cur), next_tag3)
    | Num(num) -> (TNum(num, cur), cur + 1)
    | Bool(b) -> (TBool(b, cur), cur + 1)
    | Id(name) -> (TId(name, cur), cur + 1)
    | Apply(f_name, args) ->
      let (tagged_args, next_tag) = tag_list args (cur + 1) in
      (TApply(f_name, tagged_args, cur), next_tag)
    | Tuple(attrs) ->
      let (tagged_attrs, next_tag) = tag_list attrs (cur + 1) in
      (TTuple(tagged_attrs, cur), next_tag)
    | Lambda(args_names, e) -> 
      let (tag_e, next_tag) = help e (cur + 1) in
      (TLambda(args_names, tag_e, cur), next_tag)
    | LamApply(e, args) ->
      let (tagged_e, next_tag1) = help e (cur + 1) in
      let (tagged_args, next_tag2) = tag_list args next_tag1 in
      (TLamApply(tagged_e, tagged_args, cur), next_tag2)
    | LetRec(lbds, e) ->
      let (tagged_lbds, next_tag1) = lbd_list lbds (cur + 1) in 
      let (tagged_e, next_tag2) = help e next_tag1 in
      (TLetRec(tagged_lbds, tagged_e, cur), next_tag2)
  in
  let (tagged, _) = help e 1 in tagged;;

(* Tags the content of an inner function *)
let rec tag_funs (flist : fundef list) (n : int) : tag tfun_def list =
  match flist with
  | [] -> []
  | DefFun (name, arg_names, e) :: tail -> TDefFun (name, arg_names, tag_expr e, n) :: tag_funs tail (n + 1)

(* Tags functions and main of the parsed program *)
let tag_prog (prog : prog) : tag tfun_def list * tag texpr = 
  let (funs, main) = prog in
  (tag_funs funs 1, tag_expr main)

(* Counts the number of let-bindings present on a program or function.
   Used to estimate the stack size required for its execution. *)
let rec count_exprs (e : tag texpr) : int64 =
  let add1_i64 (n : int64) : int64 = Int64.add 1L n in
  match e with
  | TLet (_, value, e_let, _) -> (Int64.add (add1_i64 (count_exprs value)) (count_exprs e_let))
  | TPrim1 (_, n, _) -> add1_i64 (count_exprs n)
  | TPrim2 (_, e1, e2, _) -> add1_i64 (max (count_exprs e1) (count_exprs e2))
  | TIf (cond, thn, els, _) -> add1_i64 (max (max (count_exprs cond) (count_exprs thn)) (count_exprs els))
  | TId _ | TBool _ | TNum _ -> 1L
  | TApply (_, args, _) ->
    let rec count_apply_exprs (e_list : tag texpr list) : int64 =
      match e_list with
      | [] -> 0L
      | hd::tl -> Int64.add (count_exprs hd) (count_apply_exprs tl)
    in
    count_apply_exprs args
  | TTuple (attrs, _) ->
    let rec count_tuple_exprs (e_list : tag texpr list) : int64 =
      match e_list with
      | [] -> 0L
      | hd::tl -> max (count_exprs hd) (count_tuple_exprs tl)
    in
    (add1_i64 (count_tuple_exprs attrs))
  | TSet (t, pos, value, _) ->
    add1_i64 (Int64.add (Int64.add (count_exprs t) (count_exprs pos)) (count_exprs value))
  | TLambda(_, e, _) -> add1_i64 (count_exprs e)
  | TLamApply(e, args, _) ->
    let rec count_apply_exprs (e_list : tag texpr list) : int64 =
      match e_list with
      | [] -> 0L
      | hd::tl -> Int64.add (count_exprs hd) (count_apply_exprs tl)
    in
    (max (count_apply_exprs args) (count_exprs e))
  | TLetRec(lbds, e, _) ->
    let rec count_lbds_exprs (lbds_list : (string * string list * 'a texpr * 'a) list) : int64 =
      match lbds_list with
      | [] -> 0L
      | (_, _, lbd, _)::tl -> Int64.add (count_exprs lbd) (count_lbds_exprs tl)
    in
    (max (count_lbds_exprs lbds) (count_exprs e))

      

(* Pretty printing - used by testing framework *)
let rec string_of_tag_expr(e : tag texpr) : string = 
  match e with
  | TNum (n, tag) -> sprintf "tag_%d %s" tag (Int64.to_string n)
  | TBool (b, tag) -> sprintf "tag_%d %s" tag (if b then "true" else "false")
  | TId (s, tag) -> sprintf "tag_%d %s" tag s
  | TPrim1 (op, e, tag) -> sprintf "(tag_%d %s %s)" tag
    (match op with
    | Add1 -> "add1"
    | Sub1 -> "sub1"
    | Not -> "not"
    | Print -> "print") (string_of_tag_expr e)
  | TPrim2 (op, e1, e2, tag) -> sprintf "(tag_%d %s %s %s)" tag 
    (match op with 
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | And -> "&&"
    | Lte -> "<="
    | Get -> "get") (string_of_tag_expr e1) (string_of_tag_expr e2)
  | TLet (x, e1, e2, tag) -> sprintf "(tag_%d let (%s %s) %s)" tag x (string_of_tag_expr e1) (string_of_tag_expr e2) 
  | TSet (t, e1, e2, tag) -> sprintf "(tag_%d set %s %s %s)" tag (string_of_tag_expr t) (string_of_tag_expr e1) (string_of_tag_expr e2) 
  | TIf (e1, e2, e3, tag) -> sprintf "(tag_%d if %s %s %s)" tag (string_of_tag_expr e1) (string_of_tag_expr e2) (string_of_tag_expr e3)
  | TApply (nm, args, tag) -> sprintf "(tag_%d %s (%s))" tag nm (String.concat " " (List.map string_of_tag_expr args))
  | TTuple (attrs, tag) -> sprintf "(tag_%d %s)" tag (String.concat " " (List.map string_of_tag_expr attrs))
  | TLambda (args, e, tag) -> sprintf "(tag_%d lambda (%s) %s)" tag (String.concat " " args) (string_of_tag_expr e)
  | TLamApply (e, args, tag) -> sprintf "(tag_%d %s %s)" tag (string_of_tag_expr e) (String.concat " " (List.map string_of_tag_expr args))
  | TLetRec (lbds, e, tag) -> 
    (sprintf "(tag_%d %s %s)" tag 
      (String.concat " " 
        (List.map 
          (fun s -> (match s with
            | (nm, args, e, tag) -> 
              sprintf "(tag_%d %s (lambda (%s) %s))" tag nm (String.concat " " args) (string_of_tag_expr e))
          ) lbds
        )
      ) 
      (string_of_tag_expr e))

(* Transforms a binary bool-bool operation to a list of instruction type structures *)
let binop_boolean_to_instr_list (second_arg_eval : instruction list) (tag : int) (tag_fun : int) (skip_value : bool) : instruction list =
  let skip_label = sprintf "skip_%d_%d" tag_fun tag in
  [
    iCmp_arg_const rax (bool_to_int skip_value) ;
    i_je skip_label
  ] @
  second_arg_eval @
  [i_label skip_label]


(* Compiles the value binding to an identifier. *)
let rec compile_tid (slot_env : slot_env) (s : string) : instruction list =
  let pos_stack = slot_env_lookup s slot_env in 
  let search_var = if (0L >= pos_stack)
                   then rbp_pointer pos_stack
                   else if (pos_stack > 6L)
                   then rbp_pointer (Int64.sub pos_stack 5L)
                   else (Reg (int_to_cc64_reg (Int64.to_int pos_stack))) 
  in    
  [iMov_arg_to_RAX (search_var)]
(* Compiles a unary operation. *)
and compile_prim1 (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (op: prim1) (n: tag texpr) : instruction list =
  let compiled_n = (compile_expr n slot_env slot fenv tag_fun total_params) in
  let check_over_under_flow (checker_name : string) : instruction list = 
    store_r10_r11 @
    store_first_6_args @
    [
      iMov_arg_arg rdi rax; 
      iMov_arg_const rsi one ; 
      iCall_string checker_name ; 
      iMov_arg_arg rax (rbp_pointer slot)
    ] @
    pop_first_6_args @
    pop_r10_r11 
  in
  (compiled_n) @ (type_of_unops op slot)
  @ (begin match op with
      | Add1 -> check_over_under_flow "check_overflow_add"
      | Sub1 -> check_over_under_flow "check_overflow_sub"
      | _ -> []
    end)
  @ (unop_to_instr_list op)
(* Compiles a binary operation. *)
and compile_prim2 (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (op : prim2) (n1 : tag texpr) (n2 : tag texpr) (tag : int) : instruction list =
  let next_slot = (Int64.add 1L slot) in
  let rbp_ptr = rbp_pointer slot in
  let compile_e (n : tag texpr) (slot : int64): instruction list = compile_expr n slot_env slot fenv tag_fun total_params in
  let compiled_e1 = compile_e n1 slot @ type_of_binops op slot in
  let compiled_e2 = compile_e n2 next_slot @ type_of_binops op next_slot in 
  let mov_rax_to_rbp = iMov_arg_arg rbp_ptr rax in
  let check_over_under_flow (checker_name : string) : instruction list =   
    store_r10_r11 @
    store_first_6_args @
    [
      iMov_arg_arg rdi rbp_ptr; 
      iMov_arg_arg rsi (rbp_pointer next_slot) ; 
      iCall_string (checker_name) ;
    ] @
    pop_first_6_args @
    pop_r10_r11 
  in
  let check_zero_division : instruction list = 
    store_r10_r11 @
    store_first_6_args @
    [
      iMov_arg_arg rdi (rbp_pointer next_slot) ; 
      iCall_string ("check_div_by_0") ; 
    ] @
    pop_first_6_args @
    pop_r10_r11 
  in
  let safe_env_checker : instruction list =
    match op with
    | And | Lte | Get -> []
    | Add -> check_over_under_flow "check_overflow_add"
    | Sub -> check_over_under_flow "check_overflow_sub"
    | Mul -> check_over_under_flow "check_overflow_mul"
    | Div -> check_zero_division
  in
  let second_arg_eval =
    [mov_rax_to_rbp] @
    compiled_e2 @  
    [iMov_arg_arg (rbp_pointer next_slot) rax] @
    safe_env_checker @
    [iMov_arg_arg rax rbp_ptr] @
    binop_to_instr op next_slot tag tag_fun
  in
  compiled_e1
  @ (begin match op with
      | And -> binop_boolean_to_instr_list second_arg_eval tag tag_fun false
      | Add | Sub | Lte -> second_arg_eval
      | Mul -> second_arg_eval @ [iSar rax mul_div_shift_correction]
      | Div -> second_arg_eval @ [iSal rax mul_div_shift_correction]
      | Get -> second_arg_eval (* falta check de la tupla *)
    end)
(* Compiles a let binding. *)
and compile_let (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (x : string) (v : tag texpr) (e : tag texpr) : instruction list =
  let rbp_ptr = rbp_pointer slot in
  let next_slot = (Int64.add 1L slot) in
  let mov_rax_to_rbp = iMov_arg_arg rbp_ptr rax in
  let new_slot_env : slot_env = extend_slot_env x slot slot_env in
    (compile_expr v slot_env slot fenv tag_fun total_params)
    @ [mov_rax_to_rbp]
    @ (compile_expr e new_slot_env next_slot fenv tag_fun total_params)
(* Compiles an if statement *)
and compile_if (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (cond : tag texpr) (thn : tag texpr) (els : tag texpr) (tag : int) : instruction list =
  let else_label = sprintf "if_false_%d_%d" tag_fun tag in
  let done_label = sprintf "done_%d_%d" tag_fun tag in
  let compile_e (e : tag texpr) : instruction list = compile_expr e slot_env slot fenv tag_fun total_params in
  (compile_e cond) @ (check_rax_is_bool_instr slot) @
  [
    iCmp_arg_const rax (bool_to_int false);
    i_je else_label
  ]
  @ (compile_e thn)
  @ [ i_jmp done_label; i_label else_label ]
  @ (compile_e els)
  @ [ i_label done_label ]
(* Compiles a function call. *)
and compile_apply (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (nm : string) (args : tag texpr list) : instruction list =
  let largs = List.length args in
  let (_, _) = lookup_comp_fenv nm largs fenv in
  let rec compiles_and_push (args : tag texpr list) (actual_param : int) : instruction list =
    match args with
    | [] -> []
    | id::tl -> 
      compiles_and_push tl (actual_param + 1)
      @ compile_expr id slot_env slot fenv tag_fun total_params
      @ (if actual_param > 6 then [iPush rax] else [(move_arg_1_to_6 actual_param rax)])
  in
  let remove_params_7_to_m : instruction list =
    if largs > 6 then [(iAdd_arg_const rsp (Int64.of_int (8 * (largs - 6))))] else []
  in
  (store_r10_r11) 
  @ (store_first_6_args) 
  @ (compiles_and_push args 1) 
  @ [iCall_string nm] 
  @ remove_params_7_to_m
  @ pop_first_6_args
  @ pop_r10_r11
(* Compilation of tuple creation. *)
and compile_tuple (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (attrs : tag texpr list) : instruction list =
  let next_slot = (Int64.add 1L slot) in
  let compile_tuple_help (lst : tag texpr list) : instruction list =
    let rec compile_lexpr (lst : tag texpr list) (param_pos : int) : instruction list =
      match lst with
      | [] -> []
      | hd::tl -> (compile_expr hd slot_env next_slot fenv tag_fun total_params) @
                  [iMov_arg_arg (Ptr (R11, (Int64.of_int param_pos))) rax] @
                  (compile_lexpr tl (param_pos + 1))
    in
    [
      iPush r11 ;
      iMov_arg_arg r11 r15 ;
      iMov_arg_const (Ptr (R11, 0L)) (Int64.of_int (4 * (List.length attrs))) ;
      iAdd_arg_const r15 (Int64.of_int (8 * (List.length attrs + 1)))
    ] @
    (compile_lexpr lst 1) @
    [
      iMov_arg_to_RAX r11 ;
      iAdd_arg_const rax 1L ;
      iPop r11
    ]
  in
  (compile_tuple_help attrs) @
  [
    iAdd_arg_const r15 7L ;
    iPush r11 ;
    iMov_arg_const r11 (Int64.mul Int64.minus_one 8L) ;
    iAnd_arg_arg r15 r11 ; 
    iPop r11
  ]
(* Compilation of the set tuple value *)
and compile_set (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (t : tag texpr) (pos : tag texpr) (value : tag texpr) : instruction list =
  let rbp_ptr = rbp_pointer slot in
  let next_slot = (Int64.add 1L slot) in
  let compiled_t = compile_expr t slot_env slot fenv tag_fun total_params in 
  let compiled_pos = compile_expr pos slot_env next_slot fenv tag_fun total_params in
  let compiled_value = compile_expr value slot_env (Int64.sub next_slot 1L) fenv tag_fun total_params in 
  let check_index_range = [
    iCmp_arg_const r11 0L ;
    IJl "index_too_low" ;
    iCmp_arg_arg r11 (Ptr(R10, 0L)) ;
    IJge "index_too_high"
  ]
  in
  compiled_t @
  (check_rax_is_tuple_instr slot) @
  compiled_pos @
  [
    iMov_arg_arg (rbp_pointer next_slot) rax ; 
    iMov_arg_arg rax (rbp_pointer next_slot)
  ] @
  (check_rax_is_int_instr next_slot) @
  compiled_value @
  [
    iMov_arg_arg (rbp_pointer (Int64.sub next_slot 1L)) rax ;
    iPush r10 ;
    iPush r11 ;
    iMov_arg_arg r10 rbp_ptr ;
    iSub_arg_const r10 1L ;
    iMov_arg_arg r11 (rbp_pointer next_slot) 
  ] @
  check_index_range @
    (*iCmp_arg_const r11 0L ;
    IJl "index_too_low" ;
    iCmp_arg_arg r11 (Ptr(R10, 0L)) ;
    IJge "index_too_high" ;*)
  [
    iSar r11 2L ;
    iAdd_arg_const r11 1L ;
    iSal r11 3L ;
    iAdd_arg_arg r10 r11 ;
    iMov_arg_arg r11 (rbp_pointer (Int64.sub next_slot 1L)) ;
    iMov_arg_arg (Ptr(R10, 0L)) r11 ;
    iPop r11 ;
    iPop r10 ;
    iMov_arg_to_RAX rbp_ptr
  ] 
and compile_lambda (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (arg_names : string list) (e : tag texpr) (t : tag) : instruction list =
  let start_lambda = (sprintf "lambda_%d_%d" tag_fun t) in 
  let end_lambda = (sprintf "lambda_%d_%d_end" tag_fun t) in
  let add_int64 (a : int64) (b : int64) : int64 = Int64.add a b in
  let cant_vars, lambda_env = count_vars e [] arg_names slot_env in
  let remove_duplicate (lst : string list) : string list =
    let rec is_member (name : string) (lst : string list) : bool = 
      match lst with
      | [] -> false
      | hd::tl -> 
        if hd = name then true
        else is_member name tl 
    in
    let rec loop (lst : string list) : string list =
      match lst with
      | [] -> []
      | hd::tl -> (*clean_lambda_env*)
        begin
          let result = loop tl in 
          if is_member hd result then result
          else hd::tl
        end
    in
    loop lst
  in
  let clean_lambda_env = remove_duplicate lambda_env in
  let rec allocate_vars (lst : string list) (pos : int64): instruction list =
    match lst with
    | [] -> []
    | hd::tl -> 
      (compile_tid slot_env hd) @
      [iMov_arg_arg (Ptr(R11, (add_int64 3L pos))) rax] @
      allocate_vars tl (add_int64 pos 1L)
  in
  let rec free_var_to_stack (lst : string list) (slot_env : slot_env) (pos : int64) : instruction list * slot_env =
    match lst with
    | [] -> ([], slot_env)
    | hd::tl -> 
      let allocations, new_slot_env = 
        free_var_to_stack tl (extend_slot_env hd pos slot_env) (Int64.sub pos 1L)
      in
      let pos_heap = add_int64 2L (Int64.mul pos (-1L)) in
      let mov_free_var =
        [
         iMov_arg_arg rax (Ptr(R11, pos_heap)) ;
         iMov_arg_arg (Ptr(RBP, pos)) rax 
        ]
      in 
      (mov_free_var @ allocations, new_slot_env)
  in
  let rec add_args_to_env (arg_ids : string list) (slot : int64) : slot_env =
    match arg_ids with
    | [] -> empty_slot_env
    | arg :: tl -> extend_slot_env arg slot (add_args_to_env tl (Int64.add slot 1L))
  in
  let storage_of_free_vars, new_slot_env = free_var_to_stack clean_lambda_env slot_env (-1L) in
  let new_slot_env = (add_args_to_env arg_names 2L) @ new_slot_env in
  let n_local_vars = count_exprs e in
  let closure_lambda =
    [
     iPush r11;
     iMov_arg_arg r11 r15;
     iAdd_arg_const r15 (Int64.mul 8L (Int64.add 3L cant_vars));
     iMov_arg_const (Ptr(R11, 0L)) (Int64.of_int (List.length arg_names));
     IMov((Ptr(R11, 1L)), FLabel start_lambda);
     iMov_arg_const (Ptr(R11, 2L)) cant_vars;
    ] @ 
    allocate_vars clean_lambda_env 0L @
    [
     iMov_arg_to_RAX r11;
     iAdd_arg_const rax lambda_tag;
     iPop r11;
    ] 
  in 
  let new_slot_value = (Int64.add (Int64.mul cant_vars (-1L)) (-1L)) in
  [
   i_jmp end_lambda ;
   i_label start_lambda ; 
   iPush rbp ;
   iMov_arg_arg rbp rsp ;
   iSub_arg_const rsp (Int64.mul 8L cant_vars) ;
   iPush r11 ;
   iMov_arg_arg r11 rdi ;
   iSub_arg_const r11 lambda_tag ;
  ] @
  storage_of_free_vars @
  [
   iSub_arg_const rsp (Int64.mul 8L (n_local_vars));
   iPop r11;
  ] @
  compile_expr e new_slot_env new_slot_value fenv tag_fun total_params @
  [
   iMov_arg_arg rsp rbp ;
   iPop rbp ;
   IRet ;
   i_label end_lambda;
  ] @
  closure_lambda
(* Compiles a first class function application*)
and compile_lamapply (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (lbd : tag texpr) (args : tag texpr list) : instruction list = 
  let largs = List.length args in
  let rec compiles_and_push (args : tag texpr list) (actual_param : int) : instruction list =
    match args with
    | [] -> []
    | id::tl -> 
      compiles_and_push tl (actual_param + 1)
      @ compile_expr id slot_env slot fenv tag_fun total_params
      @ (if actual_param > 6 then [iPush rax] else [(move_arg_1_to_6 actual_param rax)])
  in
  let remove_params_6_to_m : instruction list =
    if largs > 5 then [(iAdd_arg_const rsp (Int64.of_int (8 * ((largs + 1) - 6))))] else []
  in
  (compile_expr lbd slot_env slot fenv tag_fun total_params) @
  (check_rax_is_lambda_instr slot) @
  [
    iPush r11 ;
    iMov_arg_arg r11 rax ;
    iSub_arg_const rax lambda_tag ;
    iCmp_arg_const (Ptr(RAX, 0L)) (Int64.of_int largs) ;
    iPush r10 ;
    iMov_arg_const r10 (Int64.of_int largs) ;
    i_jne "error_wrong_arity" ;
    iPop r10 ;
  ] @
  (store_r10_r11) @
  (store_first_6_args) @
  [iMov_arg_arg rdi r11] @
  [iMov_arg_arg r11 rax] @
  (compiles_and_push args 2) @
  [iCall_reg (Ptr(R11, 1L))] @
  (remove_params_6_to_m) @
  (pop_first_6_args) @
  (pop_r10_r11) @
  [iPop r11]
(* compiles a set of recursive first class function definitions *)
and compile_letrec (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) (lbds : (string * string list * tag texpr * tag) list) (e : tag texpr) : instruction list =
  let next_slot = (Int64.add 1L slot) in
  let rec extend_env_with_lbds (lbds : (string * string list * tag texpr * tag) list) (slot : int64) (new_slot_env : slot_env) : slot_env =
    match lbds with
    | [] -> new_slot_env
    | (nm, _, _, _)::tl -> 
      let aux_slot_env = extend_env_with_lbds tl (Int64.add slot (-1L)) new_slot_env in 
      extend_slot_env nm slot aux_slot_env
  in
  let recs_in_slot_env = extend_env_with_lbds lbds next_slot empty_slot_env in 
  let slot = (Int64.sub slot (Int64.of_int ((List.length recs_in_slot_env) + 1))) in 
  let final_slot_env = recs_in_slot_env @ slot_env in
  let rec compile_lbds (lbds : (string * string list * tag texpr * tag) list) : instruction list = 
    match lbds with
    | [] -> []
    | (nm, args, e, tag)::tl -> 
      (compile_expr (TLambda(args,e,tag)) final_slot_env slot fenv tag_fun total_params) @
      [iMov_arg_arg (Ptr(RBP, slot_env_lookup nm recs_in_slot_env)) rax] @
      compile_lbds tl
  in
  let rec modify_free_vars (lbds : (string * string list * tag texpr * tag) list) : instruction list = 
    match lbds with
    | [] -> []
    | (nm, arg_names, e, _):: tl ->
      let slot_lambda = slot_env_lookup nm recs_in_slot_env in
      let _, free_vars_in_lambda = count_vars e [] arg_names final_slot_env in
      let rec found_and_compile (recs : slot_env) = 
        let index_of (nm : string) (free_vars : string list) = 
          let rec index_rec (i : int) (free_vars : string list) = 
            match free_vars with
            | [] -> -1
            | hd::tl -> if hd = nm then i else index_rec (i+1) tl
          in
          index_rec 0 free_vars
        in 
        match recs with
        | [] -> []
        | (nm_rec, st)::tl ->
          let pos = index_of nm_rec free_vars_in_lambda in
          let instruct = 
            if pos = -1
            then []
            else 
              [
               iPush r11 ;
               iPush r10 ;
               iMov_arg_arg r11 (Ptr(RBP, st)) ;
               iMov_arg_arg r10 (Ptr(RBP, slot_lambda)) ;
               iSub_arg_const r10 3L;
               iMov_arg_arg (Ptr(R10, (Int64.add 3L (Int64.of_int pos)))) r11 ;
               iPop r10 ;
               iPop r11 ;
              ] 
          in 
          instruct @
          found_and_compile tl
      in
      (found_and_compile recs_in_slot_env) @
      modify_free_vars tl 
  in
  compile_lbds lbds @
  modify_free_vars lbds @
  compile_expr e final_slot_env slot fenv tag_fun total_params
(* Main compile function.
    arguments:
      e: expression to be compiled
      slot_env: identifier reference environment
      slot: the 8-byte stack slot which currently holds the lastly saved reference.
      fenv: the functions environment
      tag_fun:
      total_params:
    returns:
      the abstract syntax of the NASM code. *)
and compile_expr (e : tag texpr) (slot_env : slot_env) (slot : int64) (fenv : comp_fenv) (tag_fun : tag) (total_params : int) : instruction list =
  (*let next_slot = (Int64.sub slot 1L) in*)
  (*let rbp_ptr = rbp_pointer slot in*)
  (*let mov_rax_to_rbp = iMov_arg_arg rbp_ptr rax in*)
  (* Compiles the value binding to an identifier. *)
  (*let compile_tid (s : string) : instruction list =
    let pos_stack = slot_env_lookup s slot_env in 
    let search_var = if (0L >= pos_stack)
                     then rbp_pointer pos_stack
                     else if (pos_stack > 6L)
                     then rbp_pointer (Int64.sub pos_stack 5L)
                     else (Reg (int_to_cc64_reg (Int64.to_int pos_stack))) 
    in    
    [iMov_arg_to_RAX (search_var)]
  in*)
  (* Compiles a unary operation. *)
  (*let compile_prim1 (op: prim1) (n: tag texpr) : instruction list =
    let compiled_n = (compile_expr n slot_env slot fenv tag_fun total_params) in
    let check_over_under_flow (checker_name : string) : instruction list = 
      store_r10_r11 @
      store_first_6_args @
      [
        iMov_arg_arg rdi rax; 
        iMov_arg_const rsi one ; 
        iCall_string checker_name ; 
        iMov_arg_arg rax (rbp_pointer slot)
      ] @
      pop_first_6_args @
      pop_r10_r11 
    in
    (compiled_n) @ (type_of_unops op slot)
    @ (begin match op with
        | Add1 -> check_over_under_flow "check_overflow_add"
        | Sub1 -> check_over_under_flow "check_overflow_sub"
        | _ -> []
      end)
    @ (unop_to_instr_list op)
  in*)
  (* Compiles a binary operation. *)
  (*let compile_prim2 (op : prim2) (n1 : tag texpr) (n2 : tag texpr) (tag : int) : instruction list =
    let compile_e (n : tag texpr) (slot : int64): instruction list = compile_expr n slot_env slot fenv tag_fun total_params in
    let compiled_e1 = compile_e n1 slot @ type_of_binops op slot in
    let compiled_e2 = compile_e n2 next_slot @ type_of_binops op next_slot in 
    let check_over_under_flow (checker_name : string) : instruction list =   
      store_r10_r11 @
      store_first_6_args @
      [
        iMov_arg_arg rdi rbp_ptr; 
        iMov_arg_arg rsi (rbp_pointer next_slot) ; 
        iCall_string (checker_name) ;
      ] @
      pop_first_6_args @
      pop_r10_r11 
    in
    let check_zero_division : instruction list = 
      store_r10_r11 @
      store_first_6_args @
      [
        iMov_arg_arg rdi (rbp_pointer next_slot) ; 
        iCall_string ("check_div_by_0") ; 
      ] @
      pop_first_6_args @
      pop_r10_r11 
    in
    let safe_env_checker : instruction list =
      match op with
      | And | Lte | Get -> []
      | Add -> check_over_under_flow "check_overflow_add"
      | Sub -> check_over_under_flow "check_overflow_sub"
      | Mul -> check_over_under_flow "check_overflow_mul"
      | Div -> check_zero_division
    in
    let second_arg_eval =
      [mov_rax_to_rbp] @
      compiled_e2 @  
      [iMov_arg_arg (rbp_pointer next_slot) rax] @
      safe_env_checker @
      [iMov_arg_arg rax rbp_ptr] @
      binop_to_instr op next_slot tag tag_fun
    in
    compiled_e1
    @ (begin match op with
        | And -> binop_boolean_to_instr_list second_arg_eval tag tag_fun false
        | Add | Sub | Lte -> second_arg_eval
        | Mul -> second_arg_eval @ [iSar rax mul_div_shift_correction]
        | Div -> second_arg_eval @ [iSal rax mul_div_shift_correction]
        | Get -> second_arg_eval (* falta check de la tupla *)
      end)
  in*)
  (* Compiles a let binding. *)
  (*let compile_let (x : string) (v : tag texpr) (e : tag texpr) : instruction list =
    let new_slot_env : slot_env = extend_slot_env x slot slot_env in
      (compile_expr v slot_env slot fenv tag_fun total_params)
      @ [mov_rax_to_rbp]
      @ (compile_expr e new_slot_env next_slot fenv tag_fun total_params)
  in*)
  (* Compiles an if statement *)
  (*let compile_if (cond : tag texpr) (thn : tag texpr) (els : tag texpr) (tag : int) : instruction list =
    let else_label = sprintf "if_false_%d_%d" tag_fun tag in
    let done_label = sprintf "done_%d_%d" tag_fun tag in
    let compile_e (e : tag texpr) : instruction list = compile_expr e slot_env slot fenv tag_fun total_params in
    (compile_e cond) @ (check_rax_is_bool_instr slot) @
    [
      iCmp_arg_const rax (bool_to_int false);
      i_je else_label
    ]
    @ (compile_e thn)
    @ [ i_jmp done_label; i_label else_label ]
    @ (compile_e els)
    @ [ i_label done_label ]
  in*)
  (* Compiles a function call. *)
  (*let compile_apply (nm : string) (args : tag texpr list) : instruction list =
    let largs = List.length args in
    let (_, _) = lookup_comp_fenv nm largs fenv in
    let rec compiles_and_push (args : tag texpr list) (actual_param : int) : instruction list =
      match args with
      | [] -> []
      | id::tl -> 
        compiles_and_push tl (actual_param + 1)
        @ compile_expr id slot_env slot fenv tag_fun total_params
        @ (if actual_param > 6 then [iPush rax] else [(move_arg_1_to_6 actual_param rax)])
    in
    let remove_params_7_to_m : instruction list =
      if largs > 6 then [(iAdd_arg_const rsp (Int64.of_int (8 * (largs - 6))))] else []
    in
    (store_r10_r11) 
    @ (store_first_6_args) 
    @ (compiles_and_push args 1) 
    @ [iCall_string nm] 
    @ remove_params_7_to_m
    @ pop_first_6_args
    @ pop_r10_r11
  in*)
  (* Compilation of tuple creation. *)
  (*let compile_tuple (attrs : tag texpr list) : instruction list =
    let compile_tuple_help (lst : tag texpr list) : instruction list =
      let rec compile_lexpr (lst : tag texpr list) (param_pos : int) : instruction list =
        match lst with
        | [] -> []
        | hd::tl -> (compile_expr hd slot_env next_slot fenv tag_fun total_params) @
                    [iMov_arg_arg (Ptr (R11, (Int64.of_int param_pos))) rax] @
                    (compile_lexpr tl (param_pos + 1))
      in
      [
        iPush r11 ;
        iMov_arg_arg r11 r15 ;
        iMov_arg_const (Ptr (R11, 0L)) (Int64.of_int (4 * (List.length attrs))) ;
        iAdd_arg_const r15 (Int64.of_int (8 * (List.length attrs + 1)))
      ] @
      (compile_lexpr lst 1) @
      [
        iMov_arg_to_RAX r11 ;
        iAdd_arg_const rax 1L ;
        iPop r11
      ]
    in
    (compile_tuple_help attrs) @
    [
      iAdd_arg_const r15 7L ;
      iPush r11 ;
      iMov_arg_const r11 (Int64.mul Int64.minus_one 8L) ;
      iAnd_arg_arg r15 r11 ; 
      iPop r11
    ]
  in*)
  (* Compilation of the set tuple value *)
  (*let compile_set (t : tag texpr) (pos : tag texpr) (value : tag texpr) : instruction list =
    let compiled_t = compile_expr t slot_env slot fenv tag_fun total_params in 
    let compiled_pos = compile_expr pos slot_env next_slot fenv tag_fun total_params in
    let compiled_value = compile_expr value slot_env (Int64.sub next_slot 1L) fenv tag_fun total_params in 
    let check_index_range = [
      iCmp_arg_const r11 0L ;
      IJl "index_too_low" ;
      iCmp_arg_arg r11 (Ptr(R10, 0L)) ;
      IJge "index_too_high"
    ]
    in
    compiled_t @
    (check_rax_is_tuple_instr slot) @
    compiled_pos @
    [
      iMov_arg_arg (rbp_pointer next_slot) rax ; 
      iMov_arg_arg rax (rbp_pointer next_slot)
    ] @
    (check_rax_is_int_instr next_slot) @
    compiled_value @
    [
      iMov_arg_arg (rbp_pointer (Int64.sub next_slot 1L)) rax ;
      iPush r10 ;
      iPush r11 ;
      iMov_arg_arg r10 rbp_ptr ;
      iSub_arg_const r10 1L ;
      iMov_arg_arg r11 (rbp_pointer next_slot) 
    ] @
    check_index_range @
      (*iCmp_arg_const r11 0L ;
      IJl "index_too_low" ;
      iCmp_arg_arg r11 (Ptr(R10, 0L)) ;
      IJge "index_too_high" ;*)
    [
      iSar r11 2L ;
      iAdd_arg_const r11 1L ;
      iSal r11 3L ;
      iAdd_arg_arg r10 r11 ;
      iMov_arg_arg r11 (rbp_pointer (Int64.sub next_slot 1L)) ;
      iMov_arg_arg (Ptr(R10, 0L)) r11 ;
      iPop r11 ;
      iPop r10 ;
      iMov_arg_to_RAX rbp_ptr
    ] 
  in*)
  (*let rec exist_var_slot_env (name : string) (slot_env : slot_env): bool =
    match slot_env with
    | [] -> false
    | (n, _) :: rest -> if (n = name) then true else (exist_var_slot_env name rest)
  in 
  let rec var_is_a_param (name : string) (arg_names : string list) : bool =
    match arg_names with
    | [] -> false
    | n:: rest -> if (n = name) then true else (var_is_a_param name rest)
  in 
  let count_vars (e_l : tag texpr) (inner_scope : string list) (arg_names : string list) (slot_env : slot_env) : int64 * string list =
    let add_int64 (a : int64) (b : int64) : int64 = Int64.add a b in
    let triple_add_int64 (a : int64) (b : int64) (c : int64) : int64 = add_int64 (add_int64 a b) c in
    let rec real_count_vars (e_l : tag texpr) (inner_scope : string list) : int64 * string list =
      match e_l with
      | TId (s, _) -> 
        if (exist_var_slot_env s slot_env)
        then 
          if not (var_is_a_param s arg_names)
          then (if not (var_is_a_param s inner_scope)
                then (1L, [s])
                else (0L, [])) 
          else (0L, [])
        else (0L, [])
      | TNum (_, _) | TBool (_, _) -> (0L, [])
      | TPrim1 (_, n, _) -> 
        let sum, lambda_env = real_count_vars n inner_scope in
        (sum, lambda_env)
      | TLet (nm, e1, e2, _) ->
        let sum1, lambda_env1 = (real_count_vars e1 inner_scope) in
        let sum2, lambda_env2 = (real_count_vars e2 (nm::inner_scope)) in
        (add_int64 sum1 sum2, lambda_env1 @ lambda_env2) 
      | TPrim2 (_, e1, e2, _) ->
        let sum1, lambda_env1 = (real_count_vars e1 inner_scope) in
        let sum2, lambda_env2 = (real_count_vars e2 inner_scope) in
        (add_int64 sum1 sum2, lambda_env1 @ lambda_env2) 
      | TIf(cond, thn, els, _) -> 
        let sum_cond, lambda_env_cond = (real_count_vars cond inner_scope) in
        let sum_thn, lambda_env_thn = (real_count_vars thn inner_scope) in
        let sum_els, lambda_env_els = (real_count_vars els inner_scope) in
        (triple_add_int64 sum_cond sum_thn sum_els, lambda_env_cond @ lambda_env_thn @ lambda_env_els)
      | TApply(_, args, _) -> 
        let rec count_apply_vars (e_list : tag texpr list) : int64 * string list =
          match e_list with
          | [] -> (0L, [])
          | hd::tl -> 
            let sum_hd, lambda_env_hd = (real_count_vars hd inner_scope) in
            let sum_tl, lambda_env_tl = (count_apply_vars tl) in
            (add_int64 sum_hd sum_tl, lambda_env_hd @ lambda_env_tl)
        in
        count_apply_vars args
      | TTuple(attrs, _) -> 
        let rec count_tuple_vars (e_list : tag texpr list) : int64 * string list =
          match e_list with
          | [] -> (0L, [])
          | hd::tl -> 
            let sum_hd, lambda_env_hd = (real_count_vars hd inner_scope) in
            let sum_tl, lambda_env_tl = (count_tuple_vars tl) in
            (add_int64 sum_hd sum_tl, lambda_env_hd @ lambda_env_tl)
        in
        count_tuple_vars attrs
      | TSet(t, pos, value, _) ->
        let sum_t, lambda_env_t = (real_count_vars t inner_scope) in
        let sum_pos, lambda_env_pos = (real_count_vars pos inner_scope) in
        let sum_value, lambda_env_value = (real_count_vars value inner_scope) in
        (triple_add_int64 sum_t sum_pos sum_value, lambda_env_t @ lambda_env_pos @ lambda_env_value)
      | TLambda(_, e, _) ->
        let sum, lambda_env = real_count_vars e inner_scope in
        (sum, lambda_env)  
      | TLamApply(lbd, e, _) ->
        let rec count_apply_vars (e_list : tag texpr list) : int64 * string list =
          match e_list with
          | [] -> (0L, [])
          | hd::tl -> 
            let sum_hd, lambda_env_hd = (real_count_vars hd inner_scope) in
            let sum_tl, lambda_env_tl = (count_apply_vars tl) in
            (add_int64 sum_hd sum_tl, lambda_env_hd @ lambda_env_tl)
        in
        let sum_lbd, lambda_env_lbd = (real_count_vars lbd inner_scope) in
        let sum_e, lambda_env_e = (count_apply_vars e) in
        (add_int64 sum_lbd sum_e, lambda_env_lbd @ lambda_env_e)
      | TLetRec(lbds, e, _) ->
        let rec count_lbds_vars (lbds_list : (string * string list * tag texpr * 'a) list) : int64 * string list =
          match lbds_list with
          | [] -> (0L, [])
          | (_, _, e, _)::tl -> 
            let sum_e, lambda_env_e = (real_count_vars e inner_scope) in
            let sum_tl, lambda_env_tl = (count_lbds_vars tl) in
            (add_int64 sum_e sum_tl, lambda_env_e @ lambda_env_tl)
        in 
        let sum_lbds, lambda_env_lbds = (count_lbds_vars lbds) in
        let sum_e, lambda_env_e = (real_count_vars e inner_scope) in
        (add_int64 sum_lbds sum_e, lambda_env_lbds @ lambda_env_e)
    in 
    real_count_vars e_l inner_scope
  in  
  let compile_lambda (arg_names : string list) (e : tag texpr) (t : tag) : instruction list =
    let start_lambda = (sprintf "lambda_%d_%d" tag_fun t) in 
    let end_lambda = (sprintf "lambda_%d_%d_end" tag_fun t) in
    let add_int64 (a : int64) (b : int64) : int64 = Int64.add a b in
    let cant_vars, lambda_env = count_vars e [] arg_names slot_env in
    let remove_duplicate (lst : string list) : string list =
      let rec is_member (name : string) (lst : string list) : bool = 
        match lst with
        | [] -> false
        | hd::tl -> 
          if hd = name then true
          else is_member name tl 
      in
      let rec loop (lst : string list) : string list =
        match lst with
        | [] -> []
        | hd::tl -> (*clean_lambda_env*)
          begin
            let result = loop tl in 
            if is_member hd result then result
            else hd::tl
          end
      in
      loop lst
    in
    let clean_lambda_env = remove_duplicate lambda_env in
    let rec allocate_vars (lst : string list) (pos : int64): instruction list =
      match lst with
      | [] -> []
      | hd::tl -> 
        (compile_tid hd) @
        [iMov_arg_arg (Ptr(R11, (add_int64 3L pos))) rax] @
        allocate_vars tl (add_int64 pos 1L)
    in
    let rec free_var_to_stack (lst : string list) (slot_env : slot_env) (pos : int64) : instruction list * slot_env =
      match lst with
      | [] -> ([], slot_env)
      | hd::tl -> 
        let allocations, new_slot_env = 
          free_var_to_stack tl (extend_slot_env hd pos slot_env) (Int64.sub pos 1L)
        in
        let pos_heap = add_int64 2L (Int64.mul pos (-1L)) in
        let mov_free_var =
          [
           iMov_arg_arg rax (Ptr(R11, pos_heap)) ;
           iMov_arg_arg (Ptr(RBP, pos)) rax 
          ]
        in 
        (mov_free_var @ allocations, new_slot_env)
    in
    let rec add_args_to_env (arg_ids : string list) (slot : int64) : slot_env =
      match arg_ids with
      | [] -> empty_slot_env
      | arg :: tl -> extend_slot_env arg slot (add_args_to_env tl (Int64.add slot 1L))
    in
    let storage_of_free_vars, new_slot_env = free_var_to_stack clean_lambda_env slot_env (-1L) in
    let new_slot_env = (add_args_to_env arg_names 2L) @ new_slot_env in
    let n_local_vars = count_exprs e in
    let closure_lambda =
      [
       iPush r11;
       iMov_arg_arg r11 r15;
       iAdd_arg_const r15 (Int64.mul 8L (Int64.add 3L cant_vars));
       iMov_arg_const (Ptr(R11, 0L)) (Int64.of_int (List.length arg_names));
       IMov((Ptr(R11, 1L)), FLabel start_lambda);
       iMov_arg_const (Ptr(R11, 2L)) cant_vars;
      ] @ 
      allocate_vars clean_lambda_env 0L @
      [
       iMov_arg_to_RAX r11;
       iAdd_arg_const rax lambda_tag;
       iPop r11;
      ] 
    in 
    let new_slot_value = (Int64.add (Int64.mul cant_vars (-1L)) (-1L)) in
    [
     i_jmp end_lambda ;
     i_label start_lambda ; 
     iPush rbp ;
     iMov_arg_arg rbp rsp ;
     iSub_arg_const rsp (Int64.mul 8L cant_vars) ;
     iPush r11 ;
     iMov_arg_arg r11 rdi ;
     iSub_arg_const r11 lambda_tag ;
    ] @
    storage_of_free_vars @
    [
     iSub_arg_const rsp (Int64.mul 8L (n_local_vars));
     iPop r11;
    ] @
    compile_expr e new_slot_env new_slot_value fenv tag_fun total_params @
    [
     iMov_arg_arg rsp rbp ;
     iPop rbp ;
     IRet ;
     i_label end_lambda;
    ] @
    closure_lambda
  in*)
  (*let compile_lamapply (lbd : tag texpr) (args : tag texpr list) : instruction list = 
    let largs = List.length args in
    let rec compiles_and_push (args : tag texpr list) (actual_param : int) : instruction list =
      match args with
      | [] -> []
      | id::tl -> 
        compiles_and_push tl (actual_param + 1)
        @ compile_expr id slot_env slot fenv tag_fun total_params
        @ (if actual_param > 6 then [iPush rax] else [(move_arg_1_to_6 actual_param rax)])
    in
    let remove_params_6_to_m : instruction list =
      if largs > 5 then [(iAdd_arg_const rsp (Int64.of_int (8 * ((largs + 1) - 6))))] else []
    in
    (compile_expr lbd slot_env slot fenv tag_fun total_params) @
    (check_rax_is_lambda_instr slot) @
    [
      iPush r11 ;
      iMov_arg_arg r11 rax ;
      iSub_arg_const rax lambda_tag ;
      iCmp_arg_const (Ptr(RAX, 0L)) (Int64.of_int largs) ;
      iPush r10 ;
      iMov_arg_const r10 (Int64.of_int largs) ;
      i_jne "error_wrong_arity" ;
      iPop r10 ;
    ] @
    (store_r10_r11) @
    (store_first_6_args) @
    [iMov_arg_arg rdi r11] @
    [iMov_arg_arg r11 rax] @
    (compiles_and_push args 2) @
    [iCall_reg (Ptr(R11, 1L))] @
    (remove_params_6_to_m) @
    (pop_first_6_args) @
    (pop_r10_r11) @
    [iPop r11]
  in *)
  (*let compile_letrec (lbds : (string * string list * tag texpr * tag) list) (e : tag texpr) : instruction list =
    let rec extend_env_with_lbds (lbds : (string * string list * tag texpr * tag) list) (slot : int64) (new_slot_env : slot_env) : slot_env =
      match lbds with
      | [] -> new_slot_env
      | (nm, _, _, _)::tl -> 
        let aux_slot_env = extend_env_with_lbds tl (Int64.add slot (-1L)) new_slot_env in 
        extend_slot_env nm slot aux_slot_env
    in
    let recs_in_slot_env = extend_env_with_lbds lbds next_slot empty_slot_env in 
    let slot = (Int64.sub slot (Int64.of_int ((List.length recs_in_slot_env) + 1))) in 
    let final_slot_env = recs_in_slot_env @ slot_env in
    let rec compile_lbds (lbds : (string * string list * tag texpr * tag) list) : instruction list = 
      match lbds with
      | [] -> []
      | (nm, args, e, tag)::tl -> 
        (compile_expr (TLambda(args,e,tag)) final_slot_env slot fenv tag_fun total_params) @
        [iMov_arg_arg (Ptr(RBP, slot_env_lookup nm recs_in_slot_env)) rax] @
        compile_lbds tl
    in
    let rec modify_free_vars (lbds : (string * string list * tag texpr * tag) list) : instruction list = 
      match lbds with
      | [] -> []
      | (nm, arg_names, e, _):: tl ->
        let slot_lambda = slot_env_lookup nm recs_in_slot_env in
        let _, free_vars_in_lambda = count_vars e [] arg_names final_slot_env in
        let rec found_and_compile (recs : slot_env) = 
          let index_of (nm : string) (free_vars : string list) = 
            let rec index_rec (i : int) (free_vars : string list) = 
              match free_vars with
              | [] -> -1
              | hd::tl -> if hd = nm then i else index_rec (i+1) tl
            in
            index_rec 0 free_vars
          in 
          match recs with
          | [] -> []
          | (nm_rec, st)::tl ->
            let pos = index_of nm_rec free_vars_in_lambda in
            let instruct = 
              if pos = -1
              then []
              else 
                [
                 iPush r11 ;
                 iPush r10 ;
                 iMov_arg_arg r11 (Ptr(RBP, st)) ;
                 iMov_arg_arg r10 (Ptr(RBP, slot_lambda)) ;
                 iSub_arg_const r10 3L;
                 iMov_arg_arg (Ptr(R10, (Int64.add 3L (Int64.of_int pos)))) r11 ;
                 iPop r10 ;
                 iPop r11 ;
                ] 
            in 
            instruct @
            found_and_compile tl
        in
        (found_and_compile recs_in_slot_env) @
        modify_free_vars tl 
    in
    compile_lbds lbds @
    modify_free_vars lbds @
    compile_expr e final_slot_env slot fenv tag_fun total_params
  in*) 
  (* Main compile instruction here *)
  match e with 
  | TId (s, _) -> compile_tid slot_env s
  | TNum (n, _) -> [iMov_const_to_RAX (Int64.mul n add_int_tag)]
  | TBool (b, _) -> [iMov_const_to_RAX (bool_to_int b)]
  | TPrim1 (op, n, _) -> compile_prim1 slot_env slot fenv tag_fun total_params op n
  | TLet (x, v, e, _) -> compile_let slot_env slot fenv tag_fun total_params x v e
  | TPrim2 (op, n1, n2, tag) -> compile_prim2 slot_env slot fenv tag_fun total_params op n1 n2 tag
  | TIf(cond, thn, els, tag) -> compile_if slot_env slot fenv tag_fun total_params cond thn els tag
  | TApply(nm, args, _) -> compile_apply slot_env slot fenv tag_fun total_params nm args
  | TTuple(attrs, _) -> compile_tuple slot_env slot fenv tag_fun total_params attrs 
  | TSet(t, pos, value, _) -> compile_set slot_env slot fenv tag_fun total_params t pos value 
  | TLambda(arg_names, e, tag) -> compile_lambda slot_env slot fenv tag_fun total_params arg_names e tag
  | TLamApply(lbd, args, _) -> compile_lamapply slot_env slot fenv tag_fun total_params lbd args
  | TLetRec(lbds, e, _) -> compile_letrec slot_env slot fenv tag_fun total_params lbds e
  (*| _ -> failwith "TO BE DONE!"*)

(* Compiles the function definitions. *)
let rec compile_funcs (func_list : tag tfun_def list) (cfenv : comp_fenv) : instruction list * comp_fenv =
  match func_list with
  | [] -> ([], cfenv)
  | TDefFun (name, arg_names, e, tag) :: tail ->
    let extended_comp_fenv : comp_fenv = extend_comp_fenv name arg_names cfenv in
    let (instrs, compd_fenv) = compile_funcs tail extended_comp_fenv in
    let rec add_args_to_env (arg_ids : string list) (slot : int64) : slot_env =
      match arg_ids with
      | [] -> empty_slot_env
      | arg :: tl -> extend_slot_env arg slot (add_args_to_env tl (Int64.add slot 1L))
    in
    let arg_values = add_args_to_env arg_names 1L in
    (
      [i_label name] @
      function_start (count_exprs e) @
      (compile_expr e arg_values Int64.minus_one compd_fenv tag (List.length arg_values)) @
      function_end @
      instrs,
      compd_fenv
    )

(* Prints the program p (given in abstract Scheme syntax) in NASM code. *)
let compile_prog p : string =
  let (tagged_funcs, tagged_main) = tag_prog p in
  let (intrs_funs, cfenv)  = (compile_funcs tagged_funcs (("type_mismatch", [])::empty_comp_fenv)) in 
  let n_lets_main = count_exprs tagged_main in
  let instrs_main = function_start n_lets_main @ compile_expr tagged_main empty_slot_env Int64.minus_one cfenv 0 0 @ function_end in
  let init_heap = "
  mov R15, RDI
  add R15, 7
  mov R11, 0xfffffffffffffff8
  and R15, R11" in
  let prelude ="
section .text
extern check_overflow_add
extern check_overflow_sub
extern check_overflow_mul
extern check_div_by_0
extern indexError
extern print
extern typeError
extern wrongArity
global our_code_starts_here
our_code_starts_here:" in
  let error_section = "
error_not_number:
  push RSI
  push RDI
  mov RSI, RAX
  mov RDI, 0x1
  call typeError
error_not_boolean:
  push RSI
  push RDI
  mov RSI, RAX
  mov RDI, 0x2
  call typeError
error_not_tuple:
  push RSI
  push RDI
  mov RSI, RAX
  mov RDI, 0x3
  call typeError
error_not_lambda:
  push RSI
  push RDI
  mov RSI, RAX
  mov RDI, 0x4
  call typeError
index_too_high:
  push RSI
  push RDI
  mov RDI, R11
  mov RSI, [R10]
  call indexError
error_wrong_arity:
  push RSI
  push RDI
  mov RDI, [R11]
  mov RSI, R10
  call wrongArity
index_too_low:
  push RSI
  push RDI
  mov RDI, R11
  mov RSI, [R10]
  mov RDI, 0
  call indexError" in
  prelude ^ init_heap ^ pp_instrs (instrs_main)^ pp_instrs intrs_funs ^ error_section
