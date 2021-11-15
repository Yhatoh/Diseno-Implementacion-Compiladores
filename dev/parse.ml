(** Parser **)
open Ast
open Printf
open CCSexp

exception CTError of string

(* Applies ANF to a unary operation. *)
let a_normal_form_unop (op : prim1) (arg : expr) : expr =
  (Let ("arg", arg, Prim1 (op, (Id "arg"))))

(* Applies ANF to a binary operation. *)
let a_normal_form_binop (op : prim2) (arg1 : expr) (arg2 : expr) : expr =
  (Let ("arg1", arg1, (Let ("arg2", arg2, Prim2(op, (Id "arg1"), (Id "arg2"))))))

let a_normal_form_ids (arg_list : expr list) : expr list * string list =
  let rec arg_ids_strings (n : int) : string list =
    if n = 0 then [] else (sprintf "arg%s" (string_of_int n)) :: arg_ids_strings (n - 1)
  in

  let len_arg_list = List.length arg_list in
  let ids_strs = arg_ids_strings len_arg_list in
  let arg_ids_exprs : expr list = List.map (fun s -> Id s) ids_strs in
  (arg_ids_exprs, ids_strs)

(* Applies ANF to a function application. *)
let a_normal_form_apply (f_name : string) (arg_list : expr list) : expr =
  let (arg_ids_exprs, ids_strs) = a_normal_form_ids arg_list in

  let rec assign_id_and_execute (f_name : string) (args : expr list) (id_exprs : expr list) (id_strs : string list) : expr =
    match id_strs with
    | [] -> Apply (f_name, id_exprs)
    | s_hd::s_tl ->
      let a_hd::a_tl = args in
      Let (s_hd, a_hd, assign_id_and_execute f_name a_tl id_exprs s_tl)
  in
  assign_id_and_execute f_name arg_list arg_ids_exprs ids_strs

let a_normal_form_tuple (attr_list : expr list) : expr =
  let (arg_ids_exprs, ids_strs) = a_normal_form_ids attr_list in

  let rec assign_id_and_execute (args : expr list) (id_exprs : expr list) (id_strs : string list) : expr =
    match id_strs with
    | [] -> Tuple id_exprs
    | s_hd::s_tl ->let a_hd::a_tl = args in
                   Let (s_hd, a_hd, assign_id_and_execute a_tl id_exprs s_tl)
  in

  assign_id_and_execute attr_list arg_ids_exprs ids_strs


let parse_arg_name (sexp : sexp) : string =
  match sexp with
  | `Atom name -> name
  | _ -> raise (CTError (sprintf "Not a valid argument name: %s" (to_string sexp)))

let rec parse_exp (sexp : sexp) : expr =
  match sexp with
  | `Atom "true" -> Bool true
  | `Atom "false" -> Bool false
  | `Atom s -> (
    match Int64.of_string_opt s with Some n -> Num n | None -> Id s )
  | `List (`Atom "tup" :: exprs) -> a_normal_form_tuple (List.map parse_exp exprs)
  | `List (`Atom "@" :: e1 :: exprs) -> LamApply (parse_exp e1, List.map parse_exp exprs)
  | `List [eop; e] -> (
    match eop with 
    | `Atom "add1" -> Prim1 (Add1, parse_exp e)
    | `Atom "sub1" -> Prim1 (Sub1, parse_exp e)
    | `Atom "not" -> Prim1 (Not, parse_exp e)
    | `Atom "print" -> Prim1 (Print, parse_exp e)  (* comment out this line if providing print via the sys interface *)
    | `Atom name -> a_normal_form_apply (String.concat "_" (String.split_on_char '-' name)) [parse_exp e] (*Apply ((String.concat "_" (String.split_on_char '-' name)), [parse_exp e])*)
    | _ -> raise (CTError (sprintf "Not a valid expr: %s" (to_string sexp)))
    )
  | `List [eop; e1; e2] -> (
    match eop with
    | `Atom "let" -> (
      match e1 with
      | `List [`Atom id; e] -> Let (id, parse_exp e, parse_exp e2)
      | _ -> raise (CTError (sprintf "Not a valid let assignment: %s" (to_string e1))) )
    | `Atom "letrec" -> (
      match e1 with
      | `List recs -> LetRec (parse_recs recs, parse_exp e2)
      | _ -> raise (CTError (sprintf "Not a valid letrec assignment: %s" (to_string e1)))
      )
    | `Atom "+" -> a_normal_form_binop Add (parse_exp e1) (parse_exp e2)(*Prim2 (Add, parse_exp e1, parse_exp e2)*)
    | `Atom "-" -> a_normal_form_binop Sub (parse_exp e1) (parse_exp e2)(*Prim2 (Sub, parse_exp e1, parse_exp e2)*)
    | `Atom "*" -> a_normal_form_binop Mul (parse_exp e1) (parse_exp e2)(*Prim2 (Mul, parse_exp e1, parse_exp e2)*)
    | `Atom "/" -> a_normal_form_binop Div (parse_exp e1) (parse_exp e2)(*Prim2 (Div, parse_exp e1, parse_exp e2)*)
    | `Atom "and" -> a_normal_form_binop And (parse_exp e1) (parse_exp e2)(*Prim2 (And, parse_exp e1, parse_exp e2)*)
    | `Atom "<=" -> a_normal_form_binop Lte (parse_exp e1) (parse_exp e2)(*Prim2 (Lte, parse_exp e1, parse_exp e2)*)
    | `Atom "get" -> a_normal_form_binop Get (parse_exp e1) (parse_exp e2)(*Prim2 (Get, parse_exp e1, parse_exp e2)*)
    | `Atom "lambda" -> (
      match e1 with
      | `List params -> Lambda (List.map parse_arg_name params, parse_exp e2)
      | _ -> raise (CTError (sprintf "Not a valid lambda: %s" (to_string sexp)))
    )
    | `Atom name -> a_normal_form_apply (String.concat "_" (String.split_on_char '-' name)) [parse_exp e1 ; parse_exp e2](*Apply (name, [parse_exp e1 ; parse_exp e2])*)
    | _ -> raise (CTError (sprintf "Not a valid expr: %s" (to_string sexp)))
    )
  | `List [`Atom "if"; e1; e2; e3] -> If (parse_exp e1, parse_exp e2, parse_exp e3)
  | `List [ `Atom "set"; e; k; v ] -> (Let ("arg1", parse_exp e, Let ("arg2", parse_exp k, Let ("arg3", parse_exp v, Set (Id "arg1", Id "arg2", Id "arg3")))))
  | `List (`Atom name :: e2) -> a_normal_form_apply (String.concat "_" (String.split_on_char '-' name)) (List.map parse_exp e2)(*Apply (name, List.map parse_exp e2)*)
  | _ -> raise (CTError (sprintf "Not a valid expr: %s" (to_string sexp)))
and parse_recs (recs : sexp list) : (string * string list * expr) list =
  List.map (
    fun sexp -> (
      match sexp with
      | `List [`Atom name ; r] ->
        let e = parse_exp r in
        (match e with
        | Lambda (params, body) -> name, params, body
        | _ -> raise (CTError (sprintf "Not a valid letrec assignment: %s" (string_of_expr e)))
        )
      | _ -> raise (CTError (sprintf "Not a valid letrec assignment: %s" (to_string sexp)))
    )
  ) recs

let rec create_deffun (name : string) (atris : string list) (pos : int64) : fundef list =
  match atris with
  | [] -> []
  | hd::tl ->
    DefFun (name ^ "_" ^ hd, ["t"], (Let ("arg1", Id "t", (Let ("arg2", Num(pos), Prim2(Get, Id "arg1", Id "arg2"))))))::(create_deffun name tl (Int64.add pos 1L))

let create_id (a : string) : expr =
  Id(a)


let rec parse_prog (sexp : sexp) : prog =
  match sexp with
  | `List (hd :: tl) -> (
    match hd, tl with
    | `List [`Atom "def" ; `List (`Atom name :: args) ; body], _ ->
      let (funcdefs, expr) = parse_prog (`List tl) in
      let arg_names = List.map parse_arg_name args in
      [ DefFun (name, arg_names, parse_exp body) ] @ funcdefs, expr
    | `List (`Atom "record" :: (`Atom name :: atris)), _ ->
      let (funcdefs, expr) = parse_prog (`List tl) in
      let atris_names = List.map parse_arg_name atris in 
      [ DefFun (name, atris_names, Tuple((List.map create_id atris_names))) ] 
      @ (create_deffun name atris_names 0L) 
      @ funcdefs, expr
    (*| `List (`Atom "defsys" :: `Atom name :: arg_spec), _ -> (
      match List.rev arg_spec with
      | (ret :: `Atom "->" :: args) -> 
        let (funcdefs, expr) = parse_prog (`List tl) in
        let arg_types = List.map parse_c_type (List.rev args) in
        let ret_type = parse_c_type ret in
        [ DefSys (name, arg_types, ret_type) ] @ funcdefs, expr
      | _ -> raise (CTError (sprintf "Not a valid type declaration: %s" (to_string (`List arg_spec))))
      ) *)
    | _, [] -> [], parse_exp hd
    | _ -> [], parse_exp sexp
  )
  | _ -> [], parse_exp sexp

and parse_c_type (sexp : sexp) : ctype =
  match sexp with
  | `Atom "any" -> CAny
  | `Atom "int" -> CInt
  | `Atom "bool" -> CBool
  | _ -> raise (CTError (sprintf "Not a valid type declaration: %s" (to_string sexp)))

let sexp_from_file : string -> CCSexp.sexp =
 fun filename ->
  match CCSexp.parse_file filename with
  | Ok s -> s
  | Error msg -> raise (CTError (sprintf "Unable to parse file %s: %s" filename msg))

let sexp_from_string (src : string) : CCSexp.sexp =
  match CCSexp.parse_string src with
  | Ok s -> s
  | Error msg -> raise (CTError (sprintf "Unable to parse string %s: %s" src msg))
