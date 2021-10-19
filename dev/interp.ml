(** Interpreter **)
open Ast

exception RTError of string

(** Values **)
type value = 
  | NumV of int64
  | BoolV of bool
  | TupleV of value list ref

(* Pretty printing *)
let rec string_of_val(v : value) : string =
match v with
| NumV n -> Int64.to_string n
| BoolV b -> if b then "true" else "false"
| TupleV vals -> 
        let rec string_of_val_list =
            fun ls -> (match ls with
            | [] -> ""
            | e::l -> " " ^ string_of_val e ^ string_of_val_list l) in 
        "(tup"^(string_of_val_list !vals)^")"

(* Lexical Environment *)
type env = (string * value) list
let empty_env : env = []

let extend_env (names : string list) (vals : value list) (env : env) : env =
  let param_vals = List.combine names vals in
  List.fold_left (fun env p -> p :: env) env param_vals

let lookup_env : string -> env -> value =
  fun s env ->
    match List.assoc_opt s env with
    | Some v -> v
    | None -> raise (RTError (Printf.sprintf "Unbound identifier: %s" s))

(* Function Environment *)
type fenv = fundef list
let empty_fenv : fenv = []
let rec lookup_fenv : string -> fenv -> fundef =
  fun s fenv -> 
    match fenv with
    | [] -> raise (RTError (Printf.sprintf "Undefined function: %s" s))
    | (f::fs) -> if fundef_name f = s then f else lookup_fenv s fs

(* Lifting functions on OCaml primitive types to operate on language values *)
let liftIII : (int64 -> int64 -> int64) -> value -> value -> value =
  fun op e1 e2 ->
    match e1, e2 with
    | NumV n1, NumV n2 -> NumV (op n1 n2)
    | _ -> raise (RTError (Printf.sprintf "Expected two integers, but got %s and %s" (string_of_val e1) (string_of_val e2)))

let liftBBB : (bool -> bool -> bool) -> value -> value -> value =
  fun op e1 e2 ->
    match e1, e2 with
    | BoolV b1, BoolV b2 -> BoolV (op b1 b2)
    | _ -> raise (RTError (Printf.sprintf "Expected two booleans, but got %s and %s" (string_of_val e1) (string_of_val e2)))

let liftIIB : (int64 -> int64 -> bool) -> value -> value -> value =
  fun op e1 e2 ->
    match e1, e2 with
    | NumV n1, NumV n2 -> BoolV (op n1 n2)
    | _ -> raise (RTError (Printf.sprintf "Expected two integers, but got %s and %s" (string_of_val e1) (string_of_val e2)))
  
let liftBB : (bool -> bool) -> value -> value =
  fun op e ->
    match e with
    | BoolV b -> BoolV (op b)
    (* REMEMBER MAKE TYPE CHECK HERE *)
    | _ -> failwith "runtime type error"
  

let get_elem : value -> value -> value =
    fun v1 v2 ->
        match v1, v2 with
        | TupleV ts, NumV n -> 
                (try List.nth !ts (Int64.to_int n)
                with
                | Failure msg -> raise (RTError msg)
                | RTError msg -> raise (RTError msg)
                | e -> raise (RTError ("unknown error in get elem:"^ Printexc.to_string e )))
        | _ -> raise (RTError (Printf.sprintf "Expected tuple in first position and integer in second position, but got %s and %s" (string_of_val v1) (string_of_val v2)))

let rec change : 'a list -> int -> int -> 'a -> 'a list =
    fun es index n v -> 
        if index == n 
        then v :: (List.tl es)
        else (List.hd es) :: change (List.tl es) (1 + index) n v

let set_elem : value -> value -> value -> value = 
    fun v1 v2 v3 -> 
        match v1,v2 with
        | TupleV ts, NumV n -> 
                ts := change !ts 0 (Int64.to_int n) v3 ; TupleV ts
        | _ -> raise (RTError (Printf.sprintf "Expected tuple in first position and integer in second position, but got %s and %s" (string_of_val v1) (string_of_val v2)))

(* Sys functions *)
let defs_prelude : fundef list = [
  (*DefSys ("print", [CAny], CAny) ;
  DefSys ("max", [CInt ; CInt], CInt) *)
]


(* check that the value is of the given type, return the value if ok *)
let rec check_type (t : ctype) (v : value) : value =
    match v, t with
    | NumV _, CInt | BoolV _, CBool | _, CAny -> v
    | TupleV vals, CTuple types -> 
            let _ = List.map2 check_type types !vals in
            v
    | NumV _, _ -> raise (RTError (Printf.sprintf "Expected boolean but got %s" (string_of_val v)))
    | BoolV _, _ -> raise (RTError (Printf.sprintf "Expected integer but got %s" (string_of_val v)))
    | TupleV _,_ -> raise (RTError (Printf.sprintf "Expected tuple but got %s" (string_of_val v)))
            


(* provide a dummy (non-C) interpretation of sys functions print and max *)
let interp_sys name vals = 
  match name with
  | "print" -> (match vals with 
                | v :: [] -> Printf.printf "> %s\n" (string_of_val v) ; v
                | _ -> raise (RTError "Function print expected 1 argument"))
  | "max" -> (match vals with
                | NumV n1 :: NumV n2 :: [] -> NumV (if n1 >= n2 then n1 else n2)
                | _ -> raise (RTError "Function max expected 2 integer arguments"))
  | _ -> raise (RTError (Printf.sprintf "Undefined sys function: %s" name))

(* interpreter *)
let rec interp expr env fenv =
  match expr with
  | Id x -> lookup_env x env
  | Num n -> NumV n
  | Bool b -> BoolV b
  | Prim1 (op, e) -> (
    match op with
    | Add1 -> liftIII ( Int64.add ) (interp e env fenv) (NumV 1L)
    | Sub1 -> liftIII ( Int64.sub ) (interp e env fenv) (NumV 1L)
    | Not -> liftBB ( not ) (interp e env fenv)
    | Print -> (interp (Apply ("print", [e])) env fenv)) (* re-route interp of print to the fake sys interface *)
  | Prim2 (op, e1, e2) -> 
    (match op with
    | Add -> liftIII ( Int64.add ) 
    | Sub -> liftIII ( Int64.sub ) 
    | Mul -> liftIII ( Int64.mul ) 
    | Div -> liftIII ( Int64.div ) 
    | And -> liftBBB ( && ) 
    | Lte -> liftIIB ( <= ) 
    | Get -> get_elem) (interp e1 env fenv) (interp e2 env fenv)
  | Let (x, e , b) -> interp b (extend_env [x] [(interp e env fenv)] env) fenv
  | If (e1, e2, e3) -> 
    (match interp e1 env fenv with
    | BoolV b -> interp (if b then e2 else e3) env fenv
    | e -> raise (RTError (Printf.sprintf "Expected boolean, but got %s" (string_of_val e))) )
  | Apply (name, args) -> 
    let vals = List.map (fun e -> interp e env fenv) args in
    (match lookup_fenv name fenv with
    | DefFun (_, params, body) -> 
      interp body (extend_env params vals env) fenv
    | DefSys (_, arg_types, ret_type) ->
      check_type ret_type @@ interp_sys name (List.map2 check_type arg_types vals))
  | Tuple exprs -> 
          TupleV (ref (List.map (fun e -> interp e env fenv) exprs))
  | Set (e,k,v) ->
          let t = (interp e env fenv) in
          let i = (interp k env fenv) in
          set_elem t i (interp v env fenv)

let interp_prog prog env =
  let defs, expr = prog in
  let fenv = defs_prelude @ defs in
  interp expr env fenv
