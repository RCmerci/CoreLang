type is_rec = bool

type 'a expr =
  | EVar of 'a
  | ENum of int
  | EConstr of (int * int)
  | EAp of ('a expr * 'a expr)
  (* isrec, defnitions, body *)
  | ELet of (is_rec * ('a * 'a expr) list * 'a expr)
  | ECase of ('a expr * 'a alter list)
  | ELam of ('a list * 'a expr)

(** case, vars, expr *)
and 'a alter = int * 'a list * 'a expr

type name = string

type core_expr = name expr

type core_alt = name alter

let recursive = true

let non_recursive = false

let binders_of a = List.map (fun (name, _) -> name) a

let rhss_of a = List.map (fun (_, rhs) -> rhs) a

let is_atomic_expr e = match e with EVar _ | ENum _ -> true | _ -> false

type 'a sc_defn = name * 'a list * 'a expr

type 'a program = 'a sc_defn list

type core_program = name program

type core_sc_defn = name sc_defn

let prelude_defs : core_program =
  [ ("I", ["x"], EVar "x")
  ; ("K", ["x"; "y"], EVar "x")
  ; ("K1", ["x"; "y"], EVar "y")
  ; ( "S"
    , ["f"; "g"; "x"]
    , EAp (EAp (EVar "f", EVar "x"), EAp (EVar "g", EVar "x")) )
  ; ("compose", ["f"; "g"; "x"], EAp (EVar "f", EAp (EVar "g", EVar "x")))
  ; ("twice", ["f"], EAp (EAp (EVar "compose", EVar "f"), EVar "f")) ]

(* s k k 3 *)
