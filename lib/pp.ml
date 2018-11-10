open Syntax

type iseq =
  | INil
  | IStr of string
  | IAppend of (iseq * iseq)
  | IIndent of iseq
  | INewline

let iappend s1 s2 = IAppend (s1, s2)

let istr s = IStr s

let inum n = IStr (Printf.sprintf "%d" n)

let ifwnum width n = istr (String.make width ' ' ^ Printf.sprintf "%d" n)

let inewline = INewline

let iindent seq = IIndent seq

let rec iconcat seqs =
  match seqs with [] -> INil | s :: t -> iappend s (iconcat t)

let ilayn seqs =
  List.mapi
    (fun i seq -> iconcat [ifwnum 4 i; istr ") "; iindent seq; inewline])
    seqs
  |> iconcat

let rec iinterleave seq seqs =
  match seqs with
  | [] -> INil
  | [s] -> s
  | s :: t -> iappend (iappend s seq) (iinterleave seq t)

let rec flatten col (seqs : (iseq * int) list) : string =
  match seqs with
  | [] -> ""
  | (INil, _) :: t -> flatten col t
  | (IStr s, _) :: t -> s ^ flatten (col + String.length s) t
  | (IAppend (s1, s2), indent) :: t ->
      flatten col ((s1, indent) :: (s2, indent) :: t)
  | (IIndent s, _) :: t -> flatten col ((s, col) :: t)
  | (INewline, indent) :: t -> "\n" ^ String.make indent ' ' ^ flatten indent t

let idisplay s = flatten 0 [(s, 0)]

let ppr_args args = iinterleave (istr " ") (List.map istr args)

let rec ppr_expr (expr : core_expr) : iseq =
  match expr with
  | EVar v -> istr v
  | ENum n -> inum n
  | EAp (EAp (EVar "+", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " + "; ppr_aexpr e2]
  | EAp (EAp (EVar "-", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " - "; ppr_aexpr e2]
  | EAp (EAp (EVar "*", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " * "; ppr_aexpr e2]
  | EAp (EAp (EVar "/", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " / "; ppr_aexpr e2]
  | EAp (EAp (EVar "<", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " < "; ppr_aexpr e2]
  | EAp (EAp (EVar "<=", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " <= "; ppr_aexpr e2]
  | EAp (EAp (EVar "==", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " == "; ppr_aexpr e2]
  | EAp (EAp (EVar "~=", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " ~= "; ppr_aexpr e2]
  | EAp (EAp (EVar ">=", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " >= "; ppr_aexpr e2]
  | EAp (EAp (EVar ">", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " > "; ppr_aexpr e2]
  | EAp (EAp (EVar "&", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " & "; ppr_aexpr e2]
  | EAp (EAp (EVar "|", e1), e2) ->
      iconcat [ppr_aexpr e1; istr " | "; ppr_aexpr e2]
  | EAp (e1, e2) -> iappend (iappend (ppr_aexpr e1) (istr " ")) (ppr_aexpr e2)
  | ELet (isrec, defns, expr) ->
      let keyword = if isrec then "letrec" else "let" in
      iconcat
        [ istr keyword
        ; inewline
        ; istr "  "
        ; iindent (ppr_defns defns)
        ; inewline
        ; istr "in "
        ; ppr_expr expr ]
  | ECase (e, alts) ->
      let join = iconcat [istr ";"; inewline] in
      iconcat
        [ istr "case "
        ; ppr_expr e
        ; istr " of"
        ; inewline
        ; istr "  "
        ; iindent (iinterleave join (List.map ppr_alt alts)) ]
  | ELam (args, body) ->
      iconcat
        [ istr "(\\"
        ; ppr_args args
        ; istr ". "
        ; iindent (ppr_expr body)
        ; istr ")" ]
  | EConstr (tag, arity) ->
      iconcat [istr "Pack{"; inum tag; istr ", "; inum arity; istr "}"]

and ppr_aexpr expr : iseq =
  if is_atomic_expr expr then ppr_expr expr
  else iconcat [istr "("; ppr_expr expr; istr ")"]

and ppr_defns (defns : (name * core_expr) list) : iseq =
  iinterleave (iconcat [istr ";"; inewline]) (List.map ppr_defn defns)

and ppr_defn (name, expr) : iseq =
  iconcat [istr name; istr " = "; iindent (ppr_expr expr)]

and ppr_alt (tag, args, rhs) =
  iconcat
    [ istr "<"
    ; inum tag
    ; istr ">"
    ; ppr_args args
    ; istr " -> "
    ; iindent (ppr_expr rhs) ]

let ppr_sc (name, args, expr) =
  iconcat
    [istr name; istr " "; ppr_args args; istr " = "; iindent (ppr_expr expr)]

let ppr_prog prog =
  iinterleave (iappend (istr ";") inewline) (List.map ppr_sc prog)

let pprint (prog : core_program) = idisplay (ppr_prog prog)

(* ================================================================ *)
