open Syntax

let is_digit c = Char.compare c '0' >= 0 && Char.compare c '9' <= 0

let is_alpha c =
  (Char.compare c 'a' >= 0 && Char.compare c 'z' <= 0)
  || (Char.compare c 'A' >= 0 && Char.compare c 'Z' <= 0)

let is_whitespace c =
  Char.equal c ' ' || Char.equal c '\t' || Char.equal c '\n'

let is_newline = Char.equal '\n'

let is_id_char c = is_alpha c || is_digit c || c = '_'

let member_two_char_ops (c1, c2) =
  match (c1, c2) with
  | '<', '=' | '=', '=' | '~', '=' | '>', '=' | '-', '>' -> true
  | _ -> false

let takewhile f cs =
  let rec aux r cs =
    match cs with
    | [] -> List.rev r
    | c :: t -> if f c then aux (c :: r) t else List.rev r
  in
  aux [] cs

let rec dropwhile f cs =
  match cs with [] -> [] | c :: t -> if f c then dropwhile f t else c :: t

let string_to_char_list s = List.init (String.length s) (String.get s)

let char_list_to_string cs =
  let s = Bytes.create (List.length cs) in
  List.iteri (fun i a -> Bytes.set s i a) cs ;
  Bytes.to_string s

type token = int * string

(* row, token *)

let clex (s : string) : token list =
  let cs = string_to_char_list s in
  let rec aux row cs =
    match cs with
    | [] -> []
    | c :: t when is_whitespace c ->
        if is_newline c then aux (row + 1) t else aux row t
    | c :: t when is_digit c ->
        let num_token = c :: takewhile is_digit t
        and rest_cs = dropwhile is_digit t in
        (row, char_list_to_string num_token) :: aux row rest_cs
    | c :: t when is_alpha c ->
        let var_token = c :: takewhile is_id_char t
        and rest_cs = dropwhile is_id_char t in
        (row, char_list_to_string var_token) :: aux row rest_cs
    | '|' :: '|' :: t -> aux row (dropwhile (fun c -> c <> '\n') t)
    | c1 :: c2 :: t when member_two_char_ops (c1, c2) ->
        (row, char_list_to_string [c1; c2]) :: aux row t
    | c :: t -> (row, char_list_to_string [c]) :: aux row t
  in
  aux 0 cs

(* ================================================================================ *)
(* lex above *)
(* parser follows *)
(* ================================================================================ *)
let keywords : string list = ["let"; "letrec"; "in"; "of"; "case"; "Pack"]

type 'a parser = token list -> ('a * token list) list

let plit s : string parser =
 fun tokens ->
  match tokens with (_, tok) :: t when s = tok -> [(s, t)] | _ -> []

let pnum : int parser =
 fun toks ->
  match toks with
  | (_, tok) :: t -> (
    match int_of_string_opt tok with Some i -> [(i, t)] | None -> [] )
  | _ -> []

let psat pred : string parser =
 fun toks ->
  match toks with (_, tok) :: t when pred tok -> [(tok, t)] | _ -> []

let pvar : string parser =
  let is_var s = is_alpha s.[0] && not (List.mem s keywords) in
  psat (fun c -> is_var c)

let palt p1 p2 : 'a parser = fun toks -> p1 toks @ p2 toks

let pthen (combine : 'a -> 'b -> 'c) (p1 : 'a parser) (p2 : 'b parser) :
    'c parser =
 fun toks ->
  List.map
    (fun (v1, toks1) ->
      let l2 = p2 toks1 in
      List.map (fun (v2, toks2) -> (combine v1 v2, toks2)) l2 )
    (p1 toks)
  |> List.concat

let pthen3 (combine : 'a -> 'b -> 'c -> 'd) (p1 : 'a parser) (p2 : 'b parser)
    (p3 : 'c parser) : 'd parser =
 fun toks ->
  List.map
    (fun (v1, toks1) ->
      List.map
        (fun (v2, toks2) ->
          List.map (fun (v3, toks3) -> (combine v1 v2 v3, toks3)) (p3 toks2) )
        (p2 toks1) )
    (p1 toks)
  |> List.concat |> List.concat

let pthen4 (combine : 'a -> 'b -> 'c -> 'd -> 'e) p1 p2 p3 p4 : 'e parser =
 fun toks ->
  List.map
    (fun (v1, toks1) ->
      List.map
        (fun (v2, toks2) ->
          List.map
            (fun (v3, toks3) ->
              List.map
                (fun (v4, toks4) -> (combine v1 v2 v3 v4, toks4))
                (p4 toks3) )
            (p3 toks2) )
        (p2 toks1) )
    (p1 toks)
  |> List.concat |> List.concat |> List.concat

let pempty a toks = [(a, toks)]

let pzero_or_more (p : 'a parser) : 'a list parser =
 fun toks ->
  let rec aux r toks =
    let l = p toks in
    if List.length l > 0 then
      List.concat (List.map (fun (v, toks1) -> aux (v :: r) toks1) l)
    else [(List.rev r, toks)]
  in
  aux [] toks

let pone_or_more (p : 'a parser) : 'a list parser =
  pthen List.cons p (pzero_or_more p)

let papply (p : 'a parser) (f : 'a -> 'b) : 'b parser =
 fun toks -> List.map (fun (v, toks1) -> (f v, toks1)) (p toks)

let pone_or_more_with_sep (p1 : 'a parser) (p2 : 'b parser) : 'a list parser =
 fun toks ->
  let init = p1 toks in
  let rec aux r toks =
    let l = pthen (fun _ a -> a) p2 p1 toks in
    if List.length l > 0 then
      List.map (fun (v, toks1) -> aux (v :: r) toks1) l |> List.concat
    else [(List.rev r, toks)]
  in
  List.map (fun (v, toks_init) -> aux [v] toks_init) init |> List.concat

(* let pexpr = pthen *)
type partial_expr =
  | NoOp
  | FoundOp of (name * core_expr)
  | FoundOp3 of (name * core_expr * partial_expr)

let rec assemble_op e1 pe =
  match pe with
  | NoOp -> e1
  | FoundOp (op, e2) -> EAp (EAp (EVar op, e1), e2)
  | FoundOp3 (op, e2, p) -> assemble_op (EAp (EAp (EVar op, e1), e2)) p

let combine a b = FoundOp (a, b)

let combine3 a b c = FoundOp3 (a, b, c)

let pexprc op next_expr =
  palt (pthen (fun a b -> FoundOp (a, b)) (plit op) next_expr) (pempty NoOp)

let rec pexpr1c a = pexprc "|" pexpr1 a

and pexpr2c a = pexprc "&" pexpr2 a

and pexpr3c a =
  palt
    (pthen
       (fun a b -> FoundOp (a, b))
       (psat (fun op -> List.mem op ["=="; "<="; ">="; "<"; ">"; "~="]))
       pexpr4)
    (pempty NoOp) a

and pexpr4c a =
  palt
    (pthen3 combine3 (plit "-") pexpr5 pexpr4c)
    (palt (pthen3 combine3 (plit "+") pexpr5 pexpr4c) (pempty NoOp))
    a

and pexpr5c a =
  palt
    (pthen3 combine3 (plit "*") pexpr6 pexpr5c)
    (palt (pthen3 combine3 (plit "/") pexpr6 pexpr5c) (pempty NoOp))
    a

and pexpr1 a = pthen assemble_op pexpr2 pexpr1c a

and pexpr2 a = pthen assemble_op pexpr3 pexpr2c a

and pexpr3 a = pthen assemble_op pexpr4 pexpr3c a

and pexpr4 a = pthen assemble_op pexpr5 pexpr4c a

and pexpr5 a = pthen assemble_op pexpr6 pexpr5c a

and pexpr6 a =
  let mk_ap_chain vs =
    match vs with
    | fn :: t -> List.fold_left (fun r e -> EAp (r, e)) fn t
    | [] -> failwith ""
  in
  papply (pone_or_more patomic) mk_ap_chain a

and patomic a =
  palt pconstr
    (palt pbrac_expr
       (palt (papply pvar (fun v -> EVar v)) (papply pnum (fun v -> ENum v))))
    a

and pbrac_expr a =
  let mk_brack _ e _ = e in
  pthen3 mk_brack (plit "(") pexpr (plit ")") a

and pconstr a =
  let pick_constr _ _ constr _ = constr in
  let mk_constr tag _ arity = EConstr (tag, arity) in
  let ptag_arity = pthen3 mk_constr pnum (plit ",") pnum in
  pthen4 pick_constr (plit "Pack") (plit "{") ptag_arity (plit "}") a

and plet a =
  let mk_let keyword defns _ expr = ELet (keyword = "letrec", defns, expr) in
  pthen4 mk_let (palt (plit "let") (plit "letrec")) pdefns (plit "in") pexpr a

and pdefns a = pone_or_more_with_sep pdefn (plit ";") a

and pdefn a =
  let mk_defn v _ e = (v, e) in
  pthen3 mk_defn pvar (plit "=") pexpr a

and pcase a =
  let mk_case _ e _ alts = ECase (e, alts) in
  pthen4 mk_case (plit "case") pexpr (plit "of") palters a

and palters a = pone_or_more_with_sep palter (plit ";") a

and palter a =
  let mk_alt tag vars _ e = (tag, vars, e) in
  pthen4 mk_alt ptag (pzero_or_more pvar) (plit "->") pexpr a

and ptag a =
  let get_tag _ n _ = n in
  pthen3 get_tag (plit "<") pnum (plit ">") a

and plambda a =
  let mk_lam _ vs _ e = ELam (vs, e) in
  pthen4 mk_lam (plit "\\") (pone_or_more pvar) (plit ".") pexpr a

and pexpr a = palt plet (palt pcase (palt plambda pexpr1)) a

let psc =
  let mk_sc var args _ body = (var, args, body) in
  pthen4 mk_sc pvar (pzero_or_more pvar) (plit "=") pexpr

let pprogram : core_program parser = pone_or_more_with_sep psc (plit ";")

let parse toks =
  let rec take_first r =
    match r with
    | (prog, []) :: _ -> prog
    | _ :: t -> take_first t
    | _ -> failwith "syntax error"
  in
  pprogram toks |> take_first
