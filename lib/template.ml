open Syntax

(* aux *)
let rec drop l n =
  if n = 0 then l
  else match l with _ :: t -> drop t (n - 1) | _ -> failwith "drop"

(* aux *)

type addr = int

type ti_stack = addr list

type ti_dump = ti_stack list

let dump_push dump stack = stack :: dump

let dump_pop (h :: dump) = (h, dump)

type primtive = Neg | Add | Sub | Mul | Div

type node =
  | NAp of (addr * addr)
  | NSupercomb of (name * name list * core_expr)
  | NNum of int
  | NInd of addr
  | NPrim of (name * primtive)

module Addr = struct
  type t = addr

  let equal = ( = )

  let hash t = t
end

module Heap_hashtbl = Hashtbl.Make (Addr)

type ti_heap = node Heap_hashtbl.t

module Name = struct
  type t = name

  let compare = String.compare
end

module Global_map = Map.Make (Name)

type ti_globals = addr Global_map.t

type ti_stats = int

type ti_state = ti_stack * ti_dump * ti_heap * ti_globals * ti_stats

let ti_stat_init = 0

(* let ti_stat_inc_steps s = s + 1
 *
 * let ti_stat_get_steps s = s *)

let apply_to_stats f (stack, dump, heap, globals, stats) =
  (stack, dump, heap, globals, f stats)

let halloc heap node =
  let addr = Heap_hashtbl.length heap in
  Heap_hashtbl.add heap addr node ;
  (heap, addr)

let hupdate heap addr node =
  Heap_hashtbl.add heap addr node ;
  heap

let allocate_sc (heap, globals) (name, args, body) =
  let heap', addr = halloc heap (NSupercomb (name, args, body)) in
  let globals' = Global_map.add name addr globals in
  (heap', globals')

let allocate_prim (heap, globals) (name, primtive) =
  let heap', addr = halloc heap (NPrim (name, primtive)) in
  let globals' = Global_map.add name addr globals in
  (heap', globals')

let primtives =
  [("negate", Neg); ("+", Add); ("-", Sub); ("*", Mul); ("/", Div)]

let build_initial_heap (sc_defs : core_program) : ti_heap * ti_globals =
  let heap', globals' =
    List.fold_left allocate_sc
      (Heap_hashtbl.create 100, Global_map.empty)
      sc_defs
  in
  List.fold_left allocate_prim (heap', globals') primtives

let extra_prelude_defs = []

let compile (program : core_program) : ti_state =
  let sc_defs = List.concat [program; prelude_defs; extra_prelude_defs] in
  let heap, globals = build_initial_heap sc_defs in
  let address_of_main = Global_map.find "main" globals in
  let init_stack = [address_of_main] in
  let init_dump = [] in
  (init_stack, init_dump, heap, globals, ti_stat_init)

let is_data_node n = match n with NNum _ -> true | _ -> false

let ti_final state =
  let _stack, _dump, heap, _globals, _stats = state in
  match state with
  | [solo], [], _, _, _ -> is_data_node (Heap_hashtbl.find heap solo)
  | [], _, _, _, _ -> failwith "empty stack"
  | _ -> false

let num_step (_stack, stack' :: dump, heap, globals, stats) _n =
  (stack', dump, heap, globals, stats)

let ap_step (stack, dump, heap, globals, stats) a1 _a2 =
  (a1 :: stack, dump, heap, globals, stats)

let rec instantiate expr heap env =
  match expr with
  | ENum n -> halloc heap (NNum n)
  | EAp (e1, e2) ->
      let heap', addr' = instantiate e1 heap env in
      let heap'', addr'' = instantiate e2 heap' env in
      halloc heap'' (NAp (addr', addr''))
  | EVar v -> (
    match Global_map.find_opt v env with
    | Some addr -> (heap, addr)
    | None -> failwith ("undefined name: " ^ v) )
  | ECase _ -> failwith "ECASE: not impl yet"
  | ELet (isrec, defs, body) -> instantiate_let isrec heap defs body env
  | EConstr _ -> failwith "EConstr: not impl yet"
  | _ -> failwith ""

and instantiate_let isrec heap defs body env =
  match isrec with
  | false ->
      let instantiate_rhs (heap, env) (name, rhs) =
        let heap', addr = instantiate rhs heap env in
        let env' = Global_map.add name addr env in
        (heap', env')
      in
      let heap', env' = List.fold_left instantiate_rhs (heap, env) defs in
      instantiate body heap' env'
  | true -> failwith "not impl letrec yet"

let rec instantiate_update expr upd_addr heap env =
  match expr with
  | ENum n -> hupdate heap upd_addr (NNum n)
  | EAp (e1, e2) ->
      let heap', addr' = instantiate e1 heap env in
      let heap'', addr'' = instantiate e2 heap' env in
      hupdate heap'' upd_addr (NAp (addr', addr''))
  | EVar v -> (
    match Global_map.find_opt v env with
    | Some v_addr -> hupdate heap upd_addr (NInd v_addr)
    | None -> failwith "instantiate_update Evar" )
  | ELet (isrec, defs, body) ->
      instantiate_update_let isrec heap upd_addr defs body env
  | EConstr _ -> failwith "EConstr: not impl yet"
  | ECase _ -> failwith "cant impl Ecase"
  | _ -> failwith ""

and instantiate_update_let isrec heap upd_addr defs body env =
  match isrec with
  | true -> failwith "not impl letrec yet"
  | false ->
      let instantiate_rhs (heap, env) (name, rhs) =
        let heap', addr = instantiate rhs heap env in
        let env' = Global_map.add name addr env in
        (heap', env')
      in
      let heap', env' = List.fold_left instantiate_rhs (heap, env) defs in
      instantiate_update body upd_addr heap' env'

let rec getargs heap stack n r =
  if n = 0 then List.rev r
  else
    let h, t = match stack with h :: t -> (h, t) | _ -> failwith "getargs" in
    let e = Heap_hashtbl.find heap h in
    getargs heap t (n - 1)
      ((match e with NAp (_f, arg) -> arg | _ -> failwith "1") :: r)

let sc_step (stack, dump, heap, globals, stats) _name args body : ti_state =
  let env =
    Global_map.add_seq
      (List.to_seq
         (List.combine args
            (getargs heap (List.tl stack) (List.length args) [])))
      globals
  in
  let stack' = drop stack (List.length args) in
  let heap' = instantiate_update body (List.hd stack') heap env in
  (stack', dump, heap', globals, stats)

let ind_step (_h :: stack, dump, heap, globals, stats) addr =
  (addr :: stack, dump, heap, globals, stats)

let prim_neg (h :: stack, dump, heap, globals, stats) =
  match stack with
  | [h1] -> (
    match Heap_hashtbl.find heap h1 with
    | NAp (_, b) -> (
      match Heap_hashtbl.find heap b with
      | NNum n -> ([h1], dump, hupdate heap h1 (NNum (-n)), globals, stats)
      | _ -> ([b], dump_push dump [h; h1], heap, globals, stats) )
    | _ -> failwith "must NNum node follow NPrim" )
  | _ -> failwith "must contain only 1 node in stack"

let op_prim (prim : primtive) a b =
  match prim with
  | Add -> a + b
  | Sub -> a - b
  | Mul -> a * b
  | Div -> a / b
  | Neg -> failwith "can't be here"

let prim_arith (_h :: stack, dump, heap, globals, stats) op =
  if List.length stack <> 2 then failwith "wrong number of args <> 2"
  else
    let args = getargs heap stack 2 [] in
    let h1, h2 = match args with [h1; h2] -> (h1, h2) | _ -> failwith "" in
    let arg1 = Heap_hashtbl.find heap h1 in
    let arg2 = Heap_hashtbl.find heap h2 in
    match (is_data_node arg1, is_data_node arg2) with
    | false, _ -> ([h1], dump_push dump (drop stack 1), heap, globals, stats)
    | _, false -> ([h2], dump_push dump (drop stack 1), heap, globals, stats)
    | _ ->
        let arg1_v = match arg1 with NNum v -> v | _ -> failwith "" in
        let arg2_v = match arg2 with NNum v -> v | _ -> failwith "" in
        let stack' = drop stack 1 in
        let heap' = hupdate heap (List.hd stack') (NNum (op arg1_v arg2_v)) in
        (stack', dump, heap', globals, stats)

let prim_step (_h :: stack, dump, heap, globals, stats) _name prim =
  let state = (_h :: stack, dump, heap, globals, stats) in
  match prim with
  | Neg -> prim_neg state
  | _ -> prim_arith state (op_prim prim)

let step (state : ti_state) : ti_state =
  let stack, _dump, heap, _globals, _stats = state in
  let hd = Heap_hashtbl.find heap (List.hd stack) in
  match hd with
  | NNum n -> num_step state n
  | NAp (a1, a2) -> ap_step state a1 a2
  | NSupercomb (name, args, body) ->
      apply_to_stats (fun a -> a + 1) (sc_step state name args body)
  | NInd addr -> ind_step state addr
  | NPrim (name, prim) -> prim_step state name prim

let do_admin a = a

(* ===========================  show ===================================== *)
open Pp

let show_fw_addr addr =
  let str = Printf.sprintf "%d" addr in
  let space =
    let str_len = String.length str in
    if str_len <= 4 then String.make (4 - str_len) ' ' else ""
  in
  istr (space ^ str)

let show_addr addr = istr (Printf.sprintf "%d" addr)

let show_node n =
  match n with
  | NAp (a1, a2) -> iconcat [istr "NAp "; show_addr a1; istr " "; show_addr a2]
  | NNum n -> iconcat [istr "NNum "; inum n]
  | NSupercomb (name, _args, _body) -> istr ("NSupercomb " ^ name)
  | NInd addr -> iconcat [istr "NInd "; show_addr addr]
  | NPrim (name, _prim) -> iconcat [istr "NPrim "; istr name]

let show_stack_node heap node =
  match node with
  | NAp (a1, a2) ->
      iconcat
        [ istr "NAp "
        ; show_fw_addr a1
        ; istr " "
        ; show_fw_addr a2
        ; istr " ("
        ; show_node (Heap_hashtbl.find heap a2)
        ; istr ")" ]
  | _ -> show_node node

let show_stack heap stack =
  let show_stack_item addr =
    iconcat
      [ show_fw_addr addr
      ; istr ": "
      ; show_stack_node heap (Heap_hashtbl.find heap addr) ]
  in
  iconcat
    [ istr "stack ["
    ; iindent (iinterleave inewline (List.map show_stack_item stack))
    ; istr "]" ]

let show_state (stack, _dump, heap, _globals, _stats) =
  iconcat [show_stack heap stack; inewline]

let show_results states = ilayn (List.map show_state states)

(* =========================eval======================================= *)
let rec eval state =
  show_state state |> idisplay |> print_string ;
  let get_next_state () = do_admin (step state) in
  let rest_state = if ti_final state then [] else eval (get_next_state ()) in
  state :: rest_state
