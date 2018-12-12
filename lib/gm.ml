open Syntax
open Pp

(* aux *)
let rec drop l n =
  if n = 0 then l
  else match l with _ :: t -> drop t (n - 1) | _ -> failwith "drop"

(* aux *)

type instruction =
  | Unwind
  | Push_global of name
  | Push_int of int
  | Push of int
  | Mkap
  | Slide of int

let instr_equal i1 i2 =
  match (i1, i2) with
  | Unwind, Unwind -> true
  | Push_global a, Push_global b -> a = b
  | Push_int a, Push_int b -> a = b
  | Push a, Push b -> a = b
  | Mkap, Mkap -> true
  | Slide a, Slide b -> a = b
  | _ -> false

type addr = int

type gmCode = instruction list

type gmStack = addr list

module Addr = struct
  type t = addr

  let equal = ( = )

  let hash t = t
end

module Heap_hashtbl = Hashtbl.Make (Addr)

type node = NNum of int | NAp of (addr * addr) | NGlobal of (int * gmCode)

type gmHeap = node Heap_hashtbl.t

module Name = struct
  type t = name

  let compare = String.compare
end

module Global_map = Map.Make (Name)

type gmGlobals = addr Global_map.t

type gmStats = int

type gmState = gmCode * gmStack * gmHeap * gmGlobals * gmStats

let getCode (i, _, _, _, _) = i

let putCode i (_, stack, heap, globals, stats) =
  (i, stack, heap, globals, stats)

let getStack (_, i, _, _, _) = i

let putStack i (code, _, heap, globals, stats) = (code, i, heap, globals, stats)

let halloc heap node =
  let addr = Heap_hashtbl.length heap in
  Heap_hashtbl.add heap addr node ;
  (heap, addr)

let hupdate heap addr node =
  Heap_hashtbl.add heap addr node ;
  heap

let getHeap (_, _, i, _, _) = i

let putHeap i (code, stack, _, globals, stats) =
  (code, stack, i, globals, stats)

let getGlobals (_, _, _, i, _) = i

let putGlobals i (code, stack, heap, _, stats) = (code, stack, heap, i, stats)

let getStats (_, _, _, _, i) = i

let putStats i (code, stack, heap, globals, _) = (code, stack, heap, globals, i)

let push_global f state =
  let globals = getGlobals state in
  let faddr = Global_map.find f globals in
  putStack (faddr :: getStack state) state

let push_int n state =
  let heap = getHeap state in
  let heap', addr = halloc heap (NNum n) in
  putHeap heap' (putStack (addr :: getStack state) state)

let getarg (NAp (_, a2)) = a2

let push n state =
  let stack = getStack state in
  let heap = getHeap state in
  let addr = getarg (Heap_hashtbl.find heap (List.nth stack (n + 1))) in
  putStack (addr :: stack) state

let mkap state =
  let a1, a2, stack =
    match getStack state with
    | a1 :: a2 :: stack -> (a1, a2, stack)
    | _ -> failwith "mkap"
  in
  let heap', a3 = halloc (getHeap state) (NAp (a1, a2)) in
  putHeap heap' (putStack (a3 :: stack) state)

let slide n state =
  let a, stack =
    match getStack state with
    | a :: stack -> (a, stack)
    | _ -> failwith "slide"
  in
  putStack (a :: drop stack n) state

let unwind state =
  let a, stack =
    match getStack state with
    | a :: stack -> (a, stack)
    | _ -> failwith "unwind"
  in
  let heap = getHeap state in
  let newstate node =
    match node with
    | NNum _ -> putStack [] state
    | NAp (a1, _a2) ->
        let code = getCode state in
        putStack (a1 :: a :: stack) state |> putCode (Unwind :: code)
    | NGlobal (n, c) ->
        if List.length stack < n - 1 then
          failwith
            (Printf.sprintf "not enough arg, %d, %d" (List.length stack) n)
        else putCode c state
  in
  let node = Heap_hashtbl.find heap a in
  newstate node

let dispatch instr state =
  match instr with
  | Push_global f -> push_global f state
  | Push_int n -> push_int n state
  | Push n -> push n state
  | Mkap -> mkap state
  | Slide n -> slide n state
  | Unwind -> unwind state

let isFinal state = match getCode state with [] -> true | _ -> false

let step state =
  let i, is =
    match getCode state with i :: is -> (i, is) | _ -> failwith "step"
  in
  dispatch i (putCode is state)

let do_admin s = s

let rec eval state =
  let rest_state =
    if isFinal state then [] else eval (do_admin (step state))
  in
  state :: rest_state

(* compiler follows *)

type gm_env = int Global_map.t

type gm_compiler = core_expr -> gm_env -> gmCode

type gm_compile_sc = name * int * gmCode

let arg_offset (env : gm_env) n = Global_map.map (fun v -> v + n) env

let rec compileC : gm_compiler =
 fun expr env ->
  match expr with
  | EVar v -> (
    match Global_map.find_opt v env with
    | None -> [Push_global v]
    | Some n -> [Push n] )
  | ENum n -> [Push_int n]
  | EAp (e1, e2) ->
      List.append
        (List.append (compileC e2 env) (compileC e1 (arg_offset env 1)))
        [Mkap]
  | _ -> failwith "compileC: not yet"

let compileR expr env =
  let count = Global_map.cardinal env in
  List.append (compileC expr env) [Slide (count + 1); Unwind]

let compileSC ((name, env, body) : core_sc_defn) : gm_compile_sc =
  let env' =
    List.combine env (List.init (List.length env) (fun i -> i))
    |> List.to_seq |> Global_map.of_seq
  in
  (name, List.length env, compileR body env')

let allocGlobal heap (sc : gm_compile_sc) =
  let name, i, code = sc in
  let heap', addr = halloc heap (NGlobal (i, code)) in
  (heap', name, addr)

let buildInitHeap (prog : core_program) : gmHeap * gmGlobals =
  let compiled = List.map (fun def -> compileSC def) prog in
  let initheap = Heap_hashtbl.create 100 in
  let initglobals = Global_map.empty in
  List.fold_left
    (fun (heap, globals) e ->
      let heap', name, addr = allocGlobal heap e in
      let globals' = Global_map.add name addr globals in
      (heap', globals') )
    (initheap, initglobals) compiled

let compile (prog : core_program) : gmState =
  let initialCode = [Push_global "main"; Unwind] in
  let initialStack = [] in
  let initialHeap, initialGlobals =
    buildInitHeap (List.append Syntax.prelude_defs prog)
  in
  let initStat = 0 in
  (initialCode, initialStack, initialHeap, initialGlobals, initStat)

(* =================================== show ============================= *)

let show_instr instr =
  match instr with
  | Unwind -> istr "unwind"
  | Push_global name -> iappend (istr "pushglobal ") (istr name)
  | Push_int i -> iappend (istr "pushint ") (inum i)
  | Push i -> iappend (istr "push ") (inum i)
  | Mkap -> istr "mkap"
  | Slide i -> iappend (istr "slide ") (inum i)

let show_instrs code =
  iconcat
    [ istr "  code: {"
    ; iindent
        (iappend inewline (iinterleave inewline (List.map show_instr code)))
    ; inewline
    ; istr "        }"
    ; inewline ]

let show_sc s (name, addr) =
  match Heap_hashtbl.find (getHeap s) addr with
  | NNum _ | NAp _ -> failwith "show_sc"
  | NGlobal (i, code) ->
      iconcat
        [ istr "code for :"
        ; istr name
        ; inewline
        ; show_instrs code
        ; inewline
        ; inewline ]

let show_addr addr = Printf.sprintf "%d" addr

let show_node state addr n =
  match n with
  | NNum i -> inum i
  | NAp (a1, a2) ->
      iconcat [istr "ap "; istr (show_addr a1); istr " "; istr (show_addr a2)]
  | NGlobal (i, code) ->
      let (Some name) =
        Global_map.fold
          (fun name v r ->
            match r with
            | Some r' -> r
            | None when addr = v -> Some name
            | _ -> None )
          (getGlobals state) None
      in
      iconcat [istr "Global "; istr name]

let show_stack_item state addr =
  let heap = getHeap state in
  iconcat
    [ istr (show_addr addr)
    ; istr ": "
    ; show_node state addr (Heap_hashtbl.find heap addr) ]

let show_stack state =
  iinterleave inewline (List.map (show_stack_item state) (getStack state))

let show_state state =
  iconcat [show_stack state; inewline; show_instrs (getCode state); inewline]

let show_result states =
  let (s :: _) = states in
  idisplay
    (iconcat
       [ istr "supercombinator definitions"
       ; inewline
       ; iinterleave inewline
           (Global_map.fold
              (fun name addr r -> show_sc s (name, addr) :: r)
              (getGlobals s) [])
       ; inewline
       ; inewline
       ; istr "state trans"
       ; inewline
       ; inewline
       ; ilayn (List.map show_state states) ])
