open Syntax

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
  let stack = getStack state in
  let newstate node =
    match node with
    | NNum n -> putStack [] state
    | NAp (a1, a2) -> putStack (a1 :: stack) state
    | NGlobal (n, c) -> failwith ""
  in
  failwith ""

let dispatch instr state =
  match instr with
  | Push_global f -> push_global f state
  | Push_int n -> push_int n state
  | Push n -> push n state
  | Mkap -> mkap state
  | Slide n -> slide n state
  | Unwind -> unwind state
