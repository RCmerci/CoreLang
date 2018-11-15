open Syntax

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

let getHeap (_, _, i, _, _) = i

let putHeap i (code, stack, _, globals, stats) =
  (code, stack, i, globals, stats)

let getGlobals (_, _, _, i, _) = i

let putGlobals i (code, stack, heap, _, stats) = (code, stack, heap, i, stats)

let getStats (_, _, _, _, i) = i

let putStats i (code, stack, heap, globals, _) = (code, stack, heap, globals, i)
