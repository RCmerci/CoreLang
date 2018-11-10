type addr

type ti_stack

type ti_dump

type node =
  | NAp of (addr * addr)
  | NSupercomb of (string * string list * Syntax.core_expr)
  | NNum of addr

type ti_heap

type ti_globals

type ti_stats

type ti_state = ti_stack * ti_dump * ti_heap * ti_globals * ti_stats

val compile : Syntax.core_program -> ti_state

val eval : ti_state -> ti_state list
