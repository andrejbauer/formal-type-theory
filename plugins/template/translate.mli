open Names
open Globnames
open Context


exception MissingGlobal of global_reference


type context

type translator = global_reference Refmap.t

(* TODO *)
