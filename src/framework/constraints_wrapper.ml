(** Construction of a {{!Goblint_constraint} constraint system} from an {{!Analyses.Spec} analysis specification} and {{!MyCFG.CfgBackward} CFGs}.
    Transformatons of analysis specifications as functors. *)

open Batteries
open GoblintCil
open MyCFG
open Analyses
open Goblint_constraint.ConstrSys
open GobConfig


type Goblint_backtrace.mark += TfLocation of location

let () = Goblint_backtrace.register_mark_printer (function
    | TfLocation loc ->
      Some ("transfer function at " ^ CilType.Location.show loc)
    | _ -> None (* for other marks *)
  )


module type Increment =
sig
  val increment: increment_data option
end


(** The main point of this file---generating a [DemandGlobConstrSys] from a [Spec]. *)
module Spec_wrapper (S_forwards:Spec) (S_backwards:Spec) (Cfg:CfgBidir)
  : sig
    include DemandGlobConstrSys with module LVar = VarF (S_forwards.C)
                                 and module GVar = GVarF (S_forwards.V)
                                 and module D = S_forwards.D
                                 and module G = GVarG (S_forwards.G) (S_forwards.C)
  end
=
struct
  type lv = MyCFG.node * S_forwards.C.t
  (* type gv = varinfo *)
  type ld = S_forwards.D.t
  (* type gd = S_forwards.G.t *)
  module LVar = VarF (S_forwards.C)
  module GVar = GVarF (S_forwards.V) (* * GVarF (S_backward.V) ## I probably need another functor*)
  module D = S_forwards.D
  module G = GVarG (S_forwards.G) (S_forwards.C)

  (* Two global invariants:
     1. S_forwards.V -> S_forwards.G  --  used for Spec
     2. fundec -> set of S_forwards.C  --  used for IterSysVars Node *)

  let system (v,c) =
    let wrap (v,c) = 
      match v with
      | FunctionEntry _ ->
        let tf getl sidel demandl getg sideg =
          let tf' eu = tf (v,c) eu getl sidel demandl getg sideg in
          let xs = List.map tf' (Cfg.next v) in
          List.fold_left S_forwards.D.join (S_forwards.D.bot ()) xs
        in
        Some tf
      | Function _ ->
        None
      | _ ->
        let tf getl sidel demandl getg sideg =
          let tf' eu = tf (v,c) eu getl sidel demandl getg sideg in
          let xs = List.map tf' (Cfg.next v) in
          List.fold_left S_forwards.D.join (S_forwards.D.bot ()) xs
        in

        Some tf

    in

    (* Logs.debug "# Creating transfer function for %s" (Node.show v);
       Logs.debug "  Number of nexts: %d" (List.length (Cfg.next v)) ;
       Logs.debug "  Number of prevs: %d" (List.length (Cfg.prev v)) ; *)
    wrap (v,c)


  (* what does this do? *)
  let iter_vars getl getg vq fl fg =
    failwith "iter_vars not implemented in WP"


  let sys_change getl getg =
    failwith "sys_change not implemented in WP"

  (*What does this do?*)
  let postmortem = function
    | FunctionEntry fd, c -> [(Function fd, c)]
    | _ -> []
end
