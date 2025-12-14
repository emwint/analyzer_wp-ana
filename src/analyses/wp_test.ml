open GoblintCil
open Analyses

module Spec : Analyses.MCPSpec =
struct
  let name () = "wp_test"

  include Analyses.IdentityUnitContextsSpec


  module LiveVariableSet =  SetDomain.ToppedSet (Basetype.Variables) (struct let topname = "All variables" end)
  module D =  LiveVariableSet (*Set of program variables as domain*)

  let startstate v = D.empty()
  let exitstate v = D.empty()

  let get_local = function
    | Var v, _ -> Some v (* some local variable*)
    | _, _ -> None

  let vars_from_expr (e: exp) : D.t=
    let rec aux acc e =
      match e with
      | Lval (Var v, _)       ->  D.add v acc
      | BinOp (_, e1, e2, _)  ->
        let acc1 = aux acc e1 in
        aux acc1 e2
      | UnOp (_, e1, _)       ->  aux acc e1
      | CastE (_, e1)         ->   aux acc e1
      | SizeOfE e1            -> aux acc e1
      | AlignOfE e1           -> aux acc e1
      |Question (e1, e2, e3, _) -> 
        let acc1 = aux acc e1 in
        let acc2 = aux acc1 e2 in
        aux acc2 e3
      | _ -> acc 
    in
    aux (D.empty()) e

  let assign man (lval:lval) (rval:exp) =
    let () =
      Logs.debug "=== man (analysis manager) info ===";
      Logs.debug "  lval: %a" CilType.Lval.pretty lval;
      Logs.debug "  rval: %a" CilType.Exp.pretty rval;
      Logs.debug "  local state: %a" D.pretty man.local;
      Logs.debug "  local is_top: %b" (D.is_top man.local);
      Logs.debug "  local is_bot: %b" (D.is_bot man.local);
    in

    let v = get_local lval in

    match v with
    | None -> Logs.debug "!!! possibly unsound !!!"; D.top ()
    | Some v -> 
      let l = (D.diff man.local (D.singleton v)) in
      if D.mem v man.local then D.join l (vars_from_expr rval)
      else l

  let branch man (exp:exp) (tv:bool) =
    D.join man.local (vars_from_expr exp)

  let body man (f:fundec) =
    man.local

  let return man (exp:exp option) (f:fundec) =
    match exp with
    | None -> man.local
    | Some e -> D.join man.local (vars_from_expr e)

  let enter man (lval: lval option) (f:fundec) (args:exp list) =
    [man.local, man.local]

  let combine_env man (lval:lval option) fexp (f:fundec) (args:exp list) fc au (f_ask: Queries.ask) =
    au
end


let _ =
  MCP.register_analysis (module Spec : MCPSpec)