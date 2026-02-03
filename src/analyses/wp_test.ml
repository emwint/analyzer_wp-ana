open GoblintCil
open Analyses


module Spec : Analyses.MCPSpec =
struct
  let name () = "wp_test"

  include Analyses.IdentitySpec

  (*## context ##*)
  (*Idea: make context type passsable, so add parameter.*)
  module C = Printable.Unit

  let context man _ _ = ()
  let startcontext () = ()

  (*## end of context ##*)


  module LiveVariableSet =  SetDomain.ToppedSet (Basetype.Variables) (struct let topname = "All variables" end)
  module D =  LiveVariableSet (*Set of program variables as domain*)

  let startstate v = D.empty()
  let exitstate v = D.empty()

  let vars_from_lval (l: lval) = 
    match l with
    | Var v, NoOffset when isIntegralType v.vtype && not (v.vglob || v.vaddrof) -> Some v (* local integer variable whose address is never taken *)
    | _, _ -> None (*do not know what to do here yet*)

  let vars_from_expr (e: exp) : D.t=
    let rec aux acc e =
      match e with
      | Lval (Var v, _)       ->  D.add v acc
      | BinOp (_, e1, e2, _)  ->
        let acc1 = aux acc e1 in
        aux acc1 e2
      | UnOp (_, e1, _)       ->  aux acc e1
      | SizeOfE e1            -> aux acc e1
      | AlignOfE e1           -> aux acc e1
      | Question (e1, e2, e3, _) -> 
        let acc1 = aux acc e1 in
        let acc2 = aux acc1 e2 in
        aux acc2 e3
      | CastE (_, e1)         ->   aux acc e1
      | AddrOf (l1)          ->   (match vars_from_lval l1 with
          | None -> acc
          | Some v -> D.add v acc)
      | _ -> acc 
    in
    aux (D.empty()) e


  let assign man (lval:lval) (rval:exp) =
    (* let () =
       Logs.debug "=== man (analysis manager) info ===";
       Logs.debug "  lval: %a" CilType.Lval.pretty lval;
       Logs.debug "  rval: %a" Cil Type.Exp.pretty rval;
       Logs.debug "  local state: %a" D.pretty man.local;
       Logs.debug "  local is_top: %b" (D.is_top man.local);
       Logs.debug "  local is_bot: %b" (D.is_bot man.local);
       in *)

    let v = vars_from_lval lval in

    match v with
    | None -> D.join man.local (vars_from_expr rval) (*if I do not know what the value is assigned to, then all RHS-Variables might be relevant*)
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

  (* TODO *)
  let enter man (lval: lval option) (f:fundec) (args:exp list) =
    (* Logs.debug "=== enter function %s with args %s ===" f.svar.vname 
       (String.concat ", " (List.map (CilType.Exp.show) args)); *)

    let vars =
      match lval with 
      | None -> man.local
      | Some lv -> man.local (*i have to check for every arg ... no wait... I do not care about the args here, i care about those at the combine!!!!*)

    in

    [man.local, vars]

  (* TODO *)
  let combine_env man (lval:lval option) fexp (f:fundec) (args:exp list) fc au (f_ask: Queries.ask) =
    (* Logs.debug "=== combine_env of function %s ===" f.svar.vname;
       let args_pretty = String.concat ", " (List.map CilType.Exp.show args) in
       Logs.debug "    args: %s" args_pretty;

       let sformals_pretty = String.concat ", " (List.map (fun v -> v.vname) f.sformals) in
       Logs.debug "    sformals: %s" sformals_pretty; *)

    (*map relevant sformals in man.local to the corresponding variables contained in the argument*)
    let arg_formal_pairs = List.combine args f.sformals in
    let relevant_arg_vars = 
      List.fold_left (fun acc (arg_exp, formal_var) ->
          if D.mem formal_var au then
            D.join acc (vars_from_expr arg_exp)
          else
            acc
        ) (D.empty()) arg_formal_pairs
    in

    (*join relevant*)
    D.join man.local relevant_arg_vars 

  let combine_assign man (lval:lval option) fexp (f:fundec) (args:exp list) fc au (f_ask: Queries.ask) =
    (* Logs.debug "=== combine_assign of function %s ===" f.svar.vname;
       (*how do I know which args are important? i.e. how do I match the local name of the variable in the function with the passed parameters (if there are several)*)
       let args_pretty = String.concat ", " (List.map CilType.Exp.show args) in
       Logs.debug "    args: %s" args_pretty; *)

    let simple_assign lval exp acc =
      let v = vars_from_lval lval in

      match v with
      | None -> acc  (*D.join acc (vars_from_expr exp) if I do not know what the value is assigned to, then all RHS-Variables might be relevant *)
      | Some v -> 
        let l = (D.diff acc (D.singleton v)) in
        (* if D.mem v acc then D.join l (vars_from_expr exp)
           else l *)
        l
    in

    match lval with 
    | Some lval -> List.fold_right (fun exp acc -> simple_assign lval exp acc) args man.local
    | _ -> man.local



  (** A transfer function which handles the return statement, i.e.,
      "return exp" or "return" in the passed function (fundec) *)
  let return man (exp: exp option) (f:fundec) : D.t =
    let return_val_is_important = (not (D.is_bot man.local)) || (String.equal f.svar.vname "main") in (*this does not take globals int account, only checks for "temp"*)

    match exp with
    | None -> D.empty()
    | Some e -> if return_val_is_important
      then D.join (D.empty()) (vars_from_expr e)
      else D.empty();

end
