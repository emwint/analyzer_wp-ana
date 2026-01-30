open Batteries
open GoblintCil
open MyCFG
open Analyses
open Goblint_constraint.ConstrSys
open GobConfig

module type Increment =
sig
  val increment: increment_data option
end



module BidirFromSpec (S_forw:Spec) (S_backw:Spec with type C.t = S_forw.C.t ) (Cfg:CfgBidir) (I:Increment)
  : sig
    module LVar : Goblint_constraint.ConstrSys.VarType with type t = [ `L_forw of VarF(S_forw.C).t | `L_backw of VarF(S_forw.C).t ]
    module GVar : Goblint_constraint.ConstrSys.VarType with type t = [ `G_forw of GVarF(S_forw.V).t | `G_backw of GVarF(S_backw.V).t ]
    include DemandGlobConstrSys with module LVar := LVar
                                 and module GVar := GVar
                                 and module D = Lattice.Lift2(S_forw.D)(S_backw.D)
                                 and module G = GVarG (Lattice.Lift2(S_forw.G)(S_backw.G)) (S_forw.C)
  end 
= 
struct
  (* type lv = [ `lv_forw of MyCFG.node * S_forw.C.t | `lv_back of MyCFG.node * S_forw.C.t] *)
  (* type ld = Lattice.Lift2(S_forw.D)(S_backw.D).t *)

  module LV = VarF (S_forw.C)
  module LVar =
  struct
    type t = [ `L_forw of LV.t | `L_backw of LV.t ] [@@deriving eq, ord, hash]

    let relift = function
      | `L_forw x -> `L_forw (LV.relift x)
      | `L_backw x -> `L_backw (LV.relift x)

    let pretty_trace () = function
      | `L_forw a -> GoblintCil.Pretty.dprintf "L_forw:%a" LV.pretty_trace a
      | `L_backw a -> GoblintCil.Pretty.dprintf "L_backw:%a" LV.pretty_trace a

    let printXml f = function
      | `L_forw a -> LV.printXml f a
      | `L_backw a -> LV.printXml f a

    let var_id = function
      | `L_forw a -> LV.var_id a
      | `L_backw a -> LV.var_id a

    let node = function
      | `L_forw a -> LV.node a
      | `L_backw a -> LV.node a

    let is_write_only = function
      | `L_forw a -> LV.is_write_only a
      | `L_backw a -> LV.is_write_only a
  end

  module D = Lattice.Lift2(S_forw.D)(S_backw.D)
  module GV_forw = GVarF (S_forw.V)
  module GV_backw = GVarF (S_backw.V)
  module GVar =
  struct
    type t = [ `G_forw of GV_forw.t | `G_backw of GV_backw.t ] [@@deriving eq, ord, hash]

    let relift = function
      | `G_forw x -> `G_forw (GV_forw.relift x)
      | `G_backw x -> `G_backw (GV_backw.relift x)

    let pretty_trace () = function
      | `G_forw a -> GoblintCil.Pretty.dprintf "G_forw:%a" GV_forw.pretty_trace a
      | `G_backw a -> GoblintCil.Pretty.dprintf "G_backw:%a" GV_backw.pretty_trace a

    let printXml f = function
      | `G_forw a -> GV_forw.printXml f a
      | `G_backw a -> GV_backw.printXml f a

    let var_id = function
      | `G_forw a -> GV_forw.var_id a
      | `G_backw a -> GV_backw.var_id a

    let node = function
      | `G_forw a -> GV_forw.node a
      | `G_backw a -> GV_backw.node a

    let is_write_only = function
      | `G_forw a -> GV_forw.is_write_only a
      | `G_backw a -> GV_backw.is_write_only a
  end

  module G_forw = GVarG (S_forw.G) (S_forw.C)
  module G_backw = GVarG (S_backw.G) (S_forw.C)
  module G = GVarG (Lattice.Lift2(S_forw.G)(S_backw.G)) (S_forw.C)

  module Forward = Constraints_wp.FromSpec (S_forw) (Cfg)
  module CfgBackward = struct let prev = Cfg.prev end
  module Backward = Constraints.FromSpec (S_backw) (CfgBackward) (I)

  let backw_lv_of_forw ((n,c): LV.t) : Backward.LVar.t = (n, Obj.magic c)
  let forw_lv_of_backw ((n,c): Backward.LVar.t) : LV.t = (n, Obj.magic c)

  let to_l_backw (v:LVar.t) = 
    match v with
    | `L_forw (n, l) -> `L_backw (n, l)
    | `L_backw (n, l) -> `L_backw (n, l)


  let cset_to_forw c =
    G.CSet.fold (fun x acc -> Forward.G.CSet.add x acc) c (Forward.G.CSet.empty ())

  let cset_of_forw c =
    Forward.G.CSet.fold (fun x acc -> G.CSet.add x acc) c (G.CSet.empty ())

  let cset_to_backw c =
    G.CSet.fold (fun x acc -> G_backw.CSet.add (Obj.magic x) acc) c (G_backw.CSet.empty ())

  let cset_of_backw c =
    G_backw.CSet.fold (fun x acc -> G.CSet.add (Obj.magic x) acc) c (G.CSet.empty ())

  let to_forw_d (d: D.t) : S_forw.D.t =
    match d with
    | `Lifted1 d -> d
    | `Bot -> S_forw.D.bot ()
    | `Top -> S_forw.D.top ()
    | `Lifted2 _ -> failwith "bidirConstrains: forward local got backward value"

  let to_backw_d (d: D.t) : S_backw.D.t =
    match d with
    | `Lifted2 d -> d
    | `Bot -> S_backw.D.bot ()
    | `Top -> S_backw.D.top ()
    | `Lifted1 _ -> failwith "bidirConstrains: backward local got forward value"

  let of_forw_d (d: S_forw.D.t) : D.t = `Lifted1 d
  let of_backw_d (d: S_backw.D.t) : D.t = `Lifted2 d

  let to_forw_g (g: G.t) : Forward.G.t =
    match g with
    | `Lifted1 (`Lifted1 g) -> `Lifted1 g
    | `Lifted1 `Bot -> `Bot
    | `Lifted1 `Top -> `Top
    | `Lifted1 (`Lifted2 _) -> failwith "bidirConstrains: forward global got backward value"
    | `Lifted2 c -> `Lifted2 (cset_to_forw c)
    | `Bot -> `Bot
    | `Top -> `Top

  let to_backw_g (g: G.t) : G_backw.t =
    match g with
    | `Lifted1 (`Lifted2 g) -> `Lifted1 g
    | `Lifted1 `Bot -> `Bot
    | `Lifted1 `Top -> `Top
    | `Lifted1 (`Lifted1 _) -> failwith "bidirConstrains: backward global got forward value"
    | `Lifted2 c -> `Lifted2 (cset_to_backw c)
    | `Bot -> `Bot
    | `Top -> `Top

  let of_forw_g (g: Forward.G.t) : G.t =
    match g with
    | `Lifted1 g -> `Lifted1 (`Lifted1 g)
    | `Lifted2 c -> `Lifted2 (cset_of_forw c)
    | `Bot -> `Bot
    | `Top -> `Top

  let of_backw_g (g: G_backw.t) : G.t =
    match g with
    | `Lifted1 g -> `Lifted1 (`Lifted2 g)
    | `Lifted2 c -> `Lifted2 (cset_of_backw c)
    | `Bot -> `Bot
    | `Top -> `Top

  let sync_backw man =
    match man.prev_node, Cfg.next man.prev_node with
    | _, _ :: _ :: _ -> (* Join in CFG. *)
      S_backw.sync man `Join
    | FunctionEntry f, _ -> (* Function entry, also needs sync because partial contexts joined by solver, see 00-sanity/35-join-contexts. *)
      S_backw.sync man (`JoinCall f)
    | _, _ -> S_backw.sync man `Normal

  let side_context_backw sideg f c =
    if !AnalysisState.postsolving then 
      sideg (GV_backw.contexts f) (G_backw.create_contexts (G_backw.CSet.singleton c))

  let common_man_backw var edge prev_node pval getl sidel demandl getg sideg : (S_backw.D.t, S_backw.G.t, S_backw.C.t, S_backw.V.t) man * S_backw.D.t list ref * (lval option * varinfo * exp list * S_backw.D.t * bool) list ref =
    let r = ref [] in
    let spawns = ref [] in
    (* now watch this ... *)
    let rec man =
      { ask     = (fun (type a) (q: a Queries.t) -> S_backw.query man q)
      ; emit    = (fun _ -> failwith "emit outside MCP")
      ; node    = fst var
      ; prev_node = prev_node
      ; control_context = snd var |> Obj.obj
      ; context = snd var |> Obj.obj
      ; edge    = edge
      ; local   = pval
      ; global  = (fun g -> G_backw.spec (getg (GV_backw.spec g)))
      ; spawn   = spawn
      ; split   = (fun (d:S_backw.D.t) es -> assert (List.is_empty es); r := d::!r)
      ; sideg   = (fun g d -> sideg (GV_backw.spec g) (G_backw.create_spec d))
      }
    and spawn ?(multiple=false) lval f args =
      (* TODO: adjust man node/edge? *)
      (* TODO: don't repeat for all paths that spawn same *)
      let ds = S_backw.threadenter ~multiple man lval f args in
      List.iter (fun d ->
          spawns := (lval, f, args, d, multiple) :: !spawns;
          match Cilfacade.find_varinfo_fundec f with
          | fd ->
            let c = S_backw.context man fd d in
            sidel (FunctionEntry fd, c) d;
            demandl (Function fd, c)
          | exception Not_found ->
            (* unknown function *)
            M.error ~category:Imprecise ~tags:[Category Unsound] "Created a thread from unknown function %s" f.vname;
            (* actual implementation (e.g. invalidation) is done by threadenter *)
            (* must still sync for side effects, e.g., old sync-based none privatization soundness in 02-base/51-spawn-special *)
            let rec sync_man =
              { man with
                ask = (fun (type a) (q: a Queries.t) -> S_backw.query sync_man q);
                local = d;
                prev_node = Function dummyFunDec;
              }
            in
            (* TODO: more accurate man? *)
            ignore (sync_backw sync_man)
        ) ds
    in
    (* ... nice, right! *)
    let pval = sync_backw man in
    { man with local = pval }, r, spawns

  let rec bigsqcup_backw = function
    | []    -> S_backw.D.bot ()
    | [x]   -> x
    | x::xs -> S_backw.D.join x (bigsqcup_backw xs)

  let thread_spawns_backws man d spawns =
    if List.is_empty spawns then
      d
    else
      let rec man' =
        { man with
          ask = (fun (type a) (q: a Queries.t) -> S_backw.query man' q)
        ; local = d
        }
      in
      (* TODO: don't forget path dependencies *)
      let one_spawn (lval, f, args, fd, multiple) =
        let rec fman =
          { man with
            ask = (fun (type a) (q: a Queries.t) -> S_backw.query fman q)
          ; local = fd
          }
        in
        S_backw.threadspawn man' ~multiple lval f args fman
      in
      bigsqcup_backw (List.map one_spawn spawns)

  let common_join_backw man d splits spawns =
    thread_spawns_backws man (bigsqcup_backw (d :: splits)) spawns

  let common_joins_backw man ds splits spawns = common_join_backw man (bigsqcup_backw ds) splits spawns

  let tf_assign_backw var edge prev_node lv e getl sidel demandl getg sideg d =
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let d = S_backw.assign man lv e in (* Force transfer function to be evaluated before dereferencing in common_join argument. *)
    common_join_backw man d !r !spawns

  let tf_vdecl_backw var edge prev_node v getl sidel demandl getg sideg d =
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let d = S_backw.vdecl man v in (* Force transfer function to be evaluated before dereferencing in common_join argument. *)
    common_join_backw man d !r !spawns

  let normal_return_backw r fd man sideg =
    let spawning_return = S_backw.return man r fd in
    let nval = S_backw.sync { man with local = spawning_return } `Return in
    nval

  let toplevel_kernel_return_backw r fd man sideg =
    let st = if fd.svar.vname = MyCFG.dummy_func.svar.vname then man.local else S_backw.return man r fd in
    let spawning_return = S_backw.return {man with local = st} None MyCFG.dummy_func in
    let nval = S_backw.sync { man with local = spawning_return } `Return in
    nval

  let tf_ret_backw var edge prev_node ret fd getl sidel demandl getg sideg d =
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let d = (* Force transfer function to be evaluated before dereferencing in common_join argument. *)
      if (CilType.Fundec.equal fd MyCFG.dummy_func ||
          List.mem fd.svar.vname (get_string_list "mainfun")) &&
         get_bool "kernel"
      then toplevel_kernel_return_backw ret fd man sideg
      else normal_return_backw ret fd man sideg
    in
    common_join_backw man d !r !spawns

  let tf_entry_backw var edge prev_node fd getl sidel demandl getg sideg d =
    (* Side effect function context here instead of at sidel to FunctionEntry,
       because otherwise context for main functions (entrystates) will be missing or pruned during postsolving. *)
    let c: unit -> S_forw.C.t = snd var |> Obj.obj in
    side_context_backw sideg fd (c ());
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let d = S_backw.body man fd in (* Force transfer function to be evaluated before dereferencing in common_join argument. *)
    common_join_backw man d !r !spawns

  let tf_test_backw var edge prev_node e tv getl sidel demandl getg sideg d =
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let d = S_backw.branch man e tv in (* Force transfer function to be evaluated before dereferencing in common_join argument. *)
    common_join_backw man d !r !spawns

  (*TODO: THIS HAS TO BE BACKWARDS*) (*forward context not implemented yet*)
  let tf_normal_call_backw man lv e (f:fundec) args getl sidel demandl getg sideg =
    let combine (cd, fc, fd) =
      if M.tracing then M.traceli "combine" "local: %a" S_backw.D.pretty cd;
      if M.tracing then M.trace "combine" "function: %a" S_backw.D.pretty fd;

      Logs.debug "combine: local: %a" S_backw.D.pretty cd;
      Logs.debug "combine: function: %a" S_backw.D.pretty fd;

      let rec cd_man =
        { man with
          ask = (fun (type a) (q: a Queries.t) -> S_backw.query cd_man q);
          local = cd;
        }
      in
      let fd_man =
        (* Inner scope to prevent unsynced fd_man from being used. *)
        (* Extra sync in case function has multiple returns.
           Each `Return sync is done before joining, so joined value may be unsound.
           Since sync is normally done before tf (in common_man), simulate it here for fd. *)
        (* TODO: don't do this extra sync here *)
        let rec sync_man =
          { man with
            ask = (fun (type a) (q: a Queries.t) -> S_backw.query sync_man q);
            local = fd;
            (*prev_node = Function f*)
            prev_node = FunctionEntry f;
          }
        in
        (* TODO: more accurate man? *)
        let synced = sync_backw sync_man in
        let rec fd_man =
          { sync_man with
            ask = (fun (type a) (q: a Queries.t) -> S_backw.query fd_man q);
            local = synced;
          }
        in
        fd_man
      in
      let r = List.fold_left (fun acc fd1 ->
          let rec fd1_man =
            { fd_man with
              ask = (fun (type a) (q: a Queries.t) -> S_backw.query fd1_man q);
              local = fd1;
            }
          in
          let combine_enved = S_backw.combine_env cd_man lv e f args fc fd1_man.local (Analyses.ask_of_man fd1_man) in
          let rec combine_assign_man =
            { cd_man with
              ask = (fun (type a) (q: a Queries.t) -> S_backw.query combine_assign_man q);
              local = combine_enved;
            }
          in
          S_backw.D.join acc (S_backw.combine_assign combine_assign_man lv e f args fc fd1_man.local (Analyses.ask_of_man fd1_man))
        ) (S_backw.D.bot ()) (S_backw.paths_as_set fd_man)
      in
      if M.tracing then M.traceu "combine" "combined local: %a" S_backw.D.pretty r;
      Logs.debug "combined local: %a" S_backw.D.pretty r;
      r
    in
    let paths = 
      Logs.debug "manager info at call to %a" Node.pretty man.node;
      S_backw.enter man lv f args in
    (* Wollen eig vorwärts-kontext benutzen *)
    let paths = List.map (fun (c,v) -> (c, S_backw.context man f v, v)) paths in

    (* List.iter (fun (c,fc,v) -> if not (S_backw.D.is_bot v) then sidel (FunctionEntry f, fc) v) paths; *)
    List.iter (fun (c,fc,v) -> if not (S_backw.D.is_bot v) then sidel (Function f, fc) v) paths;
    (* let paths = List.map (fun (c,fc,v) -> (c, fc, if S_backw.D.is_bot v then v else getl (Function f, fc))) paths; *)
    (* *)
    let paths = List.map (fun (c,fc,v) -> (c, fc, if S_backw.D.is_bot v then v else getl (FunctionEntry f, fc))) paths in

    (* Don't filter bot paths, otherwise LongjmpLifter is not called. *)
    (* let paths = List.filter (fun (c,fc,v) -> not (D.is_bot v)) paths in *)
    let paths = List.map (Tuple3.map2 Option.some) paths in
    if M.tracing then M.traceli "combine" "combining";
    Logs.debug  "combining";
    let paths = List.map combine paths in
    let r = List.fold_left S_backw.D.join (S_backw.D.bot ()) paths in
    if M.tracing then M.traceu "combine" "combined: %a" S_backw.D.pretty r;
    Logs.debug "combined: %a" S_backw.D.pretty r;
    r

  (*TODO: HERE AS WELL*)
  let rec tf_proc_backw var edge prev_node lv e args getl sidel demandl getg sideg d =
    let tf_special_call man f =
      let once once_control init_routine =
        (* Executes leave event for new local state d if it is not bottom *)
        let leave_once d =
          if not (S_backw.D.is_bot d) then
            let rec man' =
              { man with
                ask = (fun (type a) (q: a Queries.t) -> S_backw.query man' q);
                local = d;
              }
            in
            S_backw.event man' (Events.LeaveOnce { once_control }) man'
          else
            S_backw.D.bot ()
        in
        let first_call =
          let d' = S_backw.event man (Events.EnterOnce { once_control;  ran = false }) man in
          tf_proc_backw var edge prev_node None init_routine [] getl sidel demandl getg sideg d'
        in
        let later_call = S_backw.event man (Events.EnterOnce { once_control;  ran = true }) man in
        S_backw.D.join (leave_once first_call) (leave_once later_call)
      in
      let is_once = LibraryFunctions.find ~nowarn:true f in
      (* If the prototpye for a library function is wrong, this will throw an exception. Such exceptions are usually unrelated to pthread_once, it is just that the call to `is_once.special` raises here *)
      match is_once.special args with
      | Once { once_control; init_routine } -> once once_control init_routine
      | _  -> S_backw.special man lv f args
    in
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let functions =
      match e with
      | Lval (Var v, NoOffset) ->
        (* Handle statically known function call directly.
           Allows deactivating base. *)
        [v]
      | _ ->
        (* Depends on base for query. *)
        let ad = man.ask (Queries.EvalFunvar e) in
        Queries.AD.to_var_may ad (* TODO: don't convert, handle UnknownPtr below *) 
        (*PROBLEM: Pointer. Brauche Ergebnisse der anderen Analysen*)
    in
    let one_function f =
      match Cil.unrollType f.vtype with
      | TFun (_, params, var_arg, _)  ->
        let arg_length = List.length args in
        let p_length = Option.map_default List.length 0 params in
        (* Check whether number of arguments fits. *)
        (* If params is None, the function or its parameters are not declared, so we still analyze the unknown function call. *)
        if Option.is_none params || p_length = arg_length || (var_arg && arg_length >= p_length) then
          let d =
            (match Cilfacade.find_varinfo_fundec f with
             | fd when LibraryFunctions.use_special f.vname ->
               M.info ~category:Analyzer "Using special for defined function %s" f.vname;
               tf_special_call man f
             | fd ->
               tf_normal_call_backw man lv e fd args getl sidel demandl getg sideg
             | exception Not_found ->
               tf_special_call man f)
          in
          Some d
        else begin
          let geq = if var_arg then ">=" else "" in
          M.warn ~category:Unsound ~tags:[Category Call; CWE 685] "Potential call to function %a with wrong number of arguments (expected: %s%d, actual: %d). This call will be ignored." CilType.Varinfo.pretty f geq p_length arg_length;
          None
        end
      | _ ->
        M.warn ~category:Call "Something that is not a function (%a) is called." CilType.Varinfo.pretty f;
        None
    in
    let funs = List.filter_map one_function functions in
    if [] = funs && not (S_backw.D.is_bot man.local) then begin
      M.msg_final Warning ~category:Unsound ~tags:[Category Call] "No suitable function to call";
      M.warn ~category:Unsound ~tags:[Category Call] "No suitable function to be called at call site. Continuing with state before call.";
      d (* because LevelSliceLifter *)
    end else
      common_joins_backw man funs !r !spawns

  let tf_asm_backw var edge prev_node getl sidel demandl getg sideg d =
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let d = S_backw.asm man in (* Force transfer function to be evaluated before dereferencing in common_join argument. *)
    common_join_backw man d !r !spawns

  let tf_skip_backw var edge prev_node getl sidel demandl getg sideg d =
    let man, r, spawns = common_man_backw var edge prev_node d getl sidel demandl getg sideg in
    let d = S_backw.skip man in (* Force transfer function to be evaluated before dereferencing in common_join argument. *)
    common_join_backw man d !r !spawns

  let tf_backw var getl sidel demandl getg sideg prev_node edge d =
    begin match edge with
      | Assign (lv,rv) -> tf_assign_backw var edge prev_node lv rv
      | VDecl (v)      -> tf_vdecl_backw var edge prev_node v
      | Proc (r,f,ars) -> tf_proc_backw var edge prev_node r f ars
      | Entry f        -> tf_entry_backw var edge prev_node f
      | Ret (r,fd)     -> tf_ret_backw var edge prev_node r fd
      | Test (p,b)     -> tf_test_backw var edge prev_node p b
      | ASM (_, _, _)  -> tf_asm_backw var edge prev_node (* TODO: use ASM fields for something? *)
      | Skip           -> tf_skip_backw var edge prev_node
    end getl sidel demandl getg sideg d

  let tf_backw var getl sidel demandl getg sideg prev_node (_,edge) d (f,t) =
    (* let old_loc  = !Goblint_tracing.current_loc in
       let old_loc2 = !Goblint_tracing.next_loc in
       Goblint_tracing.current_loc := f;
       Goblint_tracing.next_loc := t;
       Goblint_backtrace.protect ~mark:(fun () -> TfLocation f) ~finally:(fun () ->
        Goblint_tracing.current_loc := old_loc;
        Goblint_tracing.next_loc := old_loc2
       ) (fun () ->
        let d       = tf_backw var getl sidel demandl getg sideg prev_node edge d in
        d
       ) *)
    tf_backw var getl sidel demandl getg sideg prev_node edge d

  let tf_backw (v,c) (edges, u) getl sidel demandl getg sideg =
    let pval = getl (u,c) in
    let _, locs = List.fold_right (fun (f,e) (t,xs) -> f, (f,t)::xs) edges (Node.location v,[]) in
    List.fold_left2 (|>) pval (List.map (tf_backw (v,Obj.repr (fun () -> c)) getl sidel demandl getg sideg u) edges) locs

  let tf_backw (v,c) (e,u) getl sidel demandl getg sideg =
    let old_node = !current_node in
    let old_fd = Option.map Node.find_fundec old_node |? Cil.dummyFunDec in
    let new_fd = Node.find_fundec v in
    if not (CilType.Fundec.equal old_fd new_fd) then
      Timing.Program.enter new_fd.svar.vname;
    let old_context = !M.current_context in
    current_node := Some u;
    M.current_context := Some (Obj.magic c); (* magic is fine because Spec is top-level Control Spec *)
    Fun.protect ~finally:(fun () ->
        current_node := old_node;
        M.current_context := old_context;
        if not (CilType.Fundec.equal old_fd new_fd) then
          Timing.Program.exit new_fd.svar.vname
      ) (fun () ->
        let d       = tf_backw (v,c) (e,u) getl sidel demandl getg sideg in
        d
      )

  let system_backw (v,c) =
    match v with
    | FunctionEntry _ ->
      let tf_backw getl sidel demandl getg sideg =
        let tf' eu = tf_backw (v,c) eu getl sidel demandl getg sideg in
        let xs = List.map tf' (Cfg.next v) in
        List.fold_left S_backw.D.join (S_backw.D.bot ()) xs
      in
      Some tf_backw
    | Function _ ->
      None
    | _ ->
      let tf_backw getl sidel demandl getg sideg =
        let tf' eu = tf_backw (v,c) eu getl sidel demandl getg sideg in
        let xs = List.map tf' (Cfg.next v) in
        List.fold_left S_backw.D.join (S_backw.D.bot ()) xs
      in

      Some tf_backw


  let system var =
    match var with
    | `L_forw v -> None
    (* Forward.system v
       |> Option.map (fun tf getl sidel demandl getg sideg ->
        let getl' v = getl (`L_forw v) |> to_forw_d in
        let sidel' v d = sidel (`L_forw v) (of_forw_d d) in
        let demandl' v = demandl (`L_forw v) in
        let getg' v = getg (`G_forw v) |> to_forw_g in
        let sideg' v d = sideg (`G_forw v) (of_forw_g d) in
        tf getl' sidel' demandl' getg' sideg' |> of_forw_d
       ) *)
    | `L_backw v ->
      system_backw v
      |> Option.map (fun tf getl sidel demandl getg sideg ->
          let getl' v = getl (`L_backw (forw_lv_of_backw v)) |> to_backw_d in
          let sidel' v d = sidel (`L_backw (forw_lv_of_backw v)) (of_backw_d d) in
          let demandl' v = demandl (`L_backw (forw_lv_of_backw v)) in
          let getg' v = getg (`G_backw v) |> to_backw_g in
          let sideg' v d = sideg (`G_backw v) (of_backw_g d) in
          tf getl' sidel' demandl' getg' sideg' |> of_backw_d
        )

  let iter_vars getl getg vq fl fg =
    failwith "damn"

  let sys_change getl getg =
    failwith "damn"

  let postmortem = function
    | `L_forw v -> List.map (fun v -> `L_forw v) (Forward.postmortem v)
    | `L_backw v -> List.map (fun v -> `L_backw (v)) (Backward.postmortem (v))
end