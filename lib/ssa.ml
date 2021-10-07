open Core_kernel
open Result.Let_syntax
open Syntax
open Expression
open HeapType
module InstanceMap = Map.Make (Instance)

module Log = (val Logs.src_log Logging.ssa_src : Logs.LOG)

type versions = int InstanceMap.t

type ssa_program =
  { command : command;
    header_table : HeaderTable.t;
    input_type : HeapType.t;
    output_type : HeapType.t
  }

type version_binding =
  | NopBind
  | VersionBind of versions

type version_context = version_binding list

let init_versions (header_table : HeaderTable.t) (version : int) =
  HeaderTable.to_list header_table
  |> List.fold ~init:InstanceMap.empty ~f:(fun acc inst ->
         Map.set acc ~key:inst ~data:version)

let increment_version inst versions =
  let v =
    Map.find versions inst
    |> Option.map ~f:(fun v -> v + 1)
    |> Option.value ~default:0
  in
  (v, Map.set ~key:inst ~data:v versions)

let current_version inst versions =
  Map.find versions inst
  |> Option.map ~f:(fun v -> (v, versions))
  |> Option.value ~default:(increment_version inst versions)

let append_version (inst : string) (version : int) =
  Printf.sprintf "%s_%d" inst version

let mk_versioned_inst inst version =
  Syntax.Instance.
    { name = Printf.sprintf "%s_%d" inst.name version; fields = inst.fields }

let rec term_to_ssa (term : Term.t) (versions : versions)
    (ctx : version_context) =
  let open Term in
  match term with
  | Plus (tm1, tm2) ->
    let tm1_ssa, tm1_vers = term_to_ssa tm1 versions ctx in
    let tm2_ssa, tm2_vers = term_to_ssa tm2 tm1_vers ctx in
    (Plus (tm1_ssa, tm2_ssa), tm2_vers)
  | Minus (tm1, tm2) ->
    let tm1_ssa, tm1_vers = term_to_ssa tm1 versions ctx in
    let tm2_ssa, tm2_vers = term_to_ssa tm2 tm1_vers ctx in
    (Minus (tm1_ssa, tm2_ssa), tm2_vers)
  | Concat (tm1, tm2) ->
    let tm1_ssa, tm1_vers = term_to_ssa tm1 versions ctx in
    let tm2_ssa, tm2_vers = term_to_ssa tm2 tm1_vers ctx in
    (Concat (tm1_ssa, tm2_ssa), tm2_vers)
  | Slice (Instance (x, inst), l, r) ->
    let inst_version, versions' =
      match List.nth_exn ctx x with
      | NopBind -> current_version inst versions
      | VersionBind bind ->
        let v, _ = current_version inst bind in
        (v, versions)
    in
    (Slice (Instance (x, mk_versioned_inst inst inst_version), l, r), versions')
  | _ as tm -> (tm, versions)

let rec exp_to_ssa (expr : Expression.t) (versions : versions)
    (ctx : version_context) =
  match expr with
  | True -> (True, versions)
  | False -> (False, versions)
  | IsValid (x, inst) ->
    let inst_version, versions' =
      match List.nth_exn ctx x with
      | NopBind -> current_version inst versions
      | VersionBind bind ->
        let v, _ = current_version inst bind in
        (v, versions)
    in
    (IsValid (x, mk_versioned_inst inst inst_version), versions')
  | TmEq (tm1, tm2) ->
    let tm1_ssa, tm1_v = term_to_ssa tm1 versions ctx in
    let tm2_ssa, tm2_v = term_to_ssa tm2 tm1_v ctx in
    (TmEq (tm1_ssa, tm2_ssa), tm2_v)
  | TmGt (tm1, tm2) ->
    let tm1_ssa, tm1_v = term_to_ssa tm1 versions ctx in
    let tm2_ssa, tm2_v = term_to_ssa tm2 tm1_v ctx in
    (TmGt (tm1_ssa, tm2_ssa), tm2_v)
  | Neg e ->
    let e_ssa, versions' = exp_to_ssa e versions ctx in
    (Neg e_ssa, versions')
  | And (e1, e2) ->
    let e1_ssa, e1_v = exp_to_ssa e1 versions ctx in
    let e2_ssa, e2_v = exp_to_ssa e2 e1_v ctx in
    (And (e1_ssa, e2_ssa), e2_v)
  | Or (e1, e2) ->
    let e1_ssa, e1_v = exp_to_ssa e1 versions ctx in
    let e2_ssa, e2_v = exp_to_ssa e2 e1_v ctx in
    (Or (e1_ssa, e2_ssa), e2_v)
  | Implies (e1, e2) ->
    let e1_ssa, e1_v = exp_to_ssa e1 versions ctx in
    let e2_ssa, e2_v = exp_to_ssa e2 e1_v ctx in
    (Implies (e1_ssa, e2_ssa), e2_v)

let rec heap_type_to_ssa (max_versions : int InstanceMap.t)
    (versions : versions) (ctx : Env.context) (vctx : version_context)
    (header_type : HeapType.t) =
  match header_type with
  | Nothing -> (Nothing, versions)
  | Empty -> (Empty, versions)
  | Top -> (Top, versions)
  | Sigma (x, hty1, hty2) ->
    let hty1', v' = heap_type_to_ssa max_versions versions ctx vctx hty1 in
    let ctx' = Env.add_binding ctx x Env.NameBind in
    let vctx' = NopBind :: vctx in
    let hty2', v'' = heap_type_to_ssa max_versions v' ctx' vctx' hty2 in
    (Sigma (x, hty1', hty2'), v'')
  | Choice (hty1, hty2) ->
    let hty1', v' = heap_type_to_ssa max_versions versions ctx vctx hty1 in
    let hty2', v'' = heap_type_to_ssa max_versions v' ctx vctx hty2 in
    (Choice (hty1', hty2'), v'')
  | Refinement (x, hty, e) ->
    let hty', v' = heap_type_to_ssa max_versions versions ctx vctx hty in
    let vctx' = NopBind :: vctx in
    let e', v'' = exp_to_ssa e v' vctx' in
    (Refinement (x, hty', e'), v'')
  | Substitution (hty1, x, hty2) ->
    let hty2', v' = heap_type_to_ssa max_versions versions ctx vctx hty2 in
    let vctx' = NopBind :: vctx in
    let hty1', v'' = heap_type_to_ssa max_versions v' ctx vctx' hty1 in
    (Substitution (hty1', x, hty2'), v'')

let merge_versions (v1 : versions) (v2 : versions) =
  Map.merge v1 v2 ~f:(fun ~key:_ -> function
    | `Left v -> Some v
    | `Right v -> Some v
    | `Both (v1, v2) -> Some (max v1 v2))

let range_incl start stop =
  List.range ~start:`inclusive ~stop:`inclusive start stop

let match_versions (cmd : command) (v1 : versions) (v2 : versions) =
  let build_command (inst : Instance.t) (versions : int list) (init : command) =
    List.fold versions ~init:(Ok init) ~f:(fun acc v ->
        let%bind acc = acc in
        let vinst = mk_versioned_inst inst v in
        let add_cmd = Add vinst in
        if v = 0 then
          return acc
        else
          let prev_inst = mk_versioned_inst inst (v - 1) in
          let size = Instance.sizeof prev_inst in
          let assign =
            Assign
              (vinst, 0, size, Term.Slice (Instance (0, prev_inst), 0, size))
          in
          return
            (Seq (acc, If (IsValid (0, prev_inst), Seq (add_cmd, assign), Skip))))
  in

  let deviating_versions =
    Map.fold v2 ~init:[] ~f:(fun ~key:inst ~data:inst_version acc ->
        match Map.find v1 inst with
        | None -> (inst, range_incl 0 inst_version) :: acc
        | Some v1_version ->
          if inst_version > v1_version then
            (inst, range_incl (v1_version + 1) inst_version) :: acc
          else
            acc)
  in
  List.fold deviating_versions ~init:(Ok cmd)
    ~f:(fun acc (inst, new_versions) ->
      let%bind acc = acc in
      build_command inst new_versions acc)

let invalidate_higher_versions versions max_versions binder hty =
  let expr =
    Map.fold max_versions ~init:Expression.True
      ~f:(fun ~key:inst ~data:maxv acc ->
        let v = Map.find versions inst |> Option.value ~default:0 in
        List.range ~start:`exclusive ~stop:`inclusive v maxv
        |> List.fold ~init:acc ~f:(fun acc' v' ->
               let vinst = mk_versioned_inst inst v' in
               And (Neg (IsValid (0, vinst)), acc')))
  in
  let binder =
    match hty with
    | Refinement (x, _, _) -> x
    | _ -> binder
  in
  Simplify.fold_refinements (HeapType.Refinement (binder, hty, expr))

let rec command_to_ssa (header_table : HeaderTable.t)
    (max_versions : int InstanceMap.t) (versions : int InstanceMap.t)
    (cmd : command) =
  match cmd with
  | Extract inst ->
    let n, v = increment_version inst versions in
    return (Extract (mk_versioned_inst inst n), v)
  | If (e, c1, c2) ->
    let e_ssa, e_v = exp_to_ssa e versions [ NopBind ] in
    let%bind ssa_c1, versions_c1 =
      command_to_ssa header_table max_versions e_v c1
    in
    let%bind ssa_c2, versions_c2 =
      command_to_ssa header_table max_versions e_v c2
    in
    let%bind ssa_c1' = match_versions ssa_c1 versions_c1 versions_c2 in
    let%map ssa_c2' = match_versions ssa_c2 versions_c2 versions_c1 in
    let versions_merged = merge_versions versions_c1 versions_c2 in
    (If (e_ssa, ssa_c1', ssa_c2'), versions_merged)
  | Assign (inst, left, right, term) ->
    let inst_size = Instance.sizeof inst in
    if not (Instance.slice_matches_field inst left right) then
      Error
        (Printf.sprintf "Invalid slice [%d:%d] on instance '%s'" left right
           inst.name)
    else
      let v, versions' = increment_version inst versions in
      let inst_next_version = mk_versioned_inst inst v in
      let tm_ssa, tm_v = term_to_ssa term versions' [VersionBind versions] in
      let cmd_add =
        Seq
          ( Add inst_next_version,
            Assign (inst_next_version, left, right, tm_ssa) )
      in
      let inst_prev_version = mk_versioned_inst inst (v - 1) in
      (* left > 0, [0:left] *)
      (* size - right > 0, [right:size] *)
      let cmd' =
        if left > 0 then
          Seq
            ( cmd_add,
              Assign
                ( inst_next_version,
                  0,
                  left,
                  Term.Slice (Instance (0, inst_prev_version), 0, left) ) )
        else
          cmd_add
      in
      let cmd' =
        if inst_size - right > 0 then
          Seq
            ( cmd',
              Assign
                ( inst_next_version,
                  right,
                  inst_size,
                  Term.Slice (Instance (0, inst_prev_version), right, inst_size)
                ) )
        else
          cmd'
      in
      return (cmd', tm_v)
  | Remit inst ->
    let v, versions' = current_version inst versions in
    return (Remit (mk_versioned_inst inst v), versions')
  | Seq (c1, c2) ->
    let%bind c1_ssa, c1_v =
      command_to_ssa header_table max_versions versions c1
    in
    let%map c2_ssa, c2_v = command_to_ssa header_table max_versions c1_v c2 in
    (Seq (c1_ssa, c2_ssa), c2_v)
  | Add inst ->
    let n, v = increment_version inst versions in
    let cmd' = Add (mk_versioned_inst inst n) in
    return (cmd', v)
  | Ascription (cmd, x, hty_in, hty_out) ->
    let%bind cmd', versions' =
      command_to_ssa header_table max_versions versions cmd
    in
    let hty_in' =
      heap_type_to_ssa max_versions versions [] [] hty_in
      |> fst
      |> invalidate_higher_versions versions max_versions x
    in
    let hty_out' =
      heap_type_to_ssa max_versions versions' [] [ VersionBind versions ]
        hty_out
      |> fst
      |> invalidate_higher_versions versions' max_versions x
    in
    return (Ascription (cmd', x, hty_in', hty_out'), versions')
  | Reset -> return (Reset, versions)
  | Skip -> return (Skip, versions)

let rec get_max_versions (versions : versions) (cmd : command) =
  match cmd with
  | Add inst
  | Assign (inst, _, _, _)
  | Extract inst ->
    let _, versions' = increment_version inst versions in
    versions'
  | If (_, c1, c2) ->
    let versions_then = get_max_versions versions c1 in
    let versions_else = get_max_versions versions c2 in
    merge_versions versions_then versions_else
  | Seq (c1, c2) ->
    let versions' = get_max_versions versions c1 in
    get_max_versions versions' c2
  | Ascription (c, _, _, _) -> get_max_versions versions c
  | Remit _
  | Reset
  | Skip ->
    versions

let header_table_to_ssa (header_table : HeaderTable.t) (versions : versions) =
  (* Does not add instances that are not used in the program. Do we need them? *)
  Map.fold ~init:String.Map.empty
    ~f:(fun ~key:name ~data:fields htacc ->
      let inst = Instance.{ name; fields } in
      let v, _ = current_version inst versions in
      List.init (v + 1) ~f:(fun n -> (append_version inst.name n, inst.fields))
      |> List.fold ~init:htacc ~f:(fun acc inst ->
             Map.set ~key:(fst inst) ~data:(snd inst) acc))
    header_table

let to_ssa header_table cmd (binder, hty_in) hty_out =
  let init_versions =
    String.Map.fold header_table ~init:InstanceMap.empty
      ~f:(fun ~key:name ~data:fields acc ->
        Map.set ~key:{ name; fields } ~data:0 acc)
  in

  (* let init_versions = Map.map header_table ~f:(fun _ -> 0) in *)
  let max_versions = get_max_versions init_versions cmd in
  let%bind cmd_ssa, inst_versions' =
    command_to_ssa header_table max_versions init_versions cmd
  in
  let cmd_ssa = Simplify.simplify_command cmd_ssa in
  let annot_tyout_ssa, inst_versions'' =
    heap_type_to_ssa max_versions inst_versions' []
      [ VersionBind init_versions ]
      hty_out
  in
  let annot_tyout_ssa = Simplify.fold_refinements annot_tyout_ssa in
  let annot_tyin_ssa, _ =
    heap_type_to_ssa max_versions init_versions [] [] hty_in
  in
  let%map refinement =
    Map.fold inst_versions'' ~init:(Ok Expression.True)
      ~f:(fun ~key:inst ~data:count acc_result ->
        let%map acc = acc_result in
        let added_versions =
          List.range ~start:`exclusive ~stop:`inclusive 0 count
        in
        Expression.And
          ( acc,
            List.fold added_versions ~init:Expression.True ~f:(fun acc n ->
                let vinst = mk_versioned_inst inst n in
                Expression.And (acc, Neg (IsValid (0, vinst)))) ))
    |> Result.map ~f:Simplify.simplify_expr
  in
  let annot_tyin_ssa =
    let binder =
      match annot_tyin_ssa with
      | Refinement (x, _, _) -> x
      | _ -> Env.pick_fresh_name [] binder
    in
    Simplify.fold_refinements
      (HeapType.Refinement (binder, annot_tyin_ssa, refinement))
  in
  let ht_ssa = header_table_to_ssa header_table inst_versions' in
  
  { command = cmd_ssa;
    header_table = ht_ssa;
    input_type = annot_tyin_ssa;
    output_type = annot_tyout_ssa
  }
