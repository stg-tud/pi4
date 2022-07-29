open Core
open Z3
open Syntax
open Result
open Let_syntax

module Log = (val Logs.src_log Logging.prover_src : Logs.LOG)

module ProfileLog = (val Logs.src_log Logging.prover_profile_src : Logs.LOG)

let prover = ref (Error (`ProverError "Prover not initialized"))

let get r =
  match !r with
  | Ok x -> x
  | Error _ -> failwith "Get error"

let make_prover loc = prover := Ok (Smtlib.make_solver loc)

let unsat result =
  let open Smtlib in
  match result with
  | Sat ->
    Log.debug (fun m -> m "Prover returned SAT");
    Ok false
  | Unsat ->
    Log.debug (fun m -> m "Prover returned UNSAT");
    Ok true
  | Unknown -> failwith "Prover returned UNKNOWN."

let default_tactic = Smtlib.UFBV
  (* Smtlib.Then [ SolveEQs; UFBV ] *)

let check_unsat_and_reset (tactic : Smtlib.tactic) =
  let open Smtlib in
  let res = check_sat_using tactic (get prover) in
  reset (get prover);
  unsat res

let check_sat_and_reset (tactic : Smtlib.tactic) =
  let open Smtlib in
  let res = check_sat_using tactic (get prover) in
  reset (get prover);
  match res with
  | Sat ->
    Log.debug (fun m -> m "Prover returned SAT");
    Ok true
  | Unsat ->
    Log.debug (fun m -> m "Prover returned UNSAT");
    Ok false
  | Unknown -> failwith "Prover returned UNKNOWN."

let declare_constants consts =
  List.iter
    ~f:(fun (ident, sort) -> Smtlib.declare_const (get prover) ident sort)
    consts

let print_assert pp term =
  let open Fmt in
  pf pp "@[<v 2>(assert@ %a)@]" Pretty.pp_smtlib_term term

let pp_declare_const pp consts =
  let open Fmt in
  pf pp "(declare-const %a %a)" Pretty.pp_ident (fst consts) Pretty.pp_sort
    (snd consts)

let print_consts pp consts =
  let open Fmt in
  pf pp "@[<v 0>%a@]" (list pp_declare_const) consts

let heur_checks s t =
  let open Syntax.HeapType in
  Stdlib.(s = t)
  ||
  match s with
  | Refinement (_, ss, _) -> Stdlib.(ss = t)
  | _ -> false

module type S = sig
  val check_subtype :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    ( bool,
      [> `EncodingError of string | `VariableLookupError of string ] )
    result

  val check_subtype_with_tactic :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    Smtlib.tactic ->
    ( bool,
      [> `EncodingError of string | `VariableLookupError of string ] )
    result

  val has_model_with_tactic :
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    Z3.Smtlib.tactic ->
    ( bool,
      [> `EncodingError of string | `VariableLookupError of string ] )
    result
end

module Make (Enc : Encoding.S) : S = struct
  let check_subtype_with_tactic (s_hty : HeapType.t) (t_hty : HeapType.t)
      (ctx : Env.context) (header_table : Syntax.HeaderTable.t)
      (tactic : Smtlib.tactic) =
    let s_hty = Simplify.fold_refinements s_hty in
    let t_hty = Simplify.fold_refinements t_hty in
    let ctx =
      List.map ctx ~f:(fun (x, binding) ->
          match binding with
          | Env.NameBind -> (x, binding)
          | Env.VarBind hty -> (x, Env.VarBind (Simplify.fold_refinements hty)))
    in
    if heur_checks s_hty t_hty then
      Ok true
    else
      let pick_unique_name = Utils.(memoize_string_count apply) in
      let freshen_context ctx =
        List.map ctx ~f:(function
          | x, Env.NameBind -> (pick_unique_name x, Env.NameBind)
          | x, Env.VarBind hty ->
            let x' = pick_unique_name x in
            let hty' = Encoding.freshen_binders hty pick_unique_name in
            (x', Env.VarBind hty'))
      in
      let svar = pick_unique_name "s" in
      let tvar = pick_unique_name "t" in
      let annot_s = Encoding.freshen_binders s_hty pick_unique_name in
      let annot_ctx = freshen_context ctx in
      let annot_t = Encoding.freshen_binders t_hty pick_unique_name in

      Log.debug (fun m ->
          m
            "@[<v>Encoding subtype relation@ %a@ <:@ %a@ to SMT using context@ %a @]"
            (Pretty.pp_header_type annot_ctx)
            annot_s
            (Pretty.pp_header_type annot_ctx)
            annot_t Pretty.pp_context annot_ctx);

      let consts_s = Enc.smt_consts annot_s svar header_table in
      let consts_t = Enc.smt_consts annot_t tvar header_table in
      let free_consts =
        List.fold annot_ctx ~init:[] ~f:(fun acc (x, binding) ->
            match binding with
            | Env.NameBind -> acc
            | Env.VarBind hty ->
              Enc.smt_consts hty x header_table |> List.append acc)
      in

      let%bind ctx_s =
        List.foldi annot_ctx ~init:(return Encoding.true_)
          ~f:(fun idx acc_result (x, binding) ->
            match binding with
            | Env.NameBind -> acc_result
            | Env.VarBind hty ->
              let%bind acc = acc_result in
              let encoding_ctx =
                if Types.contains_free_vars hty then
                  let _, ctx' = List.split_n annot_ctx (idx + 1) in
                  ctx'
                else
                  []
              in
              let%map term =
                Enc.heap_type_to_smt header_table encoding_ctx x hty
              in
              Smtlib.and_ acc term)
      in

      let%bind smt_s =
        Enc.heap_type_to_smt header_table annot_ctx svar annot_s
      in
      let%bind smt_t =
        Enc.heap_type_to_smt header_table annot_ctx tvar annot_t
      in
      let smt_t =
        Smtlib.(
          forall_ consts_t
            (implies smt_t (not_ (Enc.equal svar tvar header_table))))
      in
      let smt_consts = Encoding.id_dedup consts_s @ free_consts in
      let smt_terms = [ ctx_s; smt_s; smt_t ] in

      let assert__ = Smtlib.assert_ (get prover) in

      Log.debug (fun m ->
          m "@[<v>%a@;<2 0>%a@ (@[<v 2>check-sat-using@ %a@])@ @]@."
            print_consts smt_consts (Fmt.list print_assert) smt_terms
            Pretty.pp_tactic tactic);

      declare_constants smt_consts;
      List.iter smt_terms ~f:(fun term -> assert__ term);
      Smtlib.(
        apply (get prover) (Then [ Simplify; SolveEQs ]));
      let time = Time_ns.now () in
      let result = check_unsat_and_reset Smtlib.BV in
      let time_diff = Time_ns.abs_diff (Time_ns.now ()) time in
      ProfileLog.debug (fun m ->
          m "Subtype check performed in %f ms" (Time_ns.Span.to_ms time_diff));
      result

  let check_subtype s_hty t_hty ctx header_table =
    check_subtype_with_tactic s_hty t_hty ctx header_table default_tactic

  let has_model_with_tactic (hty : HeapType.t) (ctx : Env.context)
      (header_table : HeaderTable.t) (tactic : Smtlib.tactic) =
    let pick_unique_name = Utils.(memoize_string_count apply) in
    let hty = Simplify.fold_refinements hty in
    let ctx =
      List.map ctx ~f:(fun (x, binding) ->
          match binding with
          | Env.NameBind -> (x, binding)
          | Env.VarBind hty -> (x, Env.VarBind (Simplify.fold_refinements hty)))
    in
    let freshen_context ctx =
      List.map ctx ~f:(function
        | x, Env.NameBind -> (pick_unique_name x, Env.NameBind)
        | x, Env.VarBind hty ->
          let x' = pick_unique_name x in
          let hty' = Encoding.freshen_binders hty pick_unique_name in
          (x', Env.VarBind hty'))
    in
    let svar = pick_unique_name "s" in
    let annot_s = Encoding.freshen_binders hty pick_unique_name in
    let annot_ctx = freshen_context ctx in

    Log.debug (fun m ->
        m "@[<v>Encoding header type@ %a@ to SMT using context@ %a @]"
          (Pretty.pp_header_type annot_ctx)
          annot_s Pretty.pp_context annot_ctx);

    let consts_s = Enc.smt_consts annot_s svar header_table in
    let free_consts =
      List.fold annot_ctx ~init:[] ~f:(fun acc (x, binding) ->
          match binding with
          | Env.NameBind -> acc
          | Env.VarBind hty ->
            Enc.smt_consts hty x header_table |> List.append acc)
    in
    let%bind ctx_s =
      List.foldi annot_ctx ~init:(return Encoding.true_)
        ~f:(fun idx acc_result (x, binding) ->
          match binding with
          | Env.NameBind -> acc_result
          | Env.VarBind hty ->
            let%bind acc = acc_result in
            let encoding_ctx =
              if Types.contains_free_vars hty then
                let _, ctx' = List.split_n annot_ctx (idx + 1) in
                ctx'
              else
                []
            in
            let%map term =
              Enc.heap_type_to_smt header_table encoding_ctx x hty
            in
            Smtlib.and_ acc term)
    in
    let%bind smt_s = Enc.heap_type_to_smt header_table annot_ctx svar annot_s in
    let smt_consts = Encoding.id_dedup consts_s @ free_consts in
    let smt_terms = [ ctx_s; smt_s ] in

    let assert__ = Smtlib.assert_ (get prover) in

    Log.debug (fun m ->
        m "@[<v>%a@;<2 0>%a@ (@[<v 2>check-sat-using@ %a@])@ @]@." print_consts
          smt_consts (Fmt.list print_assert) smt_terms Pretty.pp_tactic tactic);

    declare_constants smt_consts;
    List.iter smt_terms ~f:(fun term -> assert__ term);
    check_sat_and_reset tactic
end
