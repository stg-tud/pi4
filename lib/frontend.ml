open Core
open Result.Let_syntax

module Log = (val Logs.src_log Logging.frontend_src : Logs.LOG)

module type Comp = sig
  type t

  val sexp_of_t : t -> Sexp.t

  val t_of_sexp : Sexp.t -> t

  val compare : t -> t -> int
end

module rec CfgNode : sig
  type t =
    { name : string;
      statements : Syntax.command list;
      successors : EdgeSet.t
    }
  [@@deriving compare, sexp]

  include Comp with type t := t
end = struct
  module T = struct
    type t =
      { name : string;
        statements : Syntax.command list;
        successors : EdgeSet.t
      }
    [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

and EdgeType : sig
  type t =
    | Default
    | Match of Syntax.Instance.t * string * Bigint.t
  [@@deriving compare, sexp]

  include Comp with type t := t
end = struct
  module T = struct
    type t =
      | Default
      | Match of Syntax.Instance.t * string * Bigint.t
    [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

and Edge : sig
  type t =
    { node : CfgNode.t;
      typ : EdgeType.t
    }
  [@@deriving compare, sexp]

  include Comp with type t := t
end = struct
  module T = struct
    type t =
      { node : CfgNode.t;
        typ : EdgeType.t
      }
    [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

and EdgeSet : sig
  include Set.S with type Elt.t := Edge.t
end =
  Set.Make (Edge)

let bigint_to_int bint =
  Bigint.to_int bint |> Result.of_option ~error:"Can't convert Bigint to int."

let bigint_to_bv (n : Bigint.t) (size : int) =
  let%bind int_value = bigint_to_int n in
  let bv_str = Utils.bin_of_int int_value in
  let size_diff = size - String.length bv_str in
  if size_diff < 0 then
    Error
      (Printf.sprintf "Can't fit value '%s' into a bitvector of size %d."
         (Bigint.to_string n) size)
  else
    return (Syntax.bv_s (String.init size_diff ~f:(fun _ -> '0') ^ bv_str))

let param_name (param : string) (params : Petr4.Types.Parameter.t list) =
  List.find_map params ~f:(fun (_, { variable; _ }) ->
      Some (return (snd variable)))
  |> Option.value
       ~default:(Error (Printf.sprintf "No param with name '%s'" param))

let field_size_from_type (hdr_type : Petr4.Types.Type.t) =
  match snd hdr_type with
  | BitType expr -> (
    match snd expr with
    | Petr4.Types.Expression.Int (_, n) -> return n.value
    | _ -> Error "Not implemented (Frontend.field_size_from_type - Not an Int)")
  | _ -> Error "Not implemented (Frontend.field_size_from_type - not a BitType)"

let expr_to_instance (_ : string) (header_table : Syntax.HeaderTable.t)
    (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | Name (BareName (_, inst_name))
  | ExpressionMember { expr = _, Name (BareName (_, _)); name = _, inst_name }
    ->
    Syntax.HeaderTable.lookup_instance inst_name header_table
  | _ as e ->
    Error
      (Printf.sprintf "Not a member expression (Frontend.expr_to_instance): %s"
         (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_pre_t e)))

let rec expr_to_term (header_table : Syntax.HeaderTable.t) (size : int)
    (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | Int (_, { value; _ }) -> bigint_to_bv value size
  | ExpressionMember
      { expr = _, ExpressionMember { name = _, instance_name; _ };
        name = _, member_name
      } ->
    Syntax.(
      let%bind inst = HeaderTable.lookup_instance instance_name header_table in
      Term.field_to_slice inst member_name 0)
  | Cast { typ = _, BitType (_, Int (_, { value; _ })); expr } -> (
    let%bind cast_size = bigint_to_int value in
    match snd expr with
    | ExpressionMember
        { expr = _, ExpressionMember { name = _, instance_name; _ };
          name = _, field_name
        } ->
      Syntax.(
        let%bind inst =
          HeaderTable.lookup_instance instance_name header_table
        in
        let%map field = Instance.get_field inst field_name in
        if field.typ < cast_size then
          let diff = cast_size - field.typ in
          Term.Concat (bv_s (String.make diff '0'), Term.instance_slice 0 inst)
        else
          Term.Slice (Sliceable.Instance (0, inst), 0, cast_size))
    | _ -> Error "Not implemented (Frontend.expr_to_term - Cast)")
  | BinaryOp { op = _, Petr4.Types.Op.Minus; args = e1, e2 } ->
    let%bind tm1 = expr_to_term header_table size e1 in
    let%map tm2 = expr_to_term header_table size e2 in
    Syntax.Term.Minus (tm1, tm2)
  | _ as e ->
    Log.debug (fun m ->
        m "Expr: %s"
          (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_pre_t e)));
    Error "Not implemented (Frontend.expr_to_term)"

let is_header_field_access (name : string) (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | ExpressionMember
      { expr =
          _, ExpressionMember { expr = _, Name (BareName (_, member_name)); _ };
        _
      } ->
    String.(member_name = name)
  | _ -> false

let sizeof (header_table : Syntax.HeaderTable.t)
    (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | ExpressionMember
      { expr = _, ExpressionMember { name = _, instance_name; _ };
        name = _, member_name
      } ->
    Syntax.(
      let%bind inst = HeaderTable.lookup_instance instance_name header_table in
      let%map field = Instance.get_field inst member_name in
      field.typ)
  | _ -> Error "sizeof not implemented for expression."

let rec expr_to_expr (headers_param : string)
    (header_table : Syntax.HeaderTable.t) (expr : Petr4.Types.Expression.t) =
  match snd expr with
  | True -> return Syntax.Expression.True
  | False -> return Syntax.Expression.False
  | Int _ -> Error "Not implemented (Frontend.expr_to_expr - Int)"
  | String _ -> Error "Not implemented (Frontend.expr_to_expr - String)"
  | Name _ -> Error "Not implemented (Frontend.expr_to_expr - Name)"
  | ArrayAccess _ ->
    Error "Not implemented (Frontend.expr_to_expr - ArrayAccess)"
  | BitStringAccess _ ->
    Error "Not implemented (Frontend.expr_to_expr - BitStringAccess)"
  | List _ -> Error "Not implemented (Frontend.expr_to_expr - List)"
  | Record _ -> Error "Not implemented (Frontend.expr_to_expr - Record)"
  | UnaryOp { op = _, Not; arg = e } ->
    let%map e' = expr_to_expr headers_param header_table e in
    Syntax.Expression.Neg e'
  | UnaryOp _ -> Error "Not implemented (Frontend.expr_to_expr - UnaryOp)"
  | BinaryOp { op = _, Eq; args = e1, e2 } ->
    (* print_endline (Sexplib.Sexp.to_string_hum
       (Petr4.Types.Expression.sexp_of_t e1)); print_endline (string_of_bool
       (is_header_field_access "hdr" e1)); *)
    let%bind size =
      if is_header_field_access "hdr" e1 then
        sizeof header_table e1
      else
        return 0
    in
    let%bind t1 = expr_to_term header_table 0 e1 in
    let%map t2 = expr_to_term header_table size e2 in
    Syntax.Expression.TmEq (t1, t2)
    (* print_endline (Sexplib.Sexp.to_string_hum
       (Petr4.Types.Expression.sexp_of_t e2)); *)
    (* Error "Not implemented eq(Frontend.expr_to_expr - BinaryOp)" *)
  | BinaryOp _ -> Error "Not implemented (Frontend.expr_to_expr - BinaryOp)"
  | Cast _ -> Error "Not implemented (Frontend.expr_to_expr - Cast)"
  | TypeMember _ -> Error "Not implemented (Frontend.expr_to_expr - TypeMember)"
  | ErrorMember _ ->
    Error "Not implemented (Frontend.expr_to_expr - ErrorMember)"
  | ExpressionMember { expr; name = _, member_name } -> (
    match member_name with
    | "isValid" ->
      let%map inst = expr_to_instance headers_param header_table expr in
      Syntax.Expression.IsValid (0, inst)
    | _ -> Error "Not implemented (Frontend.expr_to_expr - ExpressionMember)")
  | Ternary _ -> Error "Not implemented (Frontend.expr_to_expr - Ternary)"
  | FunctionCall { func = e; type_args = []; args = [] } ->
    expr_to_expr headers_param header_table e
  | FunctionCall _ ->
    Error "Not implemented (Frontend.expr_to_expr - FunctionCall)"
  | NamelessInstantiation _ ->
    Error "Not implemented (Frontend.expr_to_expr - NamelessInstantiation)"
  | Mask _ -> Error "Not implemented (Frontend.expr_to_expr - Mask)"
  | Range _ -> Error "Not implemented (Frontend.expr_to_expr - Range)"

let rec stmt_to_command (headers_param_name : string)
    (header_table : Syntax.HeaderTable.t) (stmt : Petr4.Types.Statement.pre_t) =
  match stmt with
  | MethodCall
      { func = _, ExpressionMember { name; expr }; type_args = []; args = [] }
    ->
    if String.(snd name = "setValid") then
      let%map inst = expr_to_instance headers_param_name header_table expr in
      Syntax.Add inst
    else
      Error "Not implemented (Frontend.stmt_to_command - MethodCall [0])"
  | MethodCall { func; args; _ } -> (
    match snd func with
    | ExpressionMember { name; _ } as exprm ->
      if String.(snd name = "extract") then
        match args with
        | [ (_, arg) ] -> (
          (* Log.debug (fun m -> m "Argument: %s" (Sexplib.Sexp.to_string_hum
             (Petr4.Types.Argument.sexp_of_pre_t arg))); *)
          match arg with
          | Expression
              { value =
                  ( _,
                    ExpressionMember
                      { expr = _, ExpressionMember { name = _, inst_name; _ };
                        name
                      } )
              }
            when String.(snd name = "next") ->
            Log.debug (fun m -> m "Stack: %s" inst_name);
            Error "TODO: Extract into header stack"
          | Expression
              { value = _, ExpressionMember { name = _, inst_name; _ } } ->
            let%map inst =
              Syntax.HeaderTable.lookup_instance inst_name header_table
            in
            Syntax.Extract inst
          | Expression
              { value =
                  ( _,
                    ArrayAccess
                      { array = _, ExpressionMember { name = _, inst_name; _ };
                        index = _, Int (_, { value; _ })
                      } )
              } ->
            Syntax.(
              let%bind array_idx = bigint_to_int value in
              let%map inst =
                HeaderTable.lookup_instance
                  (inst_name ^ string_of_int array_idx)
                  header_table
              in
              Extract inst)
          | Expression _ -> Error "Not implemented (Frontend.stmt_to_command)"
          | _ -> Error "TODO: Argument is not an expression")
        | _ -> Error "Invalid argument to extract"
      else if String.(snd name = "emit") then
        match args with
        | [ (_, arg) ] -> (
          match arg with
          | Expression
              { value = _, ExpressionMember { name = _, inst_name; _ } } ->
            let%map inst =
              Syntax.HeaderTable.lookup_instance inst_name header_table
            in
            Syntax.If ((Syntax.Expression.IsValid (0, inst)), Syntax.Remit inst, Syntax.Skip)
          | Expression _ -> Error "Not implemented (Frontend.stmt_to_command)"
          | _ -> Error "Argument to emit is not an expression"
        )
        | _ -> Error "Invalid argument to emit"
      else
        (Fmt.pr "%s" (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_pre_t exprm));
        Error (Printf.sprintf "Unrecognized method call %s" (snd name)))
    | _ -> Error "Method Called on a Non-member expression")
  | Assignment { lhs = _, ExpressionMember { expr; name = _, field }; rhs } -> (
    match expr_to_instance headers_param_name header_table expr with
    | Ok inst ->
      let open Syntax in
      let%bind l, r = Instance.field_bounds inst field in
      let%map bv = expr_to_term header_table (r - l) rhs in
      Assign (inst, l, r, bv)
    | Error e -> Error e)
  | Assignment _ ->
    Error "Not implemented (Frontend.stmt_to_command - Assignment)"
  | DirectApplication _ ->
    Error "Not implemented (Frontend.stmt_to_command - DirectApplication)"
  | Conditional { cond; tru; fls } ->
    let%bind expr = expr_to_expr headers_param_name header_table cond in
    let%bind tru_cmd =
      stmt_to_command headers_param_name header_table (snd tru)
    in
    let%map fls_cmd =
      Option.map fls ~f:(fun (_, fls_stmt) ->
          stmt_to_command headers_param_name header_table fls_stmt)
      |> Option.value ~default:(Ok Syntax.Skip)
    in
    Syntax.If (expr, tru_cmd, fls_cmd)
  | BlockStatement { block } ->
    block_to_command headers_param_name header_table block
  | Exit -> Error "Not implemented (Frontend.stmt_to_command - Exit)"
  | EmptyStatement ->
    Error "Not implemented (Frontend.stmt_to_command - EmptyStatement)"
  | Return _ -> Error "Not implemented (Frontend.stmt_to_command - Return)"
  | Switch _ -> Error "Not implemented (Frontend.stmt_to_command - Switch)"
  | DeclarationStatement _ ->
    Error "Not implemented (Frontend.stmt_to_command - DeclarationStatement)"

and block_to_command (headers_param : string)
    (header_table : Syntax.HeaderTable.t) (block : Petr4.Types.Block.t) =
  List.fold (snd block).statements ~init:(Ok Syntax.Skip)
    ~f:(fun acc_result (_, stmt) ->
      let%bind acc = acc_result in
      let%map cmd = stmt_to_command headers_param header_table stmt in
      Syntax.Seq (acc, cmd))

let add_header_type_decl (acc : Syntax.Declaration.field list String.Map.t)
    ((_, name) : Petr4.Types.P4String.t)
    (fields : Petr4.Types.Declaration.field list) =
  let%map fields =
    List.map fields ~f:(fun (_, field) ->
        let%bind field_size = field_size_from_type field.typ in
        let%map n = bigint_to_int field_size in
        Syntax.Declaration.{ name = snd field.name; typ = n })
    |> Utils.sequence_error
  in
  Map.set acc ~key:name ~data:fields

let build_header_table (Petr4.Types.Program decls) =
  Log.debug (fun m -> m "build_header_table");
  let%bind type_decls =
    List.fold decls ~init:(Ok String.Map.empty) ~f:(fun acc_result decl ->
        let%bind acc = acc_result in
        match snd decl with
        | Header { name; fields; _ } -> add_header_type_decl acc name fields
        | Struct { name; fields; _ } ->
          let type_name = snd name in
          if String.(type_name = "headers" || type_name = "metadata") then
            return acc
          else
            add_header_type_decl acc name fields
        | _ -> return acc)
  in
  let lookup_fields header_type =
    String.Map.find type_decls header_type
    |> Result.of_option
         ~error:
           (Printf.sprintf "Header type '%s' was not declared." header_type)
  in
  let%bind header_table =
    List.fold decls ~init:(Ok String.Map.empty) ~f:(fun acc decl ->
        match snd decl with
        | Struct { name; fields; _ } ->
          if String.(snd name = "headers" || snd name = "metadata") then
            List.fold fields ~init:acc ~f:(fun acc_result (_, field) ->
                let%bind inner_acc = acc_result in
                match snd field.typ with
                | TypeName (BareName (_, name)) ->
                  let%map fields = lookup_fields name in
                  String.Map.set inner_acc ~key:(snd field.name) ~data:fields
                | HeaderStack
                    { header = _, TypeName (BareName (_, name));
                      size = _, Petr4.Types.Expression.Int (_, { value; _ })
                    } ->
                  let%bind size = bigint_to_int value in
                  let%map fields = lookup_fields name in
                  List.fold (List.range 0 size) ~init:inner_acc
                    ~f:(fun macc idx ->
                      String.Map.set macc
                        ~key:(Printf.sprintf "%s%d" (snd field.name) idx)
                        ~data:fields)
                | _ -> Error "Not implemented")
          else
            acc
        | _ -> acc)
  in
  let%map standard_meta_fields = lookup_fields "standard_metadata_t" in
  Map.set header_table ~key:"standard_metadata" ~data:standard_meta_fields

let mk_empty_node name =
  CfgNode.{ name; statements = []; successors = EdgeSet.empty }

let collect_parser_states (headers_param_name : string)
    (header_table : Syntax.HeaderTable.t)
    (states : Petr4.Types.Parser.state list) =
  let accept = mk_empty_node "accept" in
  let reject = mk_empty_node "reject" in
  let init : CfgNode.t String.Map.t =
    String.Map.of_alist_exn [ ("accept", accept); ("reject", reject) ]
  in
  List.fold states ~init:(Ok init) ~f:(fun acc_result (_, state) ->
      let%bind acc = acc_result in
      let%map statements =
        List.filter_map state.statements ~f:(fun (_, stmt) ->
            Some (stmt_to_command headers_param_name header_table stmt))
        |> Utils.sequence_error
      in
      Map.set acc ~key:(snd state.name)
        ~data:
          CfgNode.
            { name = snd state.name; statements; successors = EdgeSet.empty })

let build_cfg_edges (transition : Petr4.Types.Parser.transition)
    (cfg_nodes : CfgNode.t String.Map.t) (header_table : Syntax.HeaderTable.t) :
    (Edge.t list, string) result =
  match snd transition with
  | Select { exprs; cases } ->
    let%bind inst, field =
      List.find_map exprs ~f:(fun (_, expr) ->
          match expr with
          | ExpressionMember { expr = hdr; name } ->
            let field_name = snd name in
            (let%bind inst_name =
               match snd hdr with
               | ExpressionMember { name; _ } -> return (snd name)
               | ArrayAccess
                   { array = _, ExpressionMember { name = _, inst_name; _ };
                     index = _, Int (_, { value; _ })
                   } ->
                 let%map array_idx = bigint_to_int value in
                 inst_name ^ string_of_int array_idx
               | _ ->
                 Error "Not implemented (Frontend.build_cfg_edges - Expression)"
             in
             let%map inst =
               Syntax.HeaderTable.lookup_instance inst_name header_table
             in
             (inst, field_name))
            |> Some
          | _ -> None)
      |> Option.value ~default:(Error "Could not process select expression.")
    in

    List.fold cases ~init:(Ok []) ~f:(fun edges_acc (_, { matches; next }) ->
        let next' = String.Map.find_exn cfg_nodes (snd next) in
        List.fold matches ~init:edges_acc ~f:(fun match_acc_result (_, mtch) ->
            let%bind match_acc = match_acc_result in
            let%map edge_type =
              match mtch with
              | Default -> return EdgeType.Default
              | DontCare ->
                Error "Not implemented (Frontend.build_cfg_edges - DontCare)"
              | Expression { expr = _, Int n } ->
                return (EdgeType.Match (inst, field, (snd n).value))
              | Expression { expr = _ } ->
                Error "Not implemented (Frontend.build_cfg_edges - Expression)"
            in
            let edge = Edge.{ node = next'; typ = edge_type } in
            edge :: match_acc))
  | Direct { next } ->
    let%map next =
      String.Map.find cfg_nodes (snd next)
      |> Result.of_option ~error:"Next node not found."
    in
    [ Edge.{ node = next; typ = EdgeType.Default } ]

let build_parser_cfg (Petr4.Types.Program decls)
    (header_table : Syntax.HeaderTable.t) =
  List.find_map decls ~f:(fun decl ->
      match snd decl with
      | Parser { states; params; _ } ->
        (let%bind headers_param_name = param_name "headers" params in
         (* Log.debug (fun m -> *)
         (* m "States: %s" *)
         (* (Sexplib.Sexp.to_string_hum *)
         (* ((List.sexp_of_t Petr4.Types.Parser.sexp_of_state) states))); *)
         let%bind cfg_nodes =
           collect_parser_states headers_param_name header_table states
         in
         Logs.debug (fun m ->
             m "CFG Nodes: %s"
               (Sexplib.Sexp.to_string_hum
                  (String.Map.sexp_of_t CfgNode.sexp_of_t cfg_nodes)));
         List.fold states ~init:(Ok cfg_nodes) ~f:(fun acc_result (_, state) ->
             let%bind acc = acc_result in
             let node_name = snd state.name in
             let node = String.Map.find_exn acc node_name in
             let%map edges =
               build_cfg_edges state.transition cfg_nodes header_table
             in
             let edge_set =
               List.fold edges ~init:node.successors ~f:(fun acc edge ->
                   EdgeSet.add acc edge)
             in
             String.Map.set acc ~key:node_name
               ~data:{ node with successors = edge_set }))
        |> Some
      | _ -> None)
  |> Option.value ~default:(Error "No parser declarations found.")

let build_parser (cfg : CfgNode.t String.Map.t) =
  let%bind start =
    String.Map.find cfg "start"
    |> Result.of_option ~error:"CFG does not contain state 'start'."
  in
  let rec build_parser_aux (state : CfgNode.t) =
    let stmts_cmd =
      List.fold state.statements ~init:Syntax.Skip ~f:(fun acc stmt ->
          Syntax.Seq (stmt, acc))
    in
    if Set.is_empty state.successors then
      return stmts_cmd
    else
      let default, successors =
        Set.partition_tf state.successors ~f:(fun edge ->
            match edge.typ with
            | EdgeType.Default -> true
            | _ -> false)
      in
      let%bind default_edge =
        Result.of_option (Set.nth default 0)
          ~error:"Default successor is missing."
      in
      let default_cmd =
        match default_edge.node with
        | { name = "accept"; _ } ->
          if Set.is_empty successors then
            return stmts_cmd
          else
            return Syntax.Skip
        | { name = "reject"; _ } -> Error "Don't know how to handle reject."
        | _ as node -> build_parser_aux node
      in
      if Set.is_empty successors then
        default_cmd
      else
        let%map succ_cmd =
          Set.fold successors ~init:default_cmd ~f:(fun acc_result edge ->
              let%bind acc = acc_result in
              match edge.typ with
              | EdgeType.Default ->
                Error
                  "Default edges should have been filtered out at this point."
              | EdgeType.Match (inst, field, value) ->
                let%bind slice = Syntax.Term.field_to_slice inst field 0 in
                let%bind inst_field = Syntax.Instance.get_field inst field in
                let%bind bv = bigint_to_bv value inst_field.typ in
                let expr = Syntax.(Expression.TmEq (slice, bv)) in
                let%bind node =
                  String.Map.find cfg edge.node.name
                  |> Result.of_option ~error:"Could not lookup node from CFG."
                in
                let%map cmd = build_parser_aux node in
                Syntax.If (expr, cmd, acc))
        in
        Syntax.Seq (stmts_cmd, succ_cmd)
  in
  let%map result = build_parser_aux start in
  Simplify.simplify_command result

type pi4_annotation =
  | TypeAnnotation of string
  | RoundtripAnnotation of string

let extract_annotation_body (annotation : Petr4.Types.Annotation.pre_t) =
  match snd annotation.body with
  | Petr4.Types.Annotation.Unparsed (body :: _) ->
    String.chop_prefix_if_exists
      (String.chop_suffix_if_exists (snd body) ~suffix:"\"")
      ~prefix:"\""
    |> Some
  | _ -> None

let find_type_annotation (annotations : Petr4.Types.Annotation.t list) =
  List.find_map annotations ~f:(fun (_, annot) ->
      match snd annot.name with
      | "pi4" ->
        extract_annotation_body annot
        |> Option.map ~f:(fun a -> TypeAnnotation a)
      | "pi4_roundtrip" ->
        extract_annotation_body annot
        |> Option.map ~f:(fun a -> RoundtripAnnotation a)
      | _ -> None)

let find_parser_annotations (decls : Petr4.Types.Declaration.t list) =
  List.find_map decls ~f:(fun decl ->
      match snd decl with
      | Parser { annotations; _ } -> Some annotations
      | _ -> None)

let annotated_parser_type (Petr4.Types.Program decls)
    (header_table : Syntax.HeaderTable.t) =
  let parser_annotations = find_parser_annotations decls in
  match parser_annotations with
  | Some annotations -> (
    match find_type_annotation annotations with
    | Some (TypeAnnotation ty_annot) ->
      Ok (Parsing.parse_type ty_annot header_table)
    | _ -> Error "Expected a parser type annotation")
  | None -> Error "No parser annotations found"

let control_to_command (control : string) (Petr4.Types.Program decls)
    (header_table : Syntax.HeaderTable.t) =
  List.find_map decls ~f:(fun decl ->
      match snd decl with
      | Control { name; apply; params; _ } ->
        if String.(control = snd name) then
          (let%bind headers_param_name = param_name "headers" params in
           let%map cmd =
             block_to_command headers_param_name header_table apply
           in
           Simplify.simplify_command cmd)
          |> Some
        else
          None
      | _ -> None)
  |> Option.value
       ~default:
         (Error (Printf.sprintf "No control with name '%s' found" control))

let find_type_for_control (control : string) (Petr4.Types.Program decls)
    (header_table : Syntax.HeaderTable.t) =
  List.find_map decls ~f:(fun decl ->
      match snd decl with
      | Control { name; annotations; _ } ->
        if String.(control = snd name) then
          match find_type_annotation annotations with
          | Some (TypeAnnotation ty_annot) ->
            Some (Ok (Parsing.parse_type ty_annot header_table))
          | _ -> None
        else
          None
      | _ -> None)
  |> Option.value
       ~default:
         (Error (Printf.sprintf "No control with name '%s' found" control))
