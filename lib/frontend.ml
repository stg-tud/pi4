open Core
open Result.Let_syntax
module Log = (val Logs.src_log Logging.frontend_src : Logs.LOG)

type error =
  [ `ConversionError of string
  | `HeaderTypeNotDeclaredError of string
  | `NotImplementedError of string
  | `TypeDeclarationNotFoundError of string
  | `FrontendError of string
  | `LookupError of string
  ]

type constant =
  { typ : Bigint.t;
    value : Bigint.t
  }
[@@deriving sexp, compare]

type constants = constant String.Map.t [@@deriving sexp, compare]

type instantiated_controls = Syntax.Command.t String.Map.t
[@@deriving sexp, compare]

let bigint_to_int bint =
  Bigint.to_int bint
  |> Result.of_option ~error:(`ConversionError "Can't convert Bigint to int.")

let bigint_to_bv (n : Bigint.t) (size : int) =
  let%bind int_value = bigint_to_int n in
  let bv_str = Utils.bin_of_int int_value in
  let size_diff = size - String.length bv_str in
  if size_diff < 0 then
    Error
      (`ConversionError
        (Printf.sprintf "Can't fit value '%s' into a bitvector of size %d."
           (Bigint.to_string n) size))
  else return (Syntax.bv_s (String.init size_diff ~f:(fun _ -> '0') ^ bv_str))

let int_to_bv_expr n size =
  let bv = Bitv.of_int_us n in
  let bs = Bitv.fold_left (fun s bit -> (if bit then "1" else "0") ^ s) "" bv in
  let substr = String.sub ~pos:(String.length bs - size) ~len:size bs in
  Syntax.Expression.BvExpr (Syntax.bv_s substr)

let param_name (param : string) (params : Petr4.Types.Parameter.t list) =
  List.find_map params ~f:(fun { variable; _ } -> Some (return variable.string))
  |> Option.value
       ~default:
         (Error
            (`FrontendError (Printf.sprintf "No param with name '%s'" param)))

let petr4_name_to_string (name : Petr4.Types.name) =
  match name with
  | BareName { name; _ } | QualifiedName { name; _ } -> name.string

let field_size_from_type (type_decls : Bigint.t String.Map.t)
    (hdr_type : Petr4.Types.Type.t) =
  match hdr_type with
  | Bool _ -> return (Bigint.of_int 1)
  | BitType { expr; _ } -> (
    match expr with
    | Petr4.Types.Expression.Int { x; _ } -> return x.value
    | _ ->
      Error
        (`NotImplementedError
          "Not implemented (Frontend.field_size_from_type - Not an Int)"))
  | TypeName { name = BareName { name = { string; _ }; _ }; _ } -> (
    match String.Map.find type_decls string with
    | Some n -> return n
    | None ->
      Error
        (`TypeDeclarationNotFoundError
          (Fmt.str "Type declaration %s does not exist" string)))
  | _ as e ->
    Log.debug (fun m ->
        m "Expression: %s"
          (Sexplib.Sexp.to_string_hum (Petr4.Types.Type.sexp_of_t e)));
    Error
      (`NotImplementedError
        "Not implemented (Frontend.field_size_from_type - not a BitType nor a \
         BareName)")

let get_type_declarations (decls : Petr4.Types.Declaration.t list) =
  List.fold_result decls ~init:String.Map.empty ~f:(fun acc decl ->
      match decl with
      | Petr4.Types.Declaration.TypeDef
          { name = { string = name; _ }; typ_or_decl = Left t; _ } ->
        let%map field_size = field_size_from_type String.Map.empty t in
        String.Map.add_exn acc ~key:name ~data:field_size
      | _ -> return acc)

let add_header_type_decl (type_decls : Bigint.t String.Map.t)
    (header_type_decls : Syntax.Declaration.field list String.Map.t)
    ({ string = name; _ } : Petr4.Types.P4String.t)
    (fields : Petr4.Types.Declaration.field list) =
  let%map fields =
    List.map fields
      ~f:(fun { typ = field_type; name = { string = field_name; _ }; _ } ->
        let%bind field_size = field_size_from_type type_decls field_type in
        let%map n = bigint_to_int field_size in
        Syntax.Declaration.{ name = field_name; typ = n })
    |> Utils.sequence_error
  in
  Map.set header_type_decls ~key:name ~data:fields

let count_actions (properties : Petr4.Types.Table.property list) =
  List.fold properties ~init:0 ~f:(fun acc prop ->
      match prop with
      | Actions { actions; _ } -> acc + List.length actions
      | _ -> acc)

let build_header_table (type_decls : Bigint.t String.Map.t)
    (Petr4.Types.Program decls) =
  let%bind header_type_decls =
    List.fold decls ~init:(Ok String.Map.empty)
      ~f:(fun header_type_decls decl ->
        header_type_decls >>= fun acc ->
        match decl with
        | Header { name; fields; _ } ->
          add_header_type_decl type_decls acc name fields
        | Struct { name; fields; _ } ->
          let type_name = name.string in
          if String.(type_name = "headers" (* || type_name = "metadata"*)) then
            return acc
          else add_header_type_decl type_decls acc name fields
        | _ -> return acc)
  in
  let lookup_header_type header_type =
    String.Map.find header_type_decls header_type
    |> Result.of_option
         ~error:
           (`HeaderTypeNotDeclaredError
             (Printf.sprintf "Header type '%s' was not declared." header_type))
  in
  let%bind header_table =
    List.fold decls ~init:(Ok String.Map.empty) ~f:(fun acc decl ->
        match decl with
        | Struct { name; fields; _ } ->
          if String.(name.string = "headers" (*|| name.string = "metadata"*))
          then
            List.fold fields ~init:acc
              ~f:(fun acc_result { typ; name = field_name; _ } ->
                let%bind inner_acc = acc_result in
                match typ with
                | TypeName { name = BareName { name = type_name; _ }; _ } ->
                  let%map fields = lookup_header_type type_name.string in
                  String.Map.set inner_acc ~key:field_name.string ~data:fields
                | HeaderStack
                    { header = TypeName { name = BareName { name; _ }; _ };
                      size = Petr4.Types.Expression.Int { x; _ };
                      _
                    } ->
                  let%bind size = bigint_to_int x.value in
                  let%map fields = lookup_header_type name.string in
                  List.fold (List.range 0 size) ~init:inner_acc
                    ~f:(fun macc idx ->
                      String.Map.set macc
                        ~key:(Printf.sprintf "%s_%d" field_name.string idx)
                        ~data:fields)
                | _ ->
                  Log.debug (fun m -> m "field_name: %s" field_name.string);
                  Error
                    (`NotImplementedError
                      (Fmt.str "Frontend.build_header_table: %s"
                         (Sexplib.Sexp.to_string_hum
                            (Petr4.Types.Type.sexp_of_t typ)))))
          else acc
        | _ -> acc)
  in
  let%bind metadata_fields = lookup_header_type "metadata" in
  let header_table =
    if not (List.is_empty metadata_fields) then
      Map.set header_table ~key:"meta" ~data:metadata_fields
    else header_table
  in
  (* Create header instance for standard_metadata *)
  let%bind standard_meta_fields = lookup_header_type "standard_metadata_t" in
  let header_table =
    Map.set header_table ~key:"standard_metadata" ~data:standard_meta_fields
  in
  (* Create header instance for tables *)
  List.fold decls ~init:(Ok header_table) ~f:(fun ht decl ->
      match decl with
      | Control { name = control_name; locals; _ } ->
        let%bind action_params =
          List.fold locals ~init:(Ok String.Map.empty)
            ~f:(fun action_map local ->
              match local with
              | Action { name = action_name; params; _ } ->
                let%bind action_params =
                  List.map params ~f:(fun param ->
                      let%map field_type =
                        match param.typ with
                        | TypeName { name = BareName { name; _ }; _ } ->
                          String.Map.find type_decls name.string
                          |> Option.map ~f:bigint_to_int
                          |> Option.value
                               ~default:
                                 (Error
                                    (`FrontendError
                                      "Could not look up type\n\
                                      \   declaration  \
                                       (Frontend.build_header_table)"))
                        | BitType { expr = Int { x; _ }; _ } ->
                          bigint_to_int x.value
                        | _ ->
                          Error
                            (`NotImplementedError
                              "Action type is not implemented")
                      in
                      ( Fmt.str "%s_%s" action_name.string param.variable.string,
                        field_type ))
                  |> Utils.sequence_error
                in
                action_map >>| fun am ->
                Map.set am ~key:action_name.string ~data:action_params
              | _ -> action_map)
        in
        List.fold locals ~init:ht ~f:(fun ht local ->
            match local with
            | Table { name = table_name; properties; _ } ->
              let%bind key_fields =
                List.find_map properties ~f:(function
                  | Key { keys; _ } ->
                    let key_fields =
                      List.fold keys ~init:(Ok []) ~f:(fun acc_result key ->
                          acc_result >>= fun acc ->
                          match key.key with
                          | ExpressionMember
                              { expr =
                                  Name
                                    { name = BareName { name = header_name; _ };
                                      _
                                    };
                                name = field_name;
                                _
                              }
                          | ExpressionMember
                              { name = field_name;
                                expr =
                                  ExpressionMember { name = header_name; _ };
                                _
                              } ->
                            let%bind inst =
                              Syntax.HeaderTable.lookup_instance
                                header_name.string header_table
                            in
                            let%map field_size =
                              Syntax.Instance.find_field inst field_name.string
                              |> Option.map ~f:(fun field -> field.typ)
                              |> Result.of_option
                                   ~error:
                                     (`FrontendError
                                       (Fmt.str
                                          "Field %s does not exist on\n\
                                          \    instance %s" inst.name
                                          field_name.string))
                            in

                            Syntax.Declaration.
                              { name =
                                  Fmt.str "%s_%s_key" inst.name
                                    field_name.string;
                                typ = field_size
                              }
                            :: acc
                          | FunctionCall _ -> return acc
                          | _ as k ->
                            Log.debug (fun m ->
                                m "Key: %s"
                                  (Sexplib.Sexp.to_string_hum
                                     (Petr4.Types.Expression.sexp_of_t k)));
                            Error
                              (`NotImplementedError
                                "(Frontend.build_header_table - table match\n\
                                \    key)"))
                    in
                    Some key_fields
                  | _ -> None)
                |> Option.value
                     ~default:
                       (Error
                          (`FrontendError
                            (Fmt.str "Table %s does not contain any keys"
                               table_name.string)))
              in

              let action_param_fields =
                List.fold properties ~init:key_fields ~f:(fun field_list prop ->
                    match prop with
                    | Actions { actions; _ } ->
                      List.fold actions ~init:field_list
                        ~f:(fun fields action ->
                          let action_name =
                            match action.name with
                            | BareName { name; _ } | QualifiedName { name; _ }
                              ->
                              name.string
                          in
                          String.Map.find action_params action_name
                          |> Option.value ~default:[]
                          |> List.fold ~init:fields
                               ~f:(fun acc (field_name, field_typ) ->
                                 Syntax.Declaration.
                                   { name = field_name; typ = field_typ }
                                 :: acc))
                    | _ -> field_list)
              in
              let fields =
                Syntax.Declaration.
                  { name = "act";
                    typ = Utils.min_bit_width (count_actions properties)
                  }
                :: action_param_fields
              in
              ht >>| fun t ->
              Map.set t
                ~key:
                  (Fmt.str "%s_%s_table" control_name.string table_name.string)
                ~data:fields
            | _ -> ht)
      | _ -> ht)

let petr4_expr_to_instance (_ : string) (header_table : Syntax.HeaderTable.t)
    (expr : Petr4.Types.Expression.t) =
  match expr with
  | Name { name = BareName { name; _ }; _ }
  | ExpressionMember { expr = Name { name = BareName _; _ }; name; _ } ->
    Syntax.HeaderTable.lookup_instance name.string header_table
  | _ as e ->
    Error
      (`FrontendError
        (Printf.sprintf
           "Not a member expression (Frontend.expr_to_instance): %s"
           (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_t e))))

let is_header_field_access (name : string) (expr : Petr4.Types.Expression.t) =
  match expr with
  | ExpressionMember
      { expr =
          ExpressionMember
            { expr = Name { name = BareName { name = member_name; _ }; _ }; _ };
        _
      } ->
    String.(member_name.string = name)
  | _ -> false

let is_standard_metadata_access (expr : Petr4.Types.Expression.t) =
  match expr with
  | ExpressionMember { expr = Name { name = BareName { name; _ }; _ }; _ } ->
    String.(name.string = "standard_metadata")
  | _ -> false

let rec petr4_expr_to_expr (ctx : Syntax.Expression.bv String.Map.t)
    (header_table : Syntax.HeaderTable.t) (constants : constants) (size : int)
    (expr : Petr4.Types.Expression.t) =
  let open Syntax.Expression in
  match expr with
  | True _ -> return (BvExpr (Syntax.bv_s "1"))
  | Int { x = { value; _ }; _ } ->
    let%map bv = bigint_to_bv value size in
    BvExpr bv
  | ExpressionMember
      { expr = Name { name = BareName { name = instance_name; _ }; _ };
        name = member_name;
        _
      }
  | ExpressionMember
      { expr = ExpressionMember { name = instance_name; _ };
        name = member_name;
        _
      } ->
    Syntax.(
      let%bind inst =
        HeaderTable.lookup_instance instance_name.string header_table
      in
      let%map slice = Expression.field_to_slice inst member_name.string 0 in
      BvExpr slice)
  | Cast { typ = BitType { expr = Int { x; _ }; _ }; expr; _ } -> (
    let%bind cast_size = bigint_to_int x.value in
    match expr with
    | ExpressionMember
        { expr = ExpressionMember { name = instance_name; _ };
          name = field_name;
          _
        } ->
      Syntax.(
        let%bind inst =
          HeaderTable.lookup_instance instance_name.string header_table
        in
        let%map field = Instance.get_field inst field_name.string in
        if field.typ < cast_size then
          let diff = cast_size - field.typ in
          BvExpr
            (Concat
               (bv_s (String.make diff '0'), Expression.instance_slice 0 inst))
        else BvExpr (Slice (Sliceable.Instance (0, inst), 0, cast_size)))
    | _ ->
      Error
        (`NotImplementedError
          "Not implemented (Frontend.petr4_expr_to_expr - Cast)"))
  | BinaryOp { op = Petr4.Types.Op.Minus _; args = e1, e2; _ } -> (
    let%bind tm1 = petr4_expr_to_expr ctx header_table constants size e1 in
    let%bind tm2 = petr4_expr_to_expr ctx header_table constants size e2 in
    match (tm1, tm2) with
    | BvExpr bv1, BvExpr bv2 -> return (BvExpr (Minus (bv1, bv2)))
    | _ ->
      Error
        (`FrontendError
          "Expected BvExpr (Frontend.petr4_expr_to_expr - BinaryOp Minus"))
  | BinaryOp
      { op = Petr4.Types.Op.Plus _;
        args =
          Name { name = BareName { name = constant_name; _ }; _ }, Int { x; _ };
        _
      } ->
    let%bind constant =
      Map.find constants constant_name.string
      |> Result.of_option
           ~error:
             (`FrontendError
               "Could not lookup constant - Frontend.petr4_expr_to_expr - Plus")
    in
    let%bind e1 = bigint_to_int constant.value in
    let%map e2 = bigint_to_int x.value in
    ArithExpr (Plus (Num e1, Num e2))
  | Name { name = BareName { name; _ }; _ } -> (
    match String.Map.find ctx name.string with
    | Some param_expr -> return (BvExpr param_expr)
    | None ->
      (* TODO: Can we unify the constants and ctx? *)
      let%bind const =
        String.Map.find constants name.string
        |> Result.of_option
             ~error:
               (`FrontendError (Fmt.str "Could not look up %s" name.string))
      in
      let%map bv = bigint_to_bv const.value size in
      BvExpr bv)
  | _ as e ->
    Log.debug (fun m ->
        m "Expr: %s"
          (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_t e)));
    Error (`NotImplementedError "Not implemented (Frontend.petr4_expr_to_expr)")

let sizeof (header_table : Syntax.HeaderTable.t)
    (expr : Petr4.Types.Expression.t) =
  match expr with
  | ExpressionMember
      { expr = Name { name = BareName { name = instance_name; _ }; _ };
        name = member_name;
        _
      }
  | ExpressionMember
      { expr = ExpressionMember { name = instance_name; _ };
        name = member_name;
        _
      } ->
    Syntax.(
      let%bind inst =
        HeaderTable.lookup_instance instance_name.string header_table
      in
      let%map field = Instance.get_field inst member_name.string in
      field.typ)
  | _ -> Error (`NotImplementedError "sizeof not implemented for expression.")

let rec petr4_expr_to_formula ctx (headers_param : string)
    (header_table : Syntax.HeaderTable.t) (constants : constants)
    (expr : Petr4.Types.Expression.t) =
  match expr with
  | True _ -> return Syntax.Formula.True
  | False _ -> return Syntax.Formula.False
  | Int _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_formula - Int)")
  | String _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - String)")
  | Name _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_formula - Name)")
  | ArrayAccess _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - ArrayAccess)")
  | BitStringAccess _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - BitStringAccess)")
  | List _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_formula - List)")
  | Record _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - Record)")
  | UnaryOp { op = Not _; arg = e; _ } ->
    let%map e' =
      petr4_expr_to_formula ctx headers_param header_table constants e
    in
    Syntax.Formula.Neg e'
  | UnaryOp _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - UnaryOp)")
  | BinaryOp { op = Eq _; args = e1, e2; _ } ->
    let%bind size =
      if is_header_field_access "hdr" e1 then sizeof header_table e1
      else return 0
    in
    let%bind t1 = petr4_expr_to_expr ctx header_table constants 0 e1 in
    let%map t2 = petr4_expr_to_expr ctx header_table constants size e2 in
    Syntax.Formula.Eq (t1, t2)
  | BinaryOp { op = Gt _; args = e1, e2; _ } ->
    let%bind size =
      if is_header_field_access "hdr" e1 || is_standard_metadata_access e1 then
        sizeof header_table e1
      else return 0
    in
    let%bind t1 = petr4_expr_to_expr ctx header_table constants size e1 in
    let%map t2 = petr4_expr_to_expr ctx header_table constants size e2 in
    Syntax.(Formula.Gt (t1, t2))
  | BinaryOp { op = Ge _; args = e1, e2; _ } ->
    let%bind size =
      if is_header_field_access "hdr" e1 || is_standard_metadata_access e1 then
        sizeof header_table e1
      else return 0
    in
    let%bind t1 = petr4_expr_to_expr ctx header_table constants size e1 in
    let%map t2 = petr4_expr_to_expr ctx header_table constants size e2 in
    Syntax.(Formula.Or (Formula.Gt (t1, t2), Formula.Eq (t1, t2)))
  | BinaryOp { op = And _; args = e1, e2; _ } ->
    let%bind f1 =
      petr4_expr_to_formula ctx headers_param header_table constants e1
    in
    let%map f2 =
      petr4_expr_to_formula ctx headers_param header_table constants e2
    in
    Syntax.Formula.And (f1, f2)
  | BinaryOp { op = Or _; args = e1, e2; _ } ->
    let%bind f1 =
      petr4_expr_to_formula ctx headers_param header_table constants e1
    in
    let%map f2 =
      petr4_expr_to_formula ctx headers_param header_table constants e2
    in
    Syntax.Formula.Or (f1, f2)
  | BinaryOp _ as e ->
    Log.debug (fun m ->
        m "Binary op: %s"
          (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_t e)));
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - BinaryOp)")
  | Cast _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_formula - Cast)")
  | TypeMember _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - TypeMember)")
  | ErrorMember _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - ErrorMember)")
  | ExpressionMember { expr; name = member_name; _ } -> (
    match member_name.string with
    | "isValid" ->
      let%map inst = petr4_expr_to_instance headers_param header_table expr in
      Syntax.Formula.IsValid (0, inst)
    | _ ->
      Error
        (`NotImplementedError
          "Not implemented (Frontend.expr_to_formula - ExpressionMember)"))
  | Ternary _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - Ternary)")
  | FunctionCall { func = e; type_args = []; args = []; _ } ->
    petr4_expr_to_formula ctx headers_param header_table constants e
  | FunctionCall _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - FunctionCall)")
  | NamelessInstantiation _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - NamelessInstantiation)")
  | Mask _ ->
    Error
      (`NotImplementedError "Not implemented (Frontend.expr_to_formula - Mask)")
  | Range _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.expr_to_formula - Range)")

type action_data =
  { name : string;
    params : Petr4.Types.Parameter.t list;
    body : Petr4.Types.Block.t
  }
[@@deriving sexp]

let rec petr4_statement_to_command ctx tables actions
    (headers_param_name : string) (header_table : Syntax.HeaderTable.t)
    (constants : constants) (instantiated_controls : instantiated_controls)
    (control_name : string) (stmt : _ Petr4.Types.Statement.pt) =
  match stmt with
  | MethodCall
      { func = ExpressionMember { name; expr; _ };
        type_args = [];
        args = [];
        _
      } ->
    if String.(name.string = "setValid") then
      let%map inst =
        petr4_expr_to_instance headers_param_name header_table expr
      in
      Syntax.Command.Add inst
    else if String.(name.string = "setInvalid") then
      let%map inst =
        petr4_expr_to_instance headers_param_name header_table expr
      in
      Syntax.Command.Remove inst
    else if String.(name.string = "apply") then
      match expr with
      | Name { name = BareName { name; _ }; _ } ->
        String.Map.find tables name.string
        |> Result.of_option
             ~error:
               (`FrontendError
                 (Fmt.str "Could not lookup table %s to apply" name.string))
      | _ ->
        Error
          (`FrontendError
            "Table application not implemented \
             (Frontend.petr4_statement_to_command - MethodCall [apply]")
    else
      Error
        (`NotImplementedError
          "Not implemented (Frontend.petr4_statement_to_command - MethodCall \
           [0])")
  | MethodCall { func; args; _ } -> (
    match func with
    | ExpressionMember { name; expr; _ } as exprm ->
      if String.(name.string = "emit") then
        match args with
        | [ arg ] -> (
          match arg with
          | Expression { value = ExpressionMember { name = inst_name; _ }; _ }
            ->
            let%map inst =
              Syntax.HeaderTable.lookup_instance inst_name.string header_table
            in
            Syntax.Command.If
              ( Syntax.Formula.IsValid (0, inst),
                Syntax.Command.Remit inst,
                Syntax.Command.Skip )
          | Expression _ ->
            Error
              (`NotImplementedError
                "Not implemented (Frontend.petr4_statement_to_command)")
          | _ ->
            Error
              (`InvalidArgumentError "Argument to emit is not an expression"))
        | _ -> Error (`InvalidArgumentError "Invalid argument to emit")
      else if String.(name.string = "apply") then
        match expr with
        | Name { name = BareName { name = control_inst; _ }; _ } ->
          Map.find instantiated_controls control_inst.string
          |> Result.of_option
               ~error:
                 (`FrontendError
                   "Could not lookup control instance \
                    (Frontend.petr4_statement_to_command)")
        | _ ->
          Error
            (`NotImplementedError
              "Not implemented (Frontend.petr4_statement_to_command - apply)")
      else (
        Fmt.pr "%s"
          (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_t exprm));
        Error
          (`FrontendError
            (Printf.sprintf "Unrecognized method call %s" name.string)))
    | Name { name = BareName { name; _ }; _ }
      when String.(name.string = "mark_to_drop") ->
      (* TODO: Doesn't work if standard_metadata uses a different name *)
      Syntax.(
        let%bind stdmeta_inst =
          HeaderTable.lookup_instance "standard_metadata" header_table
        in
        let%map egress_spec_field_l, egress_spec_field_r =
          Instance.field_bounds stdmeta_inst "egress_spec"
        in
        Command.Assign
          ( stdmeta_inst,
            egress_spec_field_l,
            egress_spec_field_r,
            Expression.BvExpr (bv_s "111111111") ))
    | Name { name = BareName { name; _ }; _ } ->
      Map.find actions name.string
      |> Result.of_option
           ~error:
             (`FrontendError (Fmt.str "Could not lookup action %s" name.string))
    | _ as e ->
      Log.debug (fun m ->
          m "%s"
            (Sexplib.Sexp.to_string_hum (Petr4.Types.Expression.sexp_of_t e)));
      Error
        (`FrontendError
          "Method Called on a Non-member expression \
           (Frontend.petr4_statement_to_command)"))
  | Assignment { lhs = ExpressionMember { expr; name = field; _ }; rhs; _ } -> (
    match petr4_expr_to_instance headers_param_name header_table expr with
    | Ok inst ->
      let open Syntax in
      let%bind l, r = Instance.field_bounds inst field.string in
      let%map bv = petr4_expr_to_expr ctx header_table constants (r - l) rhs in
      Command.Assign (inst, l, r, bv)
    | Error e -> Error e)
  | Assignment _ ->
    Error
      (`FrontendError
        "Not implemented (Frontend.petr4_statement_to_command - Assignment)")
  | DirectApplication _ ->
    Error
      (`FrontendError
        "Not implemented (Frontend.petr4_statement_to_command - \
         DirectApplication)")
  | Conditional { cond; tru; fls; _ } ->
    let%bind expr =
      petr4_expr_to_formula ctx headers_param_name header_table constants cond
    in
    let%bind tru_cmd =
      petr4_statement_to_command ctx tables actions headers_param_name
        header_table constants instantiated_controls control_name tru
    in
    let%map fls_cmd =
      Option.map fls ~f:(fun fls_stmt ->
          petr4_statement_to_command ctx tables actions headers_param_name
            header_table constants instantiated_controls control_name fls_stmt)
      |> Option.value ~default:(Ok Syntax.Command.Skip)
    in
    Syntax.Command.If (expr, tru_cmd, fls_cmd)
  | BlockStatement { block; _ } ->
    control_block_to_command ctx tables actions headers_param_name header_table
      constants instantiated_controls control_name block
  | Exit _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - Exit)")
  | EmptyStatement _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - EmptyStatement)")
  | Return _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - Return)")
  | Switch _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - Switch)")
  | DeclarationStatement _ ->
    Error
      (`NotImplementedError
        "Not implemented (Frontend.petr4_statement_to_command - \
         DeclarationStatement)")

and control_block_to_command ctx (tables : Syntax.Command.t String.Map.t)
    (actions : Syntax.Command.t String.Map.t) (headers_param : string)
    (header_table : Syntax.HeaderTable.t) constants instantiated_controls
    (control_name : string) (block : Petr4.Types.Block.t) =
  List.fold block.statements ~init:(Ok Syntax.Command.Skip)
    ~f:(fun acc_result stmt ->
      let%bind acc = acc_result in
      let%map cmd =
        petr4_statement_to_command ctx tables actions headers_param header_table
          constants instantiated_controls control_name stmt
      in
      Syntax.Command.Seq (acc, cmd))

and control_to_command (header_table : Syntax.HeaderTable.t)
    (constants : constants) (instantiated_controls : instantiated_controls)
    (control_name : string) (control_locals : Petr4.Types.Declaration.t list)
    (control_apply : Petr4.Types.Block.t)
    (control_params : Petr4.Types.Parameter.t list) =
  let%bind headers_param_name = param_name "headers" control_params in

  let act_data =
    List.fold control_locals ~init:String.Map.empty ~f:(fun map local ->
        match local with
        | Action { name; params; body; _ } ->
          Map.set map ~key:name.string
            ~data:{ name = name.string; params; body }
        | _ -> map)
  in

  let%bind non_table_actions =
    List.fold control_locals ~init:(Ok String.Map.empty)
      ~f:(fun acc_res local ->
        match local with
        | Action { name; params = []; body; _ } ->
          let%bind cmd =
            control_block_to_command String.Map.empty String.Map.empty
              String.Map.empty headers_param_name header_table constants
              instantiated_controls control_name body
          in
          acc_res >>| fun acc -> Map.set acc ~key:name.string ~data:cmd
        | _ -> acc_res)
  in

  let%bind table_commands =
    List.fold control_locals ~init:(Ok String.Map.empty)
      ~f:(fun tcmds_result local ->
        match local with
        | Table { name = table_name; properties = table_props; _ } ->
          let table_inst_name =
            Fmt.str "%s_%s_table" control_name table_name.string
          in
          let%bind table_inst =
            Syntax.HeaderTable.lookup_instance table_inst_name header_table
          in
          let%bind table_act_field =
            Syntax.Expression.field_to_slice table_inst "act" 0
          in
          let%bind match_key_form =
            List.fold table_props ~init:(Ok Syntax.Formula.True)
              ~f:(fun form prop ->
                match prop with
                | Key { keys; _ } ->
                  List.fold keys ~init:form ~f:(fun key_form_result key ->
                      match key.key with
                      | ExpressionMember
                          { name = field_name;
                            expr = ExpressionMember { name = header_name; _ };
                            _
                          } ->
                        let key_field_name =
                          Fmt.str "%s_%s_key" header_name.string
                            field_name.string
                        in
                        let%bind table_inst =
                          Syntax.HeaderTable.lookup_instance table_inst_name
                            header_table
                        in
                        let%bind key_field_slice =
                          Syntax.Expression.field_to_slice table_inst
                            key_field_name 0
                        in
                        let%bind header_inst =
                          Syntax.HeaderTable.lookup_instance header_name.string
                            header_table
                        in
                        let%bind field_slice =
                          Syntax.Expression.field_to_slice header_inst
                            field_name.string 0
                        in
                        key_form_result >>| fun key_form ->
                        Syntax.Formula.And
                          ( key_form,
                            Syntax.Formula.Eq
                              (BvExpr key_field_slice, BvExpr field_slice) )
                      | _ -> key_form_result)
                | _ -> form)
          in
          let petr4_actions =
            List.fold table_props ~init:[] ~f:(fun actions prop ->
                match prop with
                | Actions { actions = action_list; _ } ->
                  List.append action_list actions
                | _ -> actions)
          in
          let action_count = List.length petr4_actions in
          let actions_bit_size = Utils.min_bit_width action_count in
          let%bind action_commands =
            List.foldi petr4_actions ~init:(Ok String.Map.empty)
              ~f:(fun idx acc_res action ->
                let action_name = petr4_name_to_string action.name in
                let%bind action_cmd =
                  if String.(action_name = "NoAction") then
                    return Syntax.Command.Skip
                  else
                    let%bind act_data =
                      String.Map.find act_data action_name
                      |> Result.of_option
                           ~error:(`FrontendError "Could not lookup action")
                    in
                    let%bind param_lookup =
                      List.fold act_data.params ~init:(Ok String.Map.empty)
                        ~f:(fun acc_result param ->
                          acc_result >>= fun acc ->
                          let param_name = param.variable.string in
                          let param_field_name =
                            Fmt.str "%s_%s" act_data.name param_name
                          in
                          let%map param_field_slice =
                            Syntax.Expression.field_to_slice table_inst
                              param_field_name 0
                          in
                          Map.set acc ~key:param_name ~data:param_field_slice)
                    in

                    control_block_to_command param_lookup String.Map.empty
                      String.Map.empty headers_param_name header_table constants
                      instantiated_controls control_name act_data.body
                in
                acc_res >>| fun acc ->
                Map.set acc ~key:action_name ~data:(idx, action_cmd))
          in
          let%bind default_action_cmd =
            List.fold table_props ~init:(Ok Syntax.Command.Skip)
              ~f:(fun def_act_res prop ->
                match prop with
                | Custom { name = custom_name; value; _ }
                  when String.(custom_name.string = "default_action") -> (
                  match value with
                  | Name { name = BareName { name = def_act_name; _ }; _ }
                  | FunctionCall
                      { func =
                          Name { name = BareName { name = def_act_name; _ }; _ };
                        _
                      } ->
                    Map.find action_commands def_act_name.string
                    |> Option.map ~f:snd
                    |> Result.of_option
                         ~error:
                           (`FrontendError "Could not lookup default action")
                  | _ as e ->
                    Log.debug (fun m ->
                        m "Default_Action: %s"
                          (Sexplib.Sexp.to_string_hum
                             (Petr4.Types.Expression.sexp_of_t e)));
                    Error
                      (`NotImplementedError
                        "default_action is not a FunctionCall nor a Name"))
                | _ -> def_act_res)
          in
          let actions_cmd =
            Map.data action_commands
            |> List.fold ~init:default_action_cmd ~f:(fun cmd (i, action) ->
                   Syntax.(
                     Command.If
                       ( Formula.Eq
                           ( BvExpr table_act_field,
                             int_to_bv_expr i actions_bit_size ),
                         action,
                         cmd )))
          in
          let table_cmd =
            Syntax.Command.(
              Seq
                ( Add table_inst,
                  Syntax.Command.(If (match_key_form, actions_cmd, Skip)) ))
          in

          tcmds_result >>| fun tcmds ->
          Map.set tcmds ~key:table_name.string ~data:table_cmd
        | _ -> tcmds_result)
  in
  let%map cmd =
    control_block_to_command String.Map.empty table_commands non_table_actions
      headers_param_name header_table constants instantiated_controls
      control_name control_apply
  in
  Simplify.simplify_command cmd

let extract_annotation_body (header_table : Syntax.HeaderTable.t)
    (annotation : _ Petr4.Types.Annotation.pt) =
  match annotation.body with
  | Petr4.Types.Annotation.Unparsed { str = body :: _; _ } ->
    let body =
      String.chop_prefix_if_exists
        (String.chop_suffix_if_exists body.string ~suffix:"\"")
        ~prefix:"\""
    in
    let%map annotation = Parsing.parse_annotation header_table body in
    Some annotation
  | _ -> return None

module Parser = struct
  type header_stack =
    { name : string;
      header_type : string;
      size : int
    }
  [@@deriving sexp, compare]

  type parser_statement =
    | ExtractHeader of Syntax.Instance.t
    | ExtractHeaderStack of header_stack
    | Assignment of Syntax.Instance.t * int * int * Syntax.Expression.t
  [@@deriving sexp, compare]

  type match_expression =
    | HeaderField of Syntax.Instance.t * string
    | LastStackIndex of
        header_stack * string (* string argument is the field name *)
    | Lookahead of Bigint.t
  [@@deriving sexp, compare]

  module ParserCfg = struct
    module type Comp = sig
      type t

      val sexp_of_t : t -> Sexp.t
      val t_of_sexp : Sexp.t -> t
      val compare : t -> t -> int
    end

    module rec CfgNode : sig
      type t =
        { name : string;
          statements : parser_statement list;
          successors : EdgeSet.t
        }
      [@@deriving compare, sexp]

      include Comp with type t := t
    end = struct
      module T = struct
        type t =
          { name : string;
            statements : parser_statement list;
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
        | Match of match_expression * Bigint.t
      [@@deriving compare, sexp]

      include Comp with type t := t
    end = struct
      module T = struct
        type t =
          | Default
          | Match of match_expression * Bigint.t
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

    let mk_empty_node name =
      CfgNode.{ name; statements = []; successors = EdgeSet.empty }
  end

  let extract_parser_statements (constants : constants)
      (header_table : Syntax.HeaderTable.t) header_stacks
      (stmt : _ Petr4.Types.Statement.pt) =
    match stmt with
    | MethodCall { func; args; _ } -> (
      match func with
      | ExpressionMember { name; _ } when String.(name.string = "extract") -> (
        match args with
        | [ arg ] -> (
          match arg with
          | Expression
              { value =
                  ExpressionMember
                    { expr = ExpressionMember { name = inst_name; _ }; name; _ };
                _
              } as e
            when String.(name.string = "next") ->
            Log.debug (fun m ->
                m "Parser: %s"
                  (Sexplib.Sexp.to_string_hum
                     (Petr4.Types.Argument.sexp_of_t e)));

            let%map header_stack =
              Map.find header_stacks inst_name.string
              |> Result.of_option
                   ~error:
                     (`FrontendError
                       (Printf.sprintf
                          "Could not look up header stack for instance %s"
                          inst_name.string))
            in
            ExtractHeaderStack header_stack
          | Expression { value = ExpressionMember { name = inst_name; _ }; _ }
            ->
            let%map inst =
              Syntax.HeaderTable.lookup_instance inst_name.string header_table
            in
            ExtractHeader inst
          | Expression
              { value =
                  ArrayAccess
                    { array = ExpressionMember { name = inst_name; _ };
                      index = Int { x; _ };
                      _
                    };
                _
              } ->
            Syntax.(
              let%bind array_idx = bigint_to_int x.value in
              let%map inst =
                HeaderTable.lookup_instance
                  (Fmt.str "%s_%d" inst_name.string array_idx)
                  header_table
              in
              ExtractHeader inst)
          | Expression _ ->
            Error
              (`NotImplementedError
                "Not implemented (Frontend.extract_parser_statements)")
          | _ ->
            Error (`InvalidArgumentError "TODO: Argument is not an expression"))
        | _ -> Error (`InvalidArgumentError "Invalid argument to extract"))
      | _ -> Error (`FrontendError "Method Called on a Non-member expression"))
    | Assignment { lhs = ExpressionMember { expr; name = field; _ }; rhs; _ } ->
      let%bind inst = petr4_expr_to_instance "" header_table expr in
      let%bind l, r = Syntax.Instance.field_bounds inst field.string in
      let%map bv =
        petr4_expr_to_expr String.Map.empty header_table constants (r - l) rhs
      in
      Assignment (inst, l, r, bv)
    | stmt ->
      Error
        (`NotImplementedError
          (Fmt.str
             "Statement not implemented (Frontend.extract_parser_statements): \
              %s"
             (Sexplib.Sexp.to_string_hum (Petr4.Types.Statement.sexp_of_t stmt))))

  let collect_parser_states (_headers_param_name : string)
      (constants : constants) (header_table : Syntax.HeaderTable.t)
      header_stacks (states : Petr4.Types.Parser.state list) =
    let accept = ParserCfg.mk_empty_node "accept" in
    let reject = ParserCfg.mk_empty_node "reject" in
    let init : ParserCfg.CfgNode.t String.Map.t =
      String.Map.of_alist_exn [ ("accept", accept); ("reject", reject) ]
    in
    List.fold states ~init:(Ok init) ~f:(fun acc_result state ->
        acc_result >>= fun acc ->
        let%map parser_statements =
          List.map state.statements ~f:(fun stmt ->
              extract_parser_statements constants header_table header_stacks
                stmt)
          |> Utils.sequence_error
        in
        Map.set acc ~key:state.name.string
          ~data:
            ParserCfg.CfgNode.
              { name = state.name.string;
                statements = parser_statements;
                successors = ParserCfg.EdgeSet.empty (* header_stack = None *)
              })

  let build_cfg_edges (constants : constants) header_stacks
      (transition : Petr4.Types.Parser.transition)
      (cfg_nodes : ParserCfg.CfgNode.t String.Map.t)
      (header_table : Syntax.HeaderTable.t) =
    match transition with
    | Select { exprs; cases; _ } as s ->
      let%bind match_expr =
        List.find_map exprs ~f:(fun expr ->
            match expr with
            | FunctionCall
                { func =
                    ExpressionMember
                      { expr = Name { name = BareName { name; _ }; _ };
                        name = fname;
                        _
                      };
                  type_args =
                    [ Petr4.Types.Type.BitType { expr = Int { x; _ }; _ } ];
                  _
                }
              when String.(fname.string = "lookahead" && name.string = "packet")
              ->
              Some (Ok (Lookahead x.value))
            | ExpressionMember
                { name = field_name;
                  expr =
                    ExpressionMember
                      { name;
                        expr = ExpressionMember { name = header_stack_name; _ };
                        _
                      };
                  _
                }
              when String.(name.string = "last") ->
              Map.find header_stacks header_stack_name.string
              |> Option.map ~f:(fun hs ->
                     return (LastStackIndex (hs, field_name.string)))
            | ExpressionMember { expr = hdr; name = field_name; _ } ->
              (let%bind inst_name =
                 match hdr with
                 | ExpressionMember { name; _ } -> return name.string
                 | ArrayAccess
                     { array = ExpressionMember { name = inst_name; _ };
                       index = Int { x; _ };
                       _
                     } ->
                   let%map array_idx = bigint_to_int x.value in
                   Fmt.str "%s_%d" inst_name.string array_idx
                 | e ->
                   Error
                     (`NotImplementedError
                       (Fmt.str
                          "Not implemented (Frontend.build_cfg_edges - \
                           Select-Expression (%s))"
                          (Sexplib.Sexp.to_string_hum
                             (Petr4.Types.Expression.sexp_of_t e))))
               in
               let%map inst =
                 Syntax.HeaderTable.lookup_instance inst_name header_table
               in
               HeaderField (inst, field_name.string))
              |> Some
            | _ ->
              Log.debug (fun m ->
                  m "Select: %s"
                    (Sexplib.Sexp.to_string_hum
                       (Petr4.Types.Parser.sexp_of_transition s)));
              None)
        |> Option.value
             ~default:
               (Error (`FrontendError "Could not process select expression."))
      in
      List.fold cases ~init:(Ok []) ~f:(fun edges_acc { matches; next; _ } ->
          let next' = String.Map.find_exn cfg_nodes next.string in
          List.fold matches ~init:edges_acc ~f:(fun match_acc_result mtch ->
              let%bind match_acc = match_acc_result in
              let%map edge_type =
                match mtch with
                | Default _ -> return ParserCfg.EdgeType.Default
                | DontCare _ ->
                  Error
                    (`NotImplementedError
                      "Not implemented (Frontend.build_cfg_edges - DontCare)")
                | Expression { expr = Int { x; _ }; _ } ->
                  return (ParserCfg.EdgeType.Match (match_expr, x.value))
                | Expression
                    { expr = Name { name = BareName { name; _ }; _ }; _ } ->
                  String.Map.find constants name.string
                  |> Option.map ~f:(fun const ->
                         ParserCfg.EdgeType.Match (match_expr, const.value))
                  |> Result.of_option
                       ~error:(`FrontendError "Could not lookup constant")
                | Expression { expr; _ } ->
                  Error
                    (`NotImplementedError
                      (Fmt.str
                         "Not implemented (Frontend.build_cfg_edges - \
                          Match-Expression %s)"
                         (Sexplib.Sexp.to_string_hum
                            (Petr4.Types.Expression.sexp_of_t expr))))
              in
              let edge = ParserCfg.Edge.{ node = next'; typ = edge_type } in
              edge :: match_acc))
    | Direct { next; _ } ->
      let%map next =
        String.Map.find cfg_nodes next.string
        |> Result.of_option ~error:(`FrontendError "Next node not found.")
      in
      [ ParserCfg.Edge.{ node = next; typ = ParserCfg.EdgeType.Default } ]

  let build_parser_cfg (header_table : Syntax.HeaderTable.t)
      (constants : constants) header_stacks
      (parser_states : Petr4.Types.Parser.state list)
      (parser_params : Petr4.Types.Parameter.t list) =
    let%bind headers_param_name = param_name "headers" parser_params in
    let%bind cfg_nodes =
      collect_parser_states headers_param_name constants header_table
        header_stacks parser_states
    in
    let%map cfg =
      List.fold parser_states ~init:(Ok cfg_nodes) ~f:(fun acc_result state ->
          let%bind acc = acc_result in
          let node_name = state.name.string in
          let node = String.Map.find_exn acc node_name in
          let%map edges =
            build_cfg_edges constants header_stacks state.transition cfg_nodes
              header_table
          in
          let edge_set =
            List.fold edges ~init:node.successors ~f:(fun acc edge ->
                ParserCfg.EdgeSet.add acc edge)
          in
          String.Map.set acc ~key:node_name
            ~data:{ node with successors = edge_set })
    in
    let self_loops =
      Map.fold cfg ~init:String.Map.empty ~f:(fun ~key:_ ~data:node acc ->
          match node with
          | ParserCfg.CfgNode.
              { name = node_name;
                successors;
                statements = [ ExtractHeaderStack stack ]
              } ->
            let loops =
              Set.filter successors ~f:(fun ParserCfg.Edge.{ node; _ } ->
                  String.(node.name = node_name))
            in
            let contains_loop = not (Set.is_empty loops) in
            if contains_loop then
              let unrolled_nodes =
                List.fold (List.range 0 stack.size) ~init:String.Map.empty
                  ~f:(fun acc idx ->
                    let indexed_node_name = Fmt.str "%s_%d" node_name idx in
                    let inst_name = Fmt.str "%s_%d" stack.name idx in
                    let inst =
                      Syntax.HeaderTable.lookup_instance_exn inst_name
                        header_table
                    in
                    Map.set acc ~key:indexed_node_name
                      ~data:
                        ( ParserCfg.CfgNode.
                            { name = indexed_node_name;
                              successors = ParserCfg.EdgeSet.empty;
                              statements = [ ExtractHeader inst ]
                            },
                          idx ))
              in
              let with_succs =
                Map.data unrolled_nodes
                |> List.map ~f:(fun (node, idx) ->
                       if idx = stack.size - 1 then
                         let s =
                           Set.filter successors ~f:(fun edge ->
                               match edge with
                               | ParserCfg.Edge.{ typ = Default; _ } -> true
                               | _ -> false)
                         in
                         { node with successors = s }
                       else
                         let unrolled_successors =
                           ParserCfg.EdgeSet.map successors ~f:(fun edge ->
                               match edge with
                               | ParserCfg.Edge.
                                   { node;
                                     typ =
                                       Match
                                         (LastStackIndex (stack, field), value)
                                   }
                                 when String.(node.name = node_name) ->
                                 let next_node, _ =
                                   Map.find_exn unrolled_nodes
                                     (Fmt.str "%s_%d" node.name (idx + 1))
                                 in
                                 let stack_inst =
                                   Syntax.HeaderTable.lookup_instance_exn
                                     (Fmt.str "%s_%d" stack.name idx)
                                     header_table
                                 in
                                 ParserCfg.Edge.
                                   { node = next_node;
                                     typ =
                                       ParserCfg.EdgeType.Match
                                         (HeaderField (stack_inst, field), value)
                                   }
                               | _ as e -> e)
                         in
                         { node with successors = unrolled_successors })
              in
              Map.set acc ~key:node_name ~data:with_succs
            else acc
          | _ -> acc)
    in
    Map.fold cfg ~init:String.Map.empty ~f:(fun ~key ~data:node acc ->
        match String.Map.find self_loops node.name with
        | Some loop_nodes ->
          Log.debug (fun m ->
              m "Node: %s"
                (Sexplib.Sexp.to_string_hum (ParserCfg.CfgNode.sexp_of_t node)));
          List.fold loop_nodes ~init:acc ~f:(fun list_acc n ->
              Map.set list_acc ~key:n.name ~data:n)
        | _ ->
          (* Check if *)
          let update =
            ParserCfg.EdgeSet.map node.successors ~f:(fun edge ->
                let new_node =
                  String.Map.find self_loops edge.node.name
                  |> Option.map ~f:(fun loop_nodes -> List.hd_exn loop_nodes)
                  |> Option.value ~default:edge.node
                in
                { edge with node = new_node })
          in
          Map.set acc ~key ~data:{ node with successors = update })

  let parser_statement_to_command (statement : parser_statement) =
    match statement with
    | ExtractHeader inst -> return (Syntax.Command.Extract inst)
    | Assignment (inst, l, r, expr) ->
      return (Syntax.Command.Assign (inst, l, r, expr))
    | ExtractHeaderStack _ ->
      Error
        (`FrontendError "Parser statement should be eliminated by unrolling.")

  type successor =
    { name : string;
      typ : ParserCfg.EdgeType.t
    }
  [@@deriving sexp, compare]

  type node1 =
    { name : string;
      command : Syntax.Command.t;
      successors : successor list
    }
  [@@deriving sexp, compare]

  let handle_result result =
    match result with Ok r -> r | _ -> failwith "An error occurred"
    
  let parser_cfg_to_command (cfg : ParserCfg.CfgNode.t String.Map.t) =
    let%bind stage1 =
      Map.fold ~init:(Ok String.Map.empty) cfg
        ~f:(fun
             ~key
             ~data:ParserCfg.CfgNode.{ name; statements; successors }
             node_acc
           ->
          node_acc >>= fun acc ->
          let%map cmd =
            List.fold statements ~init:(Ok Syntax.Command.Skip)
              ~f:(fun cmd_acc stmt ->
                cmd_acc >>= fun acc ->
                let%map stmt_cmd = parser_statement_to_command stmt in
                Syntax.Command.Seq (acc, stmt_cmd))
          in
          let succs =
            Set.to_list successors
            |> List.map ~f:(fun ParserCfg.Edge.{ node; typ } ->
                   { name = node.name; typ })
          in
          Map.set acc ~key ~data:{ name; command = cmd; successors = succs })
    in

    let%bind start =
      String.Map.find stage1 "start"
      |> Result.of_option
           ~error:(`FrontendError "CFG does not contain state 'start'.")
    in
    let stage2 = String.Map.remove stage1 "start" in
    let stack = Stack.singleton start in
    let ft =
      Hashtbl.create ~growth_allowed:true ~size:(Map.length stage2)
        (module String)
    in
    Stack.until_empty stack (fun node ->
        (* Check if node is in ft *)
        if Hashtbl.find ft node.name |> Option.is_none then
          if
            (* Node is not fully translated *)
            (* Log.debug (fun m -> m "[%s] Node not fully translated" node.name); *)
            List.is_empty node.successors
          then
            (* Log.debug (fun m -> m "[%s] Successors not empty" node.name); *)
            Hashtbl.set ft ~key:node.name ~data:node.command
          else
            (* Log.debug (fun m -> m "[%s] Successors not empty" node.name); *)
            let non_translated =
              List.fold node.successors ~init:[] ~f:(fun acc succ ->
                  match Hashtbl.find ft succ.name with
                  | Some _ -> acc
                  | None -> succ.name :: acc)
            in
            if List.is_empty non_translated then
              (* All successors are fully translated *)
              (* Create command for current node and put into ft *)
              let default, non_default =
                List.partition_tf node.successors ~f:(fun edge ->
                    match edge.typ with
                    | ParserCfg.EdgeType.Default -> true
                    | _ -> false)
              in
              let default_successor =
                match List.hd default with
                | Some s -> s
                | None -> failwith "Default successor is missing"
              in
              (* Log.debug (fun m -> m "[%s] Default successor %s" node.name
                 (shum ([%sexp_of: successor] default_successor))); *)
              let default_cmd =
                if String.(default_successor.name = "accept") then
                  Syntax.Command.Skip
                else if String.(default_successor.name = "reject") then
                  failwith "Don't know how to handle reject"
                else
                  (* Here we look up the command from ft *)
                  match Hashtbl.find ft default_successor.name with
                  | Some cmd ->
                    if List.is_empty non_default then cmd
                    else Syntax.Command.Seq (node.command, cmd)
                  | None ->
                    failwith
                      (Fmt.str "Successor %s should be fully transformed"
                         default_successor.name)
              in
              (* Log.debug (fun m -> m "[%s] Default command %a" node.name
                 Pretty.pp_command default_cmd); *)
              (* TODO: handle non_default *)
              let successors_cmd =
                if List.is_empty non_default then
                  (* Log.debug (fun m -> m "[%s] Non-default successors empty"
                     node.name); *)
                  default_cmd
                else
                  (* Log.debug (fun m -> m "[%s] Non-default successors not
                     empty" node.name); *)
                  List.fold non_default ~init:default_cmd
                    ~f:(fun acc successor ->
                      match successor.typ with
                      | ParserCfg.EdgeType.Default ->
                        failwith "Unexpected edge type Default"
                      | ParserCfg.EdgeType.Match (LastStackIndex _, _) ->
                        failwith "Unexpected edge type LastStackIndex"
                      | ParserCfg.EdgeType.Match (match_expr, value) ->
                        let form =
                          (match match_expr with
                          | HeaderField (inst, field) ->
                            let%bind slice =
                              Syntax.Expression.field_to_slice inst field 0
                            in
                            let%bind inst_field =
                              Syntax.Instance.get_field inst field
                            in
                            let%map bv = bigint_to_bv value inst_field.typ in
                            Syntax.(Formula.Eq (BvExpr slice, BvExpr bv))
                          | Lookahead amount ->
                            let%bind amount_int = bigint_to_int amount in
                            let%map bv = bigint_to_bv value amount_int in
                            Syntax.Formula.Eq
                              ( BvExpr (Slice (Packet (0, PktIn), 0, amount_int)),
                                BvExpr bv )
                          | _ -> failwith "Unexpected match expression")
                          |> handle_result
                        in
                        let then_cmd =
                          match Hashtbl.find ft successor.name with
                          | Some cmd -> cmd
                          | None ->
                            failwith "Could not lookup command for successor"
                        in
                        Syntax.Command.If (form, then_cmd, acc))
              in
              let nc = Syntax.Command.Seq (node.command, successors_cmd) in

              (* Log.debug (fun m -> m "[%s] Node command: %a" node.name
                 Pretty.pp_command nc); *)
              Hashtbl.set ft ~key:node.name ~data:nc
            else (
              (* Push current node on stack and push every successor that is not
                 fully translated on stack *)
              Stack.push stack node;
              List.iter non_translated ~f:(fun node_name ->
                  match Map.find stage2 node_name with
                  | Some succ_node -> Stack.push stack succ_node
                  | None -> ()))
        else ());

    let start_cmd = Hashtbl.find_exn ft "start" in
    return (Simplify.simplify_command start_cmd)

  let petr4_parser_to_command header_table constants header_stacks parser_states
      parser_params =
    let%bind parser_cfg =
      build_parser_cfg header_table constants header_stacks parser_states
        parser_params
    in
    parser_cfg_to_command parser_cfg
end

let collect_header_stacks (decls : Petr4.Types.Declaration.t list) =
  let extract_header_stack acc decl =
    match decl with
    | Petr4.Types.Declaration.Struct { name; fields; _ }
      when String.(name.string = "headers") ->
      let collect_header_stack acc_result
          Petr4.Types.Declaration.{ name = header_name; typ; _ } =
        match typ with
        | HeaderStack
            { header = TypeName { name = BareName { name = header_type; _ }; _ };
              size = Int { x = stack_size; _ };
              _
            } ->
          let%bind stack_size = bigint_to_int stack_size.value in
          acc_result >>| fun acc ->
          Map.set acc ~key:header_name.string
            ~data:
              Parser.
                { name = header_name.string;
                  header_type = header_type.string;
                  size = stack_size
                }
        | _ -> acc_result
      in
      List.fold fields ~init:acc ~f:collect_header_stack
    | _ -> acc
  in
  List.fold decls ~init:(Ok String.Map.empty) ~f:extract_header_stack

let declaration_to_command (header_table : Syntax.HeaderTable.t)
    (constants : constants) (instantiated_controls : instantiated_controls)
    (decls : Petr4.Types.Declaration.t list) (name : string) =
  let%bind header_stacks = collect_header_stacks decls in
  List.find_map decls ~f:(fun decl ->
      match decl with
      | Parser { name = parser_name; params; states; _ }
        when String.(parser_name.string = name) ->
        Some
          (Parser.petr4_parser_to_command header_table constants header_stacks
             states params)
      | Control { name = control_name; locals; apply; params; _ }
        when String.(control_name.string = name) ->
        Some
          (control_to_command header_table constants instantiated_controls
             control_name.string locals apply params)
      | _ -> None)
  |> Option.value
       ~default:
         (Error
            (`FrontendError
              (Fmt.str "No declaration with name '%s' found." name)))

let find_pi4_annotations (header_table : Syntax.HeaderTable.t)
    (annotations : Petr4.Types.Annotation.t list) =
  List.fold annotations ~init:[] ~f:(fun acc annotation ->
      if String.(annotation.name.string = "pi4") then (
        match extract_annotation_body header_table annotation with
        | Ok pi4_annotation ->
          Option.map pi4_annotation ~f:(fun annot -> annot :: acc)
          |> Option.value ~default:acc
        | Error (`SyntaxError e) ->
          Log.err (fun m -> m "Failed to parse annotation with error %s" e);
          acc)
      else acc)

let collect_annotations (header_table : Syntax.HeaderTable.t)
    (Petr4.Types.Program decls) =
  List.fold decls ~init:[] ~f:(fun acc decl ->
      match decl with
      | Control { annotations; _ }
      | Parser { annotations; _ }
      | Struct { annotations; _ }
      | Header { annotations; _ } ->
        find_pi4_annotations header_table annotations @ acc
      | _ -> acc)

let rec annotation_to_command (header_table : Syntax.HeaderTable.t)
    (constants : constants) (instantiated_controls : instantiated_controls)
    (decls : Petr4.Types.Declaration.t list) (annotation : Syntax.Annotation.t)
    =
  match annotation with
  | TypeAnnotation (body, _) ->
    annotation_body_to_command header_table constants instantiated_controls
      decls body

and annotation_body_to_command (header_table : Syntax.HeaderTable.t)
    (constants : constants) (instantiated_controls : instantiated_controls)
    (decls : Petr4.Types.Declaration.t list)
    (annotation_body : Syntax.Annotation.annotation_body) =
  match annotation_body with
  | Reset -> return Syntax.Command.Reset
  | Block _name ->
    declaration_to_command header_table constants instantiated_controls decls
      _name
  | TypedBlock (body, typ) -> (
    let%map body_cmd =
      annotation_body_to_command header_table constants instantiated_controls
        decls body
    in
    match typ with
    | Pi (binder, input, output) ->
      Syntax.Command.Ascription (body_cmd, binder, input, output))
  | Sequence (l, r) ->
    let%bind l_cmd =
      annotation_body_to_command header_table constants instantiated_controls
        decls l
    in
    let%map r_cmd =
      annotation_body_to_command header_table constants instantiated_controls
        decls r
    in
    Syntax.Command.Seq (l_cmd, r_cmd)

let collect_constants (type_decls : Bigint.t String.Map.t)
    (Petr4.Types.Program decls) =
  List.fold decls ~init:(Ok String.Map.empty) ~f:(fun acc decl ->
      match decl with
      | Petr4.Types.Declaration.Constant
          { name;
            value = Int { x; _ };
            typ = TypeName { name = BareName { name = type_def_name; _ }; _ };
            _
          } ->
        let%bind type_decl =
          Map.find type_decls type_def_name.string
          |> Result.of_option
               ~error:
                 (`FrontendError
                   (Fmt.str
                      "Could not look up type declaration %s \
                       (Frontend.collect_constants)"
                      type_def_name.string))
        in
        acc >>| fun constants ->
        Map.set constants ~key:name.string
          ~data:{ typ = type_decl; value = x.value }
      | Petr4.Types.Declaration.Constant
          { name;
            value = Int { x = cv; _ };
            typ = BitType { expr = Int { x = bs; _ }; _ };
            _
          } ->
        acc >>| fun constants ->
        Map.set constants ~key:name.string
          ~data:{ typ = bs.value; value = cv.value }
      | Petr4.Types.Declaration.Constant _ as c ->
        Log.err (fun m ->
            m "Constant not implemented: %s"
              (Sexplib.Sexp.to_string_hum (Petr4.Types.Declaration.sexp_of_t c)));
        acc
      | _ -> acc)

let instantiated_controls header_table constants
    (decls : Petr4.Types.Declaration.t list) =
  let instantiated =
    List.fold decls ~init:[] ~f:(fun acc decl ->
        match decl with
        | Control { locals; _ } ->
          List.fold locals ~init:acc ~f:(fun inner_acc local ->
              match local with
              | Petr4.Types.Declaration.Instantiation
                  { typ =
                      TypeName { name = BareName { name = control_name; _ }; _ };
                    name = instance_name;
                    _
                  } ->
                (control_name.string, instance_name.string) :: inner_acc
              | _ -> inner_acc)
        | _ -> acc)
  in
  List.fold decls ~init:(Ok String.Map.empty) ~f:(fun acc_result decl ->
      acc_result >>= fun acc ->
      match decl with
      | Control { name; locals; apply; params; _ } ->
        let instance_names =
          List.fold instantiated ~init:[]
            ~f:(fun acc (control_name, instance_name) ->
              if String.(control_name = name.string) then instance_name :: acc
              else acc)
        in
        if not (List.is_empty instance_names) then
          let%map cmd =
            control_to_command header_table constants String.Map.empty
              name.string locals apply params
          in
          List.fold instance_names ~init:acc ~f:(fun macc inst_name ->
              Map.set macc ~key:inst_name ~data:cmd)
        else return acc
      | _ -> acc_result)
