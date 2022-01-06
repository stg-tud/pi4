open Core_kernel

type error =
  [ `ConversionError of string
  | `HeaderTypeNotDeclaredError of string
  | `NotImplementedError of string
  ]

val build_header_table :
  Petr4.Types.program ->
  (Syntax.Declaration.field list String.Map.t, [> error ]) result

val parser_to_command :
  Syntax.HeaderTable.t ->
  Petr4.Types.Parser.state list ->
  Petr4.Types.Parameter.t list ->
  ( Syntax.Command.t,
    [> error
    | `FrontendError of string
    | `FieldAccessError of string
    | `LookupError of string
    | `InvalidArgumentError of string
    ] )
  result

val control_to_command :
  Syntax.HeaderTable.t ->
  Petr4.Types.Block.t ->
  Petr4.Types.Parameter.t list ->
  ( Syntax.Command.t,
    [> error
    | `FieldAccessError of string
    | `InvalidArgumentError of string
    | `FrontendError of string
    | `LookupError of string
    ] )
  result

val collect_annotations :
  Syntax.HeaderTable.t -> Petr4.Types.program -> Syntax.Annotation.t list

val annotation_to_command :
  Petr4.Types.Declaration.t list ->
  Syntax.Annotation.t ->
  (Syntax.Command.t, 'a) result
