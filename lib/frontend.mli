open Core

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

val build_header_table :
  Bigint.t String.Map.t ->
  Petr4.Types.program ->
  (Syntax.Declaration.field list String.Map.t, [> error ]) result

val collect_annotations :
  Syntax.HeaderTable.t -> Petr4.Types.program -> Syntax.Annotation.t list

val annotation_to_command :
  Syntax.HeaderTable.t ->
  constants ->
  instantiated_controls ->
  Petr4.Types.Declaration.t list ->
  Syntax.Annotation.t ->
  ( Syntax.Command.t,
    [> `ConversionError of string
    | `FieldAccessError of string
    | `FrontendError of string
    | `InvalidArgumentError of string
    | `LookupError of string
    | `NotImplementedError of string
    ] )
  result

val collect_constants :
  Bigint.t String.Map.t ->
  Petr4.Types.program ->
  (constant String.Map.t, [> error ]) result

val get_type_declarations :
  Petr4.Types.Declaration.t list -> (Bigint.t String.Map.t, [> error ]) result

val instantiated_controls :
  Syntax.HeaderTable.t ->
  constants ->
  Petr4.Types.Declaration.t list ->
  ( Syntax.Command.t String.Map.t,
    [> `ConversionError of string
    | `FieldAccessError of string
    | `FrontendError of string
    | `InvalidArgumentError of string
    | `LookupError of string
    | `NotImplementedError of string
    ] )
  result
