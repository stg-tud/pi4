open Syntax

val pp_bit : Format.formatter -> Syntax.Bit.t -> unit
val pp_bitvector : Format.formatter -> Syntax.BitVector.t -> unit
val pp_packet : Format.formatter -> Syntax.packet -> unit
val pp_sliceable : Env.context -> Format.formatter -> Sliceable.t -> unit
val pp_sliceable_raw : Format.formatter -> Sliceable.t -> unit
val pp_expr_raw : Format.formatter -> Expression.t -> unit
val pp_bv_expr : Env.context -> Format.formatter -> Expression.bv -> unit
val pp_bv_expr_raw : Format.formatter -> Expression.bv -> unit
val pp_expr : Env.context -> Format.formatter -> Expression.t -> unit
val pp_form : Env.context -> Format.formatter -> Formula.t -> unit
val pp_form_raw : Format.formatter -> Formula.t -> unit
val pp_header_type : Env.context -> Format.formatter -> HeapType.t -> unit
val pp_header_type_raw : Format.formatter -> HeapType.t -> unit
val pp_context : Format.formatter -> Env.context -> unit
val pp_type : Format.formatter -> ty -> unit
val pp_pi_type : Env.context -> Format.formatter -> pi_type -> unit
val pp_pi_type_raw : Format.formatter -> pi_type -> unit
val pp_command : Format.formatter -> Command.t -> unit
val pp_instance : Format.formatter -> Instance.t -> unit
val pp_header_table : Format.formatter -> HeaderTable.t -> unit
val pp_program : Format.formatter -> Program.t -> unit
val pp_ident : Format.formatter -> Z3.Smtlib.identifier -> unit
val pp_sort : Format.formatter -> Z3.Smtlib.sort -> unit

val pp_ident_sort :
  Format.formatter -> Z3.Smtlib.identifier * Z3.Smtlib.sort -> unit

val pp_smtlib_term : Format.formatter -> Z3.Smtlib.term -> unit
val pp_tactic : Format.formatter -> Z3.Smtlib.tactic -> unit
val pp_annotation_body : Format.formatter -> Annotation.annotation_body -> unit
