open Syntax

val fold_plus : Expression.arith -> Expression.arith

val fold_concat : Expression.bv -> Expression.bv

val simplify_expr : Expression.t -> Expression.t

val simplify_form : Formula.t -> Formula.t

val fold_refinements : HeapType.t -> HeapType.t

val simplify_command : Command.t -> Command.t
