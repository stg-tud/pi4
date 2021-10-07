open Syntax

val fold_plus : Term.t -> Term.t

val simplify_term : Term.t -> Term.t

val simplify_expr : Expression.t -> Expression.t

val fold_refinements : HeapType.t -> HeapType.t

val simplify_command : command -> command
