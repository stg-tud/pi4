open Core_kernel
open Pi4
open Pretty
open Syntax

let bit = Alcotest.testable pp_bit [%compare.equal: Bit.t]

let bitvector = Alcotest.testable pp_bitvector [%compare.equal: BitVector.t]

let term =
  Alcotest.testable
    (Pretty.pp_expr [ ("y", NameBind); ("x", NameBind) ])
    [%compare.equal: Expression.t]

let pi_type ctx = Alcotest.testable (pp_pi_type ctx) [%compare.equal: pi_type]

let rec eq_hty (x : HeapType.t) (y : HeapType.t) =
  match (x, y) with
  | Sigma (_, x1, x2), Sigma (_, y1, y2) -> eq_hty x1 y1 && eq_hty x2 y2
  | Refinement (_, x1, e1), Refinement (_, y1, e2) ->
    eq_hty x1 y1 && [%compare.equal: Formula.t] e1 e2
  | Choice (l1, r1), Choice (l2, r2) -> eq_hty l1 l2 && eq_hty r1 r2
  | Substitution (l1, _, r1), Substitution (l2, _, r2) ->
    eq_hty l1 l2 && eq_hty r1 r2
  | _ -> [%compare.equal: HeapType.t] x y

let hty = Alcotest.testable (Pretty.pp_header_type []) eq_hty

let program = Alcotest.testable pp_program [%compare.equal: Program.t]

let command = Alcotest.testable pp_command [%compare.equal: Command.t]

let typechecker_result =
  Alcotest.testable Typechecker.TypecheckingResult.pp [%compare.equal: Typechecker.TypecheckingResult.t]
