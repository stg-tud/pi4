open Alcotest
open Pi4
open Syntax
open Expression

let test_simplify_plus () =
  let tm =
    Plus (Plus (Plus (Plus (Length (0, PktIn), Num 1), Num 1), Num 1), Num 16)
  in
  Logs.debug (fun m ->
      m "Term: %a" (Pretty.pp_expr [ ("x", NameBind) ]) (ArithExpr tm));
  let simplified = ArithExpr (Simplify.fold_plus tm) in
  let expected = ArithExpr (Plus (Length (0, PktIn), Num 19)) in
  Alcotest.(check Testable.term) "terms are equal" expected simplified

let test_set =
  [ test_case "Plus is simplified correctly" `Quick test_simplify_plus ]
