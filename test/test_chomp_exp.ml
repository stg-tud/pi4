open Alcotest
open Pi4
open Syntax
open Expression

let pp e = Pretty.pp_expr [ ("y", Env.NameBind); ("x", Env.NameBind) ] e

let eq x y = [%compare.equal: Expression.t] x y

let exp = Alcotest.testable pp eq

let foo_inst = Instance.{ name = "foo"; fields = [] }

module T = Typechecker.CompleteChecker (struct
  let maxlen = 32
end)

let test_chomp_true () =
  let e = True in
  let actual = T.chomp_e1 e 0 0 in
  let expected = e in
  Alcotest.(check exp) "T.chomp_e1 True should be True" expected actual

let test_chomp_false () =
  let e = False in
  let actual = T.chomp_e1 e 0 0 in
  let expected = e in
  Alcotest.(check exp) "T.chomp_e1 False should be False" expected actual

let test_chomp_valid1 () =
  let e = IsValid (1, foo_inst) in
  let actual = T.chomp_e1 e 0 0 in
  let expected = e in
  Alcotest.(check exp) "T.chomp_e1 y.valid x should be y.valid" expected actual

let test_chomp_valid2 () =
  let e = IsValid (0, foo_inst) in
  let actual = T.chomp_e1 e 0 0 in
  let expected = e in
  Alcotest.(check exp) "T.chomp_e1 x.valid x should be x.valid" expected actual

let plus1 t = Term.Plus (t, Num 1)

let x_inLength = Term.Length (0, PktIn)

let y_inLength = Term.Length (1, PktIn)

let y_inLength_Plus1 = plus1 y_inLength

let x_outLength = Term.Length (0, PktOut)

let test_chomp_TmEq_unchanged () =
  let e = TmEq (Num 1, x_outLength) in
  let actual = T.chomp_e1 e 0 0 in
  let expected = e in
  Alcotest.(check exp)
    "T.chomp_e1 1=|x.PktOut| x should be 1=|x.PktOut|" expected actual

let test_chomp_TmEq_inductive1 () =
  let e = TmEq (y_inLength, x_inLength) in
  let actual = T.chomp_e1 e 1 0 in
  let expected = TmEq (Plus (y_inLength, Num 1), x_inLength) in
  Alcotest.(check exp)
    "T.chomp_e1 |y.PktIn|=|x.PktIn| y should be |y.PktIn|+1=|x.PktIn|" expected
    actual

let test_chomp_TmEq_inductive2 () =
  let e = TmEq (y_inLength_Plus1, y_inLength) in
  let actual = T.chomp_e1 e 1 0 in
  let expected = TmEq (Plus (y_inLength_Plus1, Num 1), y_inLength_Plus1) in
  Alcotest.(check exp)
    "T.chomp_e1 |y.PktIn|+1=|y.PktIn| y should be |y.PktIn|+1+1=|y.PktIn|+1"
    expected actual

(* ε <: ∅ *)

let test_chomp_neg_unchanged () =
  let e = Neg True in
  let actual = T.chomp_e1 e 0 0 in
  let expected = e in
  Alcotest.(check exp) "T.chomp_e1 ¬True should be ¬True" expected actual

let test_chomp_neg_inductive () =
  let e = Neg (TmEq (Num 1, y_inLength)) in
  let actual = T.chomp_e1 e 1 0 in
  let expected = Neg (TmEq (Num 1, y_inLength_Plus1)) in
  Alcotest.(check exp)
    "T.chomp_e1 ¬ 1=|y.PktIn| y should be ¬ 1=|y.PktIn|+1" expected actual

let test_chomp_And_unchanged () =
  let e = And (False, TmEq (x_outLength, x_inLength)) in
  let actual = T.chomp_e1 e 1 0 in
  let expected = e in
  Alcotest.(check exp)
    "T.chomp_e1 false ∧ |x.PktOut|=|x.PktIn| y should be false ∧ |x.PktOut|=|x.PktIn|"
    expected actual

let test_chomp_And_inductive () =
  let e = And (True, TmEq (y_inLength, x_inLength)) in
  let actual = T.chomp_e1 e 1 0 in
  let expected = And (True, TmEq (y_inLength_Plus1, x_inLength)) in
  Alcotest.(check exp)
    "T.chomp_e1 true ∧ |y.PktIn|=|x.PktIn| y should be true ∧ |y.PktIn|+1=|x.PktIn|"
    expected actual

let test_chomp_combined_expr () =
  let a = TmEq (plus1 (plus1 x_inLength), y_inLength_Plus1) in
  let b = IsValid (0, foo_inst) in
  let e = Neg (And (Neg a, Neg b)) in
  let actual = T.chomp_e1 e 0 0 in
  let a' = TmEq (plus1 (plus1 (plus1 x_inLength)), y_inLength_Plus1) in
  let expected = Neg (And (Neg a', Neg b)) in
  Alcotest.(check exp)
    "T.chomp_e1 |x.PktIn|+1+1=|y.PktIn|+1 ∨ x.foo.valid x should be |x.PktIn|+1+1+1=|y.PktIn|+1 ∨ x.foo.valid"
    expected actual

let test_set =
  [ test_case "true" `Quick test_chomp_true;
    test_case "false" `Quick test_chomp_false;
    test_case "y.valid" `Quick test_chomp_valid1;
    test_case "x.valid" `Quick test_chomp_valid2;
    test_case "1=|x.PktOut|" `Quick test_chomp_TmEq_unchanged;
    test_case "|y.PktIn|=|x.PktIn|" `Quick test_chomp_TmEq_inductive1;
    test_case "|y.PktIn|+1=|y.PktIn|" `Quick test_chomp_TmEq_inductive2;
    test_case "¬true" `Quick test_chomp_neg_unchanged;
    test_case "¬ 1=|y.PktIn|" `Quick test_chomp_neg_inductive;
    test_case "false ∧ |x.PktOut|=|x.PktIn|" `Quick test_chomp_And_unchanged;
    test_case "true ∧ |y.PktIn|=|x.PktIn|" `Quick test_chomp_And_inductive;
    test_case "|x.PktIn|=|y.PktIn| ∨ x.foo.valid" `Quick
      test_chomp_combined_expr
  ]
