open Alcotest
open Pi4
open Syntax
open Formula
open HeapType
open Expression

module T = Typechecker.CompleteChecker (struct
  let maxlen = 32
end)

let foo_inst = Test_utils.mk_inst "foo" [ ("a", 4); ("b", 8); ("c", 16) ]

let header_table = HeaderTable.populate [ foo_inst ]

let t1 = Length (1, PktIn)

let t1' = Plus (Length (1, PktIn), Num 1)

let t2 = Plus (Plus (t1, Length (1, PktOut)), Plus (t1, Length (0, PktIn)))

let t2' = Plus (Plus (t1', Length (1, PktOut)), Plus (t1', Length (0, PktIn)))

let t3 =
  Concat (Slice (Packet (1, PktIn), 0, 10), Slice (Packet (1, PktIn), 10, 20))

let t3' =
  Concat
    ( Concat (Bv (Cons (B 0, Nil)), Slice (Packet (1, PktIn), 0, 9)),
      Slice (Packet (1, PktIn), 9, 19) )

let t4 = Concat (Packet (1, PktIn), Packet (0, PktIn))

let t4' =
  Concat (Concat (Bv (Cons (B 0, Nil)), Packet (1, PktIn)), Packet (0, PktIn))

let conj x y = And (x, y)

let disj x y = Neg (conj (Neg x) (Neg y))

let impl x y = disj (Neg x) y

let e1 = Neg (Eq (ArithExpr t1, ArithExpr t2))

let e1' = Neg (Eq (ArithExpr t1', ArithExpr t2'))

let e2 =
  disj (Gt (ArithExpr t1, ArithExpr t2)) (Gt (ArithExpr t2, ArithExpr t1))

let e2' =
  disj (Gt (ArithExpr t1', ArithExpr t2')) (Gt (ArithExpr t2', ArithExpr t1'))

let e3 = impl e2 e1

let e3' = impl e2' e1'

let e4 = conj (Eq (BvExpr t3, BvExpr t4)) (Eq (ArithExpr t2, ArithExpr t1))

let e4' = conj (Eq (BvExpr t3', BvExpr t4')) (Eq (ArithExpr t2', ArithExpr t1'))

let hty_empty = HeapType.empty header_table "x"

let hty_inst inst = HeapType.weak_instance inst "x"

let test_chomp_nothing () =
  let ty = Nothing in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = ty in
  Alcotest.(check Testable.hty) "chomp_ref1 ø should be ø" expected actual

let test_chomp_empty () =
  let ty = hty_empty in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = ty in
  Alcotest.(check Testable.hty) "chomp_ref1 ε should be ε" expected actual

let test_chomp_inst () =
  let ty = hty_inst foo_inst in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = ty in
  Alcotest.(check Testable.hty) "chomp_ref1 foo should be foo" expected actual

let test_chomp_ref1 () =
  let ty = Refinement ("y", hty_empty, e1) in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = Refinement ("y", hty_empty, e1') in
  Alcotest.(check Testable.hty)
    "chomp_ref1 { z:ε | e1 } should be { z:ε | e1' }" expected actual

let test_chomp_ref2 () =
  let ty = Refinement ("y", hty_empty, e3) in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = Refinement ("y", hty_empty, e3') in
  Alcotest.(check Testable.hty)
    "chomp_ref1 { z:{ w:instance | e2 } | e1 } should be { z:{ w:instance | e2 } | e1' }"
    expected actual

let test_chomp_ref3 () =
  let ty =
    Refinement
      ( "y",
        Refinement
          ( "z",
            hty_inst foo_inst,
            Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 1)) ),
        Eq (ArithExpr (Length (1, PktIn)), ArithExpr (Num 1)) )
  in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected =
    Refinement
      ( "y",
        Refinement
          ( "z",
            hty_inst foo_inst,
            Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 1)) ),
        Eq (ArithExpr (Plus (Length (1, PktIn), Num 1)), ArithExpr (Num 1)) )
  in
  Alcotest.(check Testable.hty)
    "chomp_ref1 { y:{ w:instance | e2 } | e1 } should be { y:{ w:instance | e2 } | e1' }"
    expected actual

let test_chomp_ref4 () =
  let ty = Refinement ("y", Refinement ("z", hty_inst foo_inst, e2), e1) in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected =
    Refinement ("y", Refinement ("z", hty_inst foo_inst, e2'), e1')
  in
  Alcotest.(check Testable.hty)
    "chomp_ref1 { y:{ z:instance | e2 } | e1 } should be { y:{ z:instance | e2 } | e1' }"
    expected actual

let test_chomp_sigma1 () =
  let ty =
    Sigma
      ( "y",
        Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (1, PktIn)), ArithExpr (Num 1))),
        Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (1, PktIn)), ArithExpr (Num 1)))
      )
  in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected =
    Sigma
      ( "y",
        Refinement
          ( "z",
            hty_empty,
            Eq (ArithExpr (Plus (Length (1, PktIn), Num 1)), ArithExpr (Num 1))
          ),
        Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (1, PktIn)), ArithExpr (Num 1)))
      )
  in
  Alcotest.(check Testable.hty)
    "chomp_ref1 Σ y:{ z:ε | |x.PktIn|=1 }. { z:ε | |y.PktIn|=1 } should be Σ y:{ z:ε | |x.PktIn|+1=1 }. { z:ε | |y.PktIn|=1 }"
    expected actual

let refty i =
  match i with
  | 1 -> Refinement ("z", hty_empty, e1)
  | 2 -> Refinement ("z", hty_empty, e2)
  | 3 -> Refinement ("z", hty_empty, e3)
  | 4 -> Refinement ("z", hty_empty, e4)
  | _ -> Refinement ("z", hty_empty, e1)

let refty' i =
  match i with
  | 1 -> Refinement ("z", hty_empty, e1')
  | 2 -> Refinement ("z", hty_empty, e2')
  | 3 -> Refinement ("z", hty_empty, e3')
  | 4 -> Refinement ("z", hty_empty, e4')
  | _ -> Refinement ("z", hty_empty, e1')

let test_chomp_sigma2 () =
  let ty = Sigma ("y", refty 4, refty 4) in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = Sigma ("y", refty' 4, refty 4) in
  Alcotest.(check Testable.hty)
    "chomp_ref1 Σ y:{ z:ε | e4 }. { z:ε | e4 } should be Σ y:{ z:ε | e4' }. { z:ε | e4 }"
    expected actual

let test_chomp_sigma3 () =
  let ty =
    Sigma
      ( "y",
        Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (1, PktIn)), ArithExpr (Num 1))),
        Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (2, PktIn)), ArithExpr (Num 1)))
      )
  in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected =
    Sigma
      ( "y",
        Refinement
          ( "z",
            hty_empty,
            Eq (ArithExpr (Plus (Length (1, PktIn), Num 1)), ArithExpr (Num 1))
          ),
        Refinement
          ( "z",
            hty_empty,
            Eq (ArithExpr (Plus (Length (2, PktIn), Num 1)), ArithExpr (Num 1))
          ) )
  in
  Alcotest.(check Testable.hty)
    "chomp_ref1 Σ y:{ z:ε | |x.PktIn|=1 }. { z:ε | |x.PktIn|=1 } should be Σ y:{ z:ε | |x.PktIn|+1=1 }. { z:ε | |x.PktIn|+1=1 }"
    expected actual

let test_chomp_choice () =
  let ty = Choice (Choice (refty 1, refty 2), Choice (refty 3, refty 4)) in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected =
    Choice (Choice (refty' 1, refty' 2), Choice (refty' 3, refty' 4))
  in
  Alcotest.(check Testable.hty)
    "chomp_ref1 { y:ε | e1 }+{ y:ε | e2 }+{ y:ε | e3 }+{ y:ε | e4 } should be { y:ε | e1' }+{ y:ε | e2' }+{ y:ε | e3' }+{ y:ε | e4' }"
    expected actual

let test_chomp_subst1 () =
  let ty =
    Substitution
      ( Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (1, PktIn)), ArithExpr (Num 1))),
        "y",
        hty_empty )
  in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = ty in
  Alcotest.(check Testable.hty)
    "chomp_ref1 { z:ε | |y.PktIn|=1 }[y→ε] should be { z:ε | |y.PktIn|=1 }[y→ε]"
    expected actual

let test_chomp_subst2 () =
  let ty =
    Substitution
      ( Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (2, PktIn)), ArithExpr (Num 1))),
        "y",
        hty_empty )
  in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected =
    Substitution
      ( Refinement
          ( "z",
            hty_empty,
            Eq (ArithExpr (Plus (Length (2, PktIn), Num 1)), ArithExpr (Num 1))
          ),
        "y",
        hty_empty )
  in
  Alcotest.(check Testable.hty)
    "chomp_ref1 { z:ε | |x.PktIn|=1 }[y→ε] should be { z:ε | |x.PktIn|+1=1 }[y→ε]"
    expected actual

let test_chomp_subst3 () =
  let ty =
    Substitution
      ( hty_empty,
        "y",
        Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (1, PktIn)), ArithExpr (Num 1)))
      )
  in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected =
    Substitution
      ( hty_empty,
        "y",
        Refinement
          ( "z",
            hty_empty,
            Eq (ArithExpr (Plus (Length (1, PktIn), Num 1)), ArithExpr (Num 1))
          ) )
  in
  Alcotest.(check Testable.hty)
    "chomp_ref1 ε[y→{ z:ε | |x.PktIn|=1 }] should be ε[y→{ z:ε | |x.PktIn|+1=1 }]"
    expected actual

let test_chomp_subst22 () =
  let ty = Substitution (refty 3, "y", refty 4) in
  let actual = Chomp.chomp_ref1 ty 0 0 in
  let expected = Substitution (refty 3, "y", refty' 4) in
  Alcotest.(check Testable.hty) "chomp_ref1 ø should be ø" expected actual

let test_set =
  [ test_case "ø" `Quick test_chomp_nothing;
    test_case "ε" `Quick test_chomp_empty;
    test_case "instance" `Quick test_chomp_inst;
    test_case "{ y:ε | e1 }" `Quick test_chomp_ref1;
    test_case "{ y:ε | e3 }" `Quick test_chomp_ref2;
    test_case "{ y:{ z:instance | |z.PktIn|=1 } | |x.PktIn|=1 }" `Quick
      test_chomp_ref3;
    test_case "{ y:{ z:instance | e2 } | e1 }" `Quick test_chomp_ref4;
    test_case "Σ y:{ z:ε | |x.PktIn|=1 }. { z:ε | |y.PktIn|=1 }" `Quick
      test_chomp_sigma1;
    test_case "Σ y:{ z:ε | e4 }. { z:ε | e4 }" `Quick test_chomp_sigma2;
    test_case "Σ y:{ z:ε | |x.PktIn|=1 }. { z:ε | |x.PktIn|=1 }" `Quick
      test_chomp_sigma3;
    test_case "{ y:ε | e1 }+{ y:ε | e2 }+{ y:ε | e3 }+{ y:ε | e4 }" `Quick
      test_chomp_choice;
    test_case "{ z:ε | |y.PktIn|=1 }[y→ε]" `Quick test_chomp_subst1;
    test_case "{ z:ε | |x.PktIn|=1 }[y→ε]" `Quick test_chomp_subst2;
    test_case "ε[y→{ z:ε | |x.PktIn|=1 }]" `Quick test_chomp_subst3;
    test_case "{ z:ε | e3 }[y→{ z:ε | e4 }]" `Quick test_chomp_subst22
  ]
