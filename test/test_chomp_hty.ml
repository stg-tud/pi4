open Core_kernel
open Alcotest
open Pi4
open Syntax
open Formula
open HeapType
open Expression

let foo_inst = Test_utils.mk_inst "foo" [ ("a", 4); ("b", 8); ("c", 16) ]

let len_PktIn i = Length (i, PktIn)

let len_PktIn' i = Plus (Length (i, PktIn), Num 1)

let slice_PktIn i l r = Slice (Packet (i, PktIn), l, r)

let slice_PktIn' i l r =
  match (l, r) with
  | _ when l < 0 || r < 1 -> Slice (Packet (i, PktIn), l, r)
  | 0, 1 -> Bv (Cons (B 0, Nil))
  | 0, _ -> Concat (Bv (Cons (B 0, Nil)), Slice (Packet (i, PktIn), 0, r - 1))
  | _ -> Slice (Packet (i, PktIn), l - 1, r - 1)

let conj x y = And (x, y)

let disj x y = Neg (conj (Neg x) (Neg y))

let impl x y = disj (Neg x) y

module T = Typechecker.CompleteChecker(struct let maxlen = 32 end)

let test_chomp_nothing () =
  let ty = Nothing in
  let actual = Chomp.chomp1 ty [] 0 in
  let expected = ty in
  Alcotest.(check Testable.hty) "chomp1 ø should be ø" expected actual

(* let test_chomp_empty () = let ty = Empty in let actual = chomp1 [] ty 0 in
   let expected = ty in Alcotest.(check Testable.hty) "chomp1 ε should be ε"
   expected actual

   let test_chomp_inst () = let ty = Instance foo_inst in let actual = chomp1 []
   ty 0 in let expected = ty in Alcotest.(check Testable.hty) "chomp1 foo should
   be foo" expected actual

   let test_chomp_sigma1 () = let ty1 = Refinement ("y", Empty, TmGt (len_PktIn
   0, Num 4)) in let ty = Sigma ("x", ty1, Empty) in let actual = chomp1 [] ty 0
   in let ty1_chomped = Refinement ("y", Empty, TmGt (len_PktIn' 0, Num 4)) in
   let ty1_zero = Refinement ("z", ty1, TmEq (len_PktIn 0, Num 0)) in let
   expected = Choice ( Sigma ("x", ty1_chomped, Empty), Sigma ("x", ty1_zero,
   Empty)) in Alcotest.(check Testable.hty) "chomp1 Σ x: { y:ε | |y.PktIn|>4 }.
   ε" expected actual

   let test_chomp_sigma2 () = let ty1 = Empty in let ty2 = Refinement ("y",
   Empty, TmGt (len_PktIn 0, len_PktIn 1)) in let ty = Sigma ("x", ty1, ty2) in
   let actual = chomp1 [] ty 0 in let ty1_chomped = Empty in let ty2_updated =
   Refinement ("y", Empty, TmGt (len_PktIn 0, len_PktIn' 1)) in let ty1_zero =
   Refinement ("z", ty1, TmEq (len_PktIn 0, Num 0)) in let ty2_chomped =
   Refinement ("y", Empty, TmGt (len_PktIn' 0, len_PktIn 1)) in let expected =
   Choice ( Sigma ("x", ty1_chomped, ty2_updated), Sigma ("x", ty1_zero,
   ty2_chomped)) in Alcotest.(check Testable.hty) "chomp1 Σ x: ε. { y:ε |
   |y.PktIn|>|x.PktIn| }" expected actual

   let test_chomp_sigma3 () = let ty1 = Refinement ("y", Empty, TmEq (Num 42,
   len_PktIn 0)) in let ty2 = Refinement ("y", Empty, TmGt (len_PktIn 1,
   len_PktIn 0)) in let ty = Sigma ("x", ty1, ty2) in let actual = chomp1 [] ty
   0 in let ty1_chomped = Refinement ("y", Empty, TmEq (Num 42, len_PktIn' 0))
   in let ty2_updated = Refinement ("y", Empty, TmGt (len_PktIn' 1, len_PktIn
   0)) in let ty1_zero = Refinement ("z", ty1, TmEq (len_PktIn 0, Num 0)) in let
   ty2_chomped = Refinement ("y", Empty, TmGt (len_PktIn 1, len_PktIn' 0)) in
   let expected = Choice ( Sigma ("x", ty1_chomped, ty2_updated), Sigma ("x",
   ty1_zero, ty2_chomped)) in Alcotest.(check Testable.hty) "chomp1 Σ x: { y:ε |
   42=|y.PktIn| }. { y:ε | |x.PktIn|>|y.PktIn| }" expected actual

   let test_chomp_choice () = let tyl1 = Refinement ("y", Empty, TmEq (len_PktIn
   0, Num 21)) in let tyl2 = Refinement ("y", Empty, TmGt (len_PktIn 1,
   len_PktIn 0)) in let tyl = Sigma ("x", tyl1, tyl2) in let tyr = Refinement
   ("x", Instance foo_inst, disj (TmEq (len_PktIn 0, Num 0)) (TmGt (len_PktIn 0,
   Num 0))) in let ty = Choice (tyl, tyr) in let actual = chomp1 [] ty 0 in let
   tyl1_chomped = Refinement ("y", Empty, TmEq (len_PktIn' 0, Num 21)) in let
   tyl2_updated = Refinement ("y", Empty, TmGt (len_PktIn' 1, len_PktIn 0)) in
   let tyl1_zero = Refinement ("z", tyl1, TmEq (len_PktIn 0, Num 0)) in let
   tyl2_chomped = Refinement ("y", Empty, TmGt (len_PktIn 1, len_PktIn' 0)) in
   let tyl' = Choice (Sigma ("x", tyl1_chomped, tyl2_updated), Sigma ("x",
   tyl1_zero, tyl2_chomped)) in let tyr' = Refinement ("x", Instance foo_inst,
   disj (TmEq (len_PktIn' 0, Num 0)) (TmGt (len_PktIn' 0, Num 0))) in let
   expected = Choice (tyl', tyr') in Alcotest.(check Testable.hty) "chomp1 Σ x:
   { y:ε | |y.PktIn|=21 }. { y:ε | |x.PktIn|>|y.PktIn| } + { y:ε | |y.PktIn|=0
   \\/ |y.PktIn|>0}" expected actual

   let test_chomp_refinement () = let e1 = TmEq (len_PktIn 0, Num 2) in let e2 =
   TmGt (Num 5, len_PktIn 0) in let e3 = And (TmEq (len_PktIn 2, len_PktIn 1))
   (TmGt (len_PktIn 0, Num 1)) in let ty = Refinement ("x", Refinement ("y",
   Refinement ("t", Empty, e3), e2), e1) in let actual = chomp1 [] ty 0 in let
   e1' = TmEq (len_PktIn' 0, Num 2) in let e2' = TmGt (Num 5, len_PktIn' 0) in
   let e3' = And (TmEq (len_PktIn 2, len_PktIn 1)) (TmGt (len_PktIn' 0, Num 1))
   in let expected = Refinement ("x", Refinement ("y", Refinement ("t", Empty,
   e3'), e2'), e1') in Alcotest.(check Testable.hty) "chomp1 { x:{ y:{ z:ε |
   |a.PktIn|=|b.PktIn| /\\ |z.PktIn|>1 } | 5>|y.PktIn| } | |x.PktIn|=2 }"
   expected actual

   let test_chomp_subst () = let ty1 = Refinement ("y", Empty, TmEq (len_PktIn
   0, len_PktIn 1)) in let ty2 = Refinement ("z", Empty, TmEq (len_PktIn 0, Num
   42)) in let ty = Substitution (ty1, "x", ty2) in let actual = chomp1 [] ty 0
   in let ty1' = Refinement ("y", Empty, TmEq (len_PktIn' 0, len_PktIn 1)) in
   let ty2' = Refinement ("z", Empty, TmEq (len_PktIn 0, Num 42)) in let
   expected = Substitution (ty1', "x", ty2') in Alcotest.(check Testable.hty) "{
   y:ε | |y.PktIn|=|x.PktIn| }[x -> { z:ε | |z.PktIn|=42 }]" expected actual

   let test_heapref_refinement () = let ty = Refinement ("x", Empty, TmEq (Bv
   (Cons (B 0, Nil)), Bv Nil)) in let actual = heap_ref1 ty 0 0 foo_inst 28 in
   let expected = Refinement ("x", Empty, TmEq (Slice (Instance (1, foo_inst),
   0, 1), Bv Nil)) in Alcotest.(check Testable.hty) "heap_ref1 { x:ε | <b0>=<>
   }" expected actual

   let test_heapref_sigma () = let ty = Sigma ("y", Refinement ("x", Empty, TmEq
   (Bv (Cons (B 0, Nil)), Bv Nil)), Refinement ("x", Empty, TmEq (Bv (Cons (B 0,
   Nil)), Bv Nil))) in let actual = heap_ref1 ty 0 0 foo_inst 28 in let expected
   = Sigma ("y", Refinement ("x", Empty, TmEq (Slice (Instance (1, foo_inst), 0,
   1), Bv Nil)), Refinement ("x", Empty, TmEq (Slice (Instance (2, foo_inst), 0,
   1), Bv Nil))) in Alcotest.(check Testable.hty) "Σ y:heap_ref1 { x:ε | <b0>=<>
   }. heap_ref1 { x:ε | <b0>=<> }" expected actual

   let test_heapref_subst () = let ty = Substitution (Refinement ("x", Empty,
   TmEq (Bv (Cons (B 0, Nil)), Bv Nil)), "y", Refinement ("x", Empty, TmEq (Bv
   (Cons (B 0, Nil)), Bv Nil))) in let actual = heap_ref1 ty 0 0 foo_inst 28 in
   let expected = Substitution (Refinement ("x", Empty, TmEq (Slice (Instance
   (2, foo_inst), 0, 1), Bv Nil)), "y", Refinement ("x", Empty, TmEq (Slice
   (Instance (1, foo_inst), 0, 1), Bv Nil))) in Alcotest.(check Testable.hty) "{
   x:ε | <b0>=<> }[y→{ x:ε | <b0>=<> }]" expected actual

   let test_chomp_heapref () = let ty = Refinement ("x", Empty, TmEq (Slice
   (Packet (0, PktIn), 0, 28), bv_s "0000000000000011111111111111")) in let
   actual = heap_ref1 (chomp1 [] ty 0) 0 0 foo_inst 28 in let expected =
   Refinement ("x", Empty, TmEq (Concat (Slice (Instance (1, foo_inst), 0, 1),
   Slice (Packet (0, PktIn), 0, 27)), bv_s "0000000000000011111111111111")) in
   Alcotest.(check Testable.hty) "{ x:ε | PktInt[0:28] =
   0000000000000011111111111111 }" expected actual

   let test_chomp_recursive () = let ty = Refinement ("x", Empty, TmEq (Slice
   (Packet (0, PktIn), 0, 28), bv_s "0000000000000011111111111111")) in let
   actual = chomp ty foo_inst in let t l = List.rev l |> List.fold ~init:(Bv
   Nil) ~f:(fun acc i -> Concat (Slice (Instance (1, foo_inst), i, i+1), acc))
   in let t' =
   [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27]
   |> t |> simplify_concat in let expected = Refinement ("x", Empty, TmEq (t',
   bv_s "0000000000000011111111111111")) in Alcotest.(check Testable.hty) "{ x:ε
   | PktInt[0:28] = 0000000000000011111111111111 }" expected actual

   (* chomp_equiv tests *) let _chomp1_equiv header_table ctx hty b0 =
   Pi4.Prover.make_prover "z3"; chomp1_equiv header_table ctx maxlen hty b0

   let empty_header_table = String.Map.empty

   let test_chomp_equiv_sigma1 () = let ty1 = Refinement ("y", Empty, TmGt
   (len_PktIn 0, Num 4)) in let ty = Sigma ("x", ty1, Empty) in let actual =
   _chomp1_equiv empty_header_table [] ty 0 in let ty1_chomped = Refinement
   ("y", Empty, TmGt (len_PktIn' 0, Num 4)) in let expected = Sigma ("x",
   ty1_chomped, Empty) in Alcotest.(check Testable.hty) "chomp1_equiv Σ x: { y:ε
   | |y.PktIn|>4 }. ε" expected actual

   let test_chomp_equiv_sigma2 () = let ty1 = Refinement ("y", Empty, TmEq
   (len_PktIn 0, Num 4)) in let ty = Sigma ("x", ty1, Empty) in let actual =
   _chomp1_equiv empty_header_table [] ty 0 in let ty1_chomped = Refinement
   ("y", Empty, TmEq (len_PktIn' 0, Num 4)) in let expected = Sigma ("x",
   ty1_chomped, Empty) in Alcotest.(check Testable.hty) "chomp1_equiv Σ x: { y:ε
   | |y.PktIn|=4 }. ε" expected actual

   let test_chomp_equiv_sigma3 () = let ref = Refinement ("z", Empty, TmEq
   (len_PktIn 0, Num 4)) in let ty = Sigma ("x", Sigma("y", ref, Empty), Empty)
   in let actual = _chomp1_equiv empty_header_table [] ty 0 in let ref_chomped =
   Refinement ("z", Empty, TmEq (len_PktIn' 0, Num 4)) in let expected = Sigma
   ("x", Sigma ("y", ref_chomped, Empty), Empty) in Alcotest.(check
   Testable.hty) "chomp1_equiv Σ x: { y:ε | |y.PktIn|=4 }. ε" expected actual

   let test_chomp_equiv_sigma4 () = let ty1 = Refinement ("y", Empty, TmEq
   (len_PktIn 0, Num 0)) in let ty2 = Refinement ("z", Empty, TmEq (len_PktIn 0,
   Num 4)) in let ty = Sigma ("x", ty1, ty2) in let actual = _chomp1_equiv
   empty_header_table [] ty 0 in let ty1_zero = Refinement ("w", ty1, TmEq
   (len_PktIn 0, Num 0)) in let ty2_chomped = Refinement ("z", Empty, TmEq
   (len_PktIn' 0, Num 4)) in let expected = Sigma ("x", ty1_zero, ty2_chomped)
   in Alcotest.(check Testable.hty) "chomp1_equiv Σ x: { y:ε | |y.PktIn|=0 }. {
   z:ε | |y.PktIn|=4 }" expected actual

   let test_chomp_equiv_sigma5 () = let ref = Refinement ("z", Empty, TmEq
   (len_PktIn 0, Num 4)) in let ty1 = Refinement ("y", Empty, TmEq (len_PktIn 0,
   Num 0)) in let ty = Sigma ("x", ty1, Sigma("y", ty1, ref)) in let actual =
   _chomp1_equiv empty_header_table [] ty 0 in let ref_chomped = Refinement
   ("z", Empty, TmEq (len_PktIn' 0, Num 4)) in let ty1_zero = Refinement ("w",
   ty1, TmEq (len_PktIn 0, Num 0)) in let expected = Sigma ("x", ty1_zero, Sigma
   ("y", ty1_zero, ref_chomped)) in Alcotest.(check Testable.hty) "foo" expected
   actual

   let test_chomp_equiv_sigma6 () = let ref4 = Refinement ("z", Empty, TmEq
   (len_PktIn 0, Num 4)) in let ref0 = Refinement ("y", Empty, TmEq (len_PktIn
   0, Num 0)) in let ty = Sigma ("x", ref0, Sigma("y", ref4, Empty)) in let
   actual = _chomp1_equiv empty_header_table [] ty 0 in let ref4_chomped =
   Refinement ("z", Empty, TmEq (len_PktIn' 0, Num 4)) in let ref0_zero =
   Refinement ("w", ref0, TmEq (len_PktIn 0, Num 0)) in let expected = Sigma
   ("x", ref0_zero, Sigma ("y", ref4_chomped, Empty)) in Alcotest.(check
   Testable.hty) "foo" expected actual *)

let test_set =
  [ test_case "ø" `Quick test_chomp_nothing
    (* test_case "ε" `Quick test_chomp_empty; test_case "instance" `Quick
       test_chomp_inst; test_case "Σ x: { y:ε | |y.PktIn|>4 }. ε" `Quick
       test_chomp_sigma1; test_case "Σ x: ε. { y:ε | |y.PktIn|>|x.PktIn| }"
       `Quick test_chomp_sigma2; test_case "Σ x: { y:ε | 42=|y.PktIn| }. { y:ε |
       |x.PktIn|>|y.PktIn| }" `Quick test_chomp_sigma3; test_case "Σ x: { y:ε |
       |y.PktIn|=21 }. { y:ε | |x.PktIn|>|y.PktIn| } + { y:ε | |y.PktIn|=0 \\/
       |y.PktIn|>0}" `Quick test_chomp_choice; test_case "{ x:{ y:{ z:ε |
       |a.PktIn|=|b.PktIn| /\\ |z.PktIn|>1 } | 5>|y.PktIn| } | |x.PktIn|=2 }"
       `Quick test_chomp_refinement; test_case "{ y:ε | |y.PktIn|=|x.PktIn| }[x
       -> { z:ε | |z.PktIn|=42 }]" `Quick test_chomp_subst; test_case "heap_ref1
       { x:ε | <b0>=<> }" `Quick test_heapref_refinement; test_case "heap_ref1 Σ
       y:heap_ref1 { x:ε | <b0>=<> }. heap_ref1 { x:ε | <b0>=<> }" `Quick
       test_heapref_sigma; test_case "heap_ref1 { x:ε | <b0>=<> }[y→{ x:ε |
       <b0>=<> }]" `Quick test_heapref_subst; test_case "one step: { x:ε |
       PktInt[0:28] = 0000000000000011111111111111 }" `Quick test_chomp_heapref;
       test_case "all steps: { x:ε | PktInt[0:28] = 0000000000000011111111111111
       }" `Quick test_chomp_recursive; test_case "equivalence reduction while
       chomping is correct: lhs >" `Quick test_chomp_equiv_sigma1; test_case
       "equivalence reduction while chomping is correct: lhs =" `Quick
       test_chomp_equiv_sigma2; test_case "equivalence reduction while chomping
       is correct: lhs nested" `Quick test_chomp_equiv_sigma3; test_case
       "equivalence reduction while chomping is correct: rhs" `Quick
       test_chomp_equiv_sigma4; test_case "equivalence reduction while chomping
       is correct: rhs nested" `Quick test_chomp_equiv_sigma5; test_case
       "equivalence reduction while chomping is correct: lhs&rhs nested" `Quick
       test_chomp_equiv_sigma6 *)
  ]
