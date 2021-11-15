open Alcotest
open Pi4
open Syntax
open Expression
open Testable

let foo_inst = Test_utils.mk_inst "foo" [ ("a", 4); ("b", 8); ("c", 16) ]

module T = Typechecker.CompleteChecker (struct
  let maxlen = 32
end)

(* num *)
let test_chomp_t1_num () =
  let t = ArithExpr (Num 1) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 1 should be 1" expected actual

(* length *)
let test_chomp_t1_length_out () =
  let t = ArithExpr (Length (0, PktOut)) in
  let actual = Chomp.chomp_t1 t 1 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 |y.PktOut| x should be |y.PktOut|" expected actual

let test_chomp_t1_length_out_binder () =
  let t = ArithExpr (Length (0, PktOut)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 |x.PktOut| x should be |x.PktOut|" expected actual

let test_chomp_t1_length_in_unchanged1 () =
  let t = ArithExpr (Length (0, PktIn)) in
  let actual = Chomp.chomp_t1 t 1 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 |x.PktIn| y should be |x.PktIn|" expected actual

let test_chomp_t1_length_in_unchanged2 () =
  let t = ArithExpr (Length (1, PktIn)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 |y.PktIn| x should be |x.PktIn|" expected actual

let test_chomp_t1_length_in_changed1 () =
  let t = ArithExpr (Length (0, PktIn)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = ArithExpr (Plus (Length (0, PktIn), Num 1)) in
  Alcotest.(check term)
    "chomp_t1 |x.PktIn| x should be |x.PktIn|+1" expected actual

let test_chomp_t1_length_in_changed2 () =
  let t = ArithExpr (Length (1, PktIn)) in
  let actual = Chomp.chomp_t1 t 1 0 in
  let expected = ArithExpr (Plus (Length (1, PktIn), Num 1)) in
  Alcotest.(check term)
    "chomp_t1 |y.PktIn| y should be |y.PktIn|+1" expected actual

(* plus *)
let test_chomp_t1_plus_unchanged () =
  let t = ArithExpr (Plus (Num 4, Num 7)) in
  let actual = Chomp.chomp_t1 t 1 0 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 4+7 should be 4+7" expected actual

let test_chomp_t1_plus_inductive_left () =
  let t = ArithExpr (Plus (Length (1, PktIn), Num 7)) in
  let actual = Chomp.chomp_t1 t 1 0 in
  let expected = ArithExpr (Plus (Plus (Length (1, PktIn), Num 1), Num 7)) in
  Alcotest.(check term)
    "chomp_t1 |y.PktIn|+7 y should be |y.PktIn|+1+7" expected actual

let test_chomp_t1_plus_inductive_right () =
  let t = ArithExpr (Plus (Length (1, PktIn), Length (0, PktIn))) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected =
    ArithExpr (Plus (Length (1, PktIn), Plus (Length (0, PktIn), Num 1)))
  in
  Alcotest.(check term)
    "chomp_t1 |y.PktIn|+|x.PktIn| x should be |y.PktIn|+|x.PktIn|+1" expected
    actual

let test_chomp_t1_plus_inductive_both () =
  let t = ArithExpr (Plus (Length (0, PktIn), Length (0, PktIn))) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected =
    ArithExpr
      (Plus (Plus (Length (0, PktIn), Num 1), Plus (Length (0, PktIn), Num 1)))
  in
  Alcotest.(check term)
    "chomp_t1 |x.PktIn|+|x.PktIn| x should be |x.PktIn|+1+|x.PktIn|+1" expected
    actual

(* bv *)
let test_chomp_t1_bv_nil () =
  let t = BvExpr (Bv Nil) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 <> should be <>" expected actual

let test_chomp_t1_bv_cons1 () =
  let t = BvExpr (Bv (Cons (Zero, Nil))) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 0::<> should be 0::<>" expected actual

let test_chomp_t1_bv_cons2 () =
  let t = BvExpr (Bv (Cons (Zero, Cons (One, Cons (B 0, Cons (B 7, Nil)))))) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 0::1::B0::B7<> should be 0::1::B0::B7::<>" expected actual

(* concat *)
let test_chomp_t1_concat_nil () =
  let t = BvExpr (Concat (Bv Nil, Bv Nil)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 <>@<> should be <>@<>" expected actual

let test_chomp_t1_concat_inductive_left () =
  let t =
    BvExpr (Concat (Slice (Packet (0, PktIn), 11, 21), Bv (Cons (One, Nil))))
  in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected =
    BvExpr (Concat (Slice (Packet (0, PktIn), 10, 20), Bv (Cons (One, Nil))))
  in
  Alcotest.(check term)
    "chomp_t1 x.PktIn[11:21]@<> should be x.PktIn[10:20]@<>" expected actual

let test_chomp_t1_concat_inductive_right () =
  let t =
    BvExpr (Concat (Bv (Cons (One, Nil)), Slice (Packet (0, PktIn), 0, 21)))
  in
  let actual = Chomp.chomp_t1 t 0 3 in
  let expected =
    BvExpr
      (Concat
         ( Bv (Cons (One, Nil)),
           Concat (Bv (Cons (B 3, Nil)), Slice (Packet (0, PktIn), 0, 20)) ))
  in
  Alcotest.(check term)
    "chomp_t1 1::<>@x.PktIn[0:21] x B3 should be 1::<>@B3::<>@x.PktIn[0:20]"
    expected actual

(* slice *)
let test_chomp_t1_slice_inst1 () =
  let t = BvExpr (Slice (Instance (0, foo_inst), 0, 10)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 x.inst[0:10] x should be x.inst[0:10]" expected actual

let test_chomp_t1_slice_inst2 () =
  let t = BvExpr (Slice (Instance (1, foo_inst), 123, 456)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 y.inst[123:456] x should be y.inst[123:456]" expected actual

let test_chomp_t1_slice_out1 () =
  let t = BvExpr (Slice (Packet (0, PktOut), 123, 456)) in
  let actual = Chomp.chomp_t1 t 1 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 x.PktOut[123:456] y should be x.PktOut[123:456]" expected actual

let test_chomp_t1_slice_out2 () =
  let t = BvExpr (Slice (Packet (0, PktOut), 123, 456)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 x.PktOut[123:456] x should be x.PktOut[123:456]" expected actual

let test_chomp_t1_slice_in_unchanged () =
  let t = BvExpr (Slice (Packet (0, PktIn), 123, 456)) in
  let actual = Chomp.chomp_t1 t 1 0 in
  let expected = t in
  Alcotest.(check term)
    "chomp_t1 x.PktIn[123:456] y should be x.PktIn[123:456]" expected actual

let test_chomp_t1_slice_in_shift_indices () =
  let t = BvExpr (Slice (Packet (0, PktIn), 123, 456)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = BvExpr (Slice (Packet (0, PktIn), 122, 455)) in
  Alcotest.(check term)
    "chomp_t1 x.PktIn[123:456] x should be x.PktIn[122:455]" expected actual

let test_chomp_t1_slice_in_r_is_1 () =
  let t = BvExpr (Slice (Packet (0, PktIn), 0, 1)) in
  let actual = Chomp.chomp_t1 t 0 0 in
  let expected = BvExpr (Bv (Cons (B 0, Nil))) in
  Alcotest.(check term)
    "chomp_t1 x.PktIn[0:1] x B0 should be B0 :: <>" expected actual

let test_chomp_t1_slice_in_r_is_not_1 () =
  let t = BvExpr (Slice (Packet (0, PktIn), 0, 21)) in
  let actual = Chomp.chomp_t1 t 0 7 in
  let expected =
    BvExpr (Concat (Bv (Cons (B 7, Nil)), Slice (Packet (0, PktIn), 0, 20)))
  in
  Alcotest.(check term)
    "chomp_t1 x.PktIn[0:21] x B7 should be B7 :: <> @ x.PktIn[0:20]" expected
    actual

(* packet *)
let test_chomp_t1_packet_out1 () =
  let t = BvExpr (Packet (1, PktOut)) in
  let actual = Chomp.chomp_t1 t 0 7 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 y.PktOut x should be y.PktOut" expected actual

let test_chomp_t1_packet_out2 () =
  let t = BvExpr (Packet (0, PktOut)) in
  let actual = Chomp.chomp_t1 t 0 7 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 x.PktOut x should be x.PktOut" expected actual

let test_chomp_t1_packet_in1 () =
  let t = BvExpr (Packet (1, PktIn)) in
  let actual = Chomp.chomp_t1 t 0 7 in
  let expected = t in
  Alcotest.(check term) "chomp_t1 y.PktIn x should be y.PktIn" expected actual

let test_chomp_t1_packet_in2 () =
  let t = BvExpr (Packet (0, PktIn)) in
  let actual = Chomp.chomp_t1 t 0 2 in
  let expected = BvExpr (Concat (Bv (Cons (B 2, Nil)), Packet (0, PktIn))) in
  Alcotest.(check term)
    "chomp_t1 x.PktIn x B2 should be B2::<>@x.PktIn" expected actual

let test_heapref_nil () =
  let t = BvExpr (Bv Nil) in
  let actual = Chomp.heap_tref1 t 0 0 foo_inst 0 in
  let expected = t in
  Alcotest.(check term) "heap_tref1 <>" expected actual

let test_heapref_zero () =
  let t = BvExpr (Bv (Cons (Zero, Nil))) in
  let actual = Chomp.heap_tref1 t 0 0 foo_inst 0 in
  let expected = t in
  Alcotest.(check term) "heap_tref1 <0>" expected actual

let test_heapref_concrete_bv () =
  let t = BvExpr (bv_s "0101101000001111") in
  let actual = Chomp.heap_tref1 t 0 0 foo_inst 0 in
  let expected = t in
  Alcotest.(check term) "heap_tref1 <0101101000001111>" expected actual

let test_heapref_b0 () =
  let t = BvExpr (Bv (Cons (B 0, Nil))) in
  let x = 1 in
  let actual = Chomp.heap_tref1 t 0 x foo_inst 28 in
  let expected = BvExpr (Slice (Instance (x, foo_inst), 0, 1)) in
  Alcotest.(check term) "heap_tref1 <b0>" expected actual

let test_heapref_b1 () =
  let t = BvExpr (Bv (Cons (B 1, Nil))) in
  let x = 1 in
  let actual = Chomp.heap_tref1 t 0 x foo_inst 28 in
  let expected = t in
  Alcotest.(check term) "heap_tref1 <b1>" expected actual

let test_heapref_b1b0 () =
  let t = BvExpr (bv_l [ B 1; B 0 ]) in
  let x = 1 in
  let actual = Chomp.heap_tref1 t 0 x foo_inst 28 in
  let expected =
    BvExpr (Concat (Bv (Cons (B 1, Nil)), Slice (Instance (x, foo_inst), 0, 1)))
  in
  Alcotest.(check term) "heap_tref1 <b1, b0>" expected actual

let test_heapref_concretebv_b0 () =
  let t = BvExpr (bv_l [ Zero; Zero; One; One; B 0 ]) in
  let x = 1 in
  let actual = Chomp.heap_tref1 t 0 x foo_inst 28 in
  let expected =
    BvExpr
      (Concat
         (bv_l [ Zero; Zero; One; One ], Slice (Instance (x, foo_inst), 0, 1)))
  in
  Alcotest.(check term) "heap_tref1 <0011 b0>" expected actual

let test_heapref_b0b1 () =
  let t = BvExpr (bv_l [ B 0; B 1 ]) in
  let x = 1 in
  let actual = Chomp.heap_tref1 t 0 x foo_inst 28 in
  let expected =
    BvExpr (Concat (Slice (Instance (x, foo_inst), 0, 1), Bv (Cons (B 1, Nil))))
  in
  Alcotest.(check term) "heap_tref1 <b0 b1>" expected actual

let test_heapref_b0_concretebv () =
  let t = BvExpr (bv_l [ B 0; Zero; One; Zero; One ]) in
  let x = 1 in
  let actual = Chomp.heap_tref1 t 0 x foo_inst 28 in
  let expected =
    BvExpr
      (Concat
         (Slice (Instance (x, foo_inst), 0, 1), bv_l [ Zero; One; Zero; One ]))
  in
  Alcotest.(check term) "heap_tref1 <b0 0101>" expected actual

let test_heapref_b0b0 () =
  let t = BvExpr (bv_l [ B 0; B 0 ]) in
  let x = 1 in
  let actual = Chomp.heap_tref1 t 0 x foo_inst 28 in
  let expected =
    BvExpr
      (Concat
         ( Slice (Instance (x, foo_inst), 0, 1),
           Slice (Instance (x, foo_inst), 0, 1) ))
  in
  Alcotest.(check term) "heap_tref1 <b0 b0>" expected actual

(* TODO: move to syntax function tests *)
let test_reduce_concat1 () =
  let t =
    BvExpr
      (Concat
         ( Bv (Cons (Zero, Nil)),
           Concat
             ( Bv (Cons (Zero, Nil)),
               Concat
                 ( Bv (Cons (One, Nil)),
                   Concat
                     (Bv (Cons (One, Nil)), Slice (Instance (0, foo_inst), 0, 1))
                 ) ) ))
  in
  let actual = Pi4.Simplify.simplify_expr t in
  (* let expected = Concat (bv_s "00", Concat (Bv (Cons (One, Nil)), Concat (Bv
     (Cons (One, Nil)), Slice (Instance (0, foo_inst), 0, 1)))) in *)
  let expected =
    BvExpr (Concat (bv_s "0011", Slice (Instance (0, foo_inst), 0, 1)))
  in
  Alcotest.(check term) "reduce concat" expected actual

let test_reduce_concat2 () =
  let t =
    BvExpr
      (Concat
         ( Slice (Instance (0, foo_inst), 0, 1),
           Concat
             ( Slice (Instance (0, foo_inst), 1, 2),
               Concat
                 ( Slice (Instance (0, foo_inst), 2, 3),
                   Concat
                     ( Slice (Instance (0, foo_inst), 3, 4),
                       Slice (Instance (0, foo_inst), 4, 5) ) ) ) ))
  in
  let actual = Pi4.Simplify.simplify_expr t in
  (* let expected = Concat (bv_s "00", Concat (Bv (Cons (One, Nil)), Concat (Bv
     (Cons (One, Nil)), Slice (Instance (0, foo_inst), 0, 1)))) in *)
  let expected = BvExpr (Slice (Instance (0, foo_inst), 0, 5)) in
  Alcotest.(check term) "reduce concat" expected actual

let test_set =
  [ test_case "chomp_t1 '1'" `Quick test_chomp_t1_num;
    test_case "chomp_t1 |y.PktOut| x" `Quick test_chomp_t1_length_out;
    test_case "chomp_t1 |x.PktOut| x" `Quick test_chomp_t1_length_out_binder;
    test_case "chomp_t1 |x.PktIn| y" `Quick test_chomp_t1_length_in_unchanged1;
    test_case "chomp_t1 |y.PktIn| x" `Quick test_chomp_t1_length_in_unchanged2;
    test_case "chomp_t1 |x.PktIn| x" `Quick test_chomp_t1_length_in_changed1;
    test_case "chomp_t1 |y.PktIn| y" `Quick test_chomp_t1_length_in_changed2;
    test_case "chomp_t1 4+7" `Quick test_chomp_t1_plus_unchanged;
    test_case "chomp_t1 |y.PktIn|+7 y" `Quick test_chomp_t1_plus_inductive_left;
    test_case "chomp_t1 |y.PktIn|+7 y" `Quick test_chomp_t1_plus_inductive_right;
    test_case "chomp_t1 |x.PktIn|+|x.PktIn| x" `Quick
      test_chomp_t1_plus_inductive_both;
    test_case "chomp_t1 <>" `Quick test_chomp_t1_bv_nil;
    test_case "chomp_t1 0::<>" `Quick test_chomp_t1_bv_cons1;
    test_case "chomp_t1 0::1::B0::B7<>" `Quick test_chomp_t1_bv_cons2;
    test_case "chomp_t1 <>@<>" `Quick test_chomp_t1_concat_nil;
    test_case "chomp_t1 x.PktIn[11:21]@<>" `Quick
      test_chomp_t1_concat_inductive_left;
    test_case "chomp_t1 1::<>@x.PktIn[0:21]" `Quick
      test_chomp_t1_concat_inductive_right;
    test_case "chomp_t1 x.inst[0:10] x" `Quick test_chomp_t1_slice_inst1;
    test_case "chomp_t1 y.inst[123:456] x" `Quick test_chomp_t1_slice_inst2;
    test_case "chomp_t1 y.PktOut[123:456] x" `Quick test_chomp_t1_slice_out1;
    test_case "chomp_t1 x.PktOut[123:456] x" `Quick test_chomp_t1_slice_out2;
    test_case "chomp_t1 y.PktIn[123:456] x" `Quick
      test_chomp_t1_slice_in_unchanged;
    test_case "chomp_t1 x.PktIn[123:456] x" `Quick
      test_chomp_t1_slice_in_shift_indices;
    test_case "chomp_t1 x.PktIn[0:1] x" `Quick test_chomp_t1_slice_in_r_is_1;
    test_case "chomp_t1 x.PktIn[0:21] x" `Quick
      test_chomp_t1_slice_in_r_is_not_1;
    test_case "chomp_t1 y.PktOut x" `Quick test_chomp_t1_packet_out1;
    test_case "chomp_t1 x.PktOut x" `Quick test_chomp_t1_packet_out2;
    test_case "chomp_t1 y.PktIn x" `Quick test_chomp_t1_packet_in1;
    test_case "chomp_t1 x.PktIn x" `Quick test_chomp_t1_packet_in2;
    test_case "heap_tref1 <>" `Quick test_heapref_nil;
    test_case "heap_tref1 <0>" `Quick test_heapref_zero;
    test_case "heap_tref1 <0101101000001111>" `Quick test_heapref_concrete_bv;
    test_case "heap_tref1 <b0>" `Quick test_heapref_b0;
    test_case "heap_tref1 <b1>" `Quick test_heapref_b1;
    test_case "heap_tref1 <b1 b0>" `Quick test_heapref_b1b0;
    test_case "heap_tref1 <0011 b0>" `Quick test_heapref_concretebv_b0;
    test_case "heap_tref1 <b0 b1>" `Quick test_heapref_b0b1;
    test_case "heap_tref1 <b0 0101>" `Quick test_heapref_b0_concretebv;
    test_case "heap_tref1 <b0 b0>" `Quick test_heapref_b0b0;
    test_case "reduce <0>@(<0>@(<1>@(<1>@(x.foo[0:1]))))" `Quick
      test_reduce_concat1;
    test_case
      "reduce x.foo[0:1]@(x.foo[1:2]@(x.foo[2:3]@(x.foo[3:4]@(x.foo[4:5]))))"
      `Quick test_reduce_concat2
  ]
