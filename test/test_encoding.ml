open Core_kernel
open Alcotest
open Pi4
open Syntax
open Z3

let maxlen = 32

let a_inst = Test_utils.mk_inst "a" [ ("f", 4); ("g", 8) ]

let header_table = HeaderTable.populate [ a_inst ]

let id_fst_compare (Smtlib.Id x, _) (Smtlib.Id y, _) : int = String.compare x y

let sort_consts consts = List.sort ~compare:id_fst_compare consts

let mk_id_sort id bvsize = (Smtlib.Id id, Smtlib.bv_sort bvsize)

let mk_bool_sort id = (Smtlib.Id id, Smtlib.bool_sort)

let id_sort_testable =
  Alcotest.testable (Fmt.list Pretty.pp_ident_sort) (List.equal Poly.equal)

module Enc = Encoding.FixedWidthBitvectorEncoding (struct
  let maxlen = 32
end)

let test_consts_nothing () =
  let consts =
    sort_consts (Enc.smt_consts Nothing "s" header_table)
  in
  let expected =
    [ mk_id_sort "s.a" 12;
      mk_bool_sort "s.a.valid";
      mk_id_sort "s.pkt_in" 32;
      mk_id_sort "s.pkt_in.length" 6;
      mk_id_sort "s.pkt_out" 32;
      mk_id_sort "s.pkt_out.length" 6
    ]
  in
  Logs.debug (fun m -> m "Consts: %a" (Fmt.list Pretty.pp_ident_sort) consts);
  Alcotest.(check id_sort_testable) "consts are equal" expected consts

let test_consts_top () =
  let consts = sort_consts (Enc.smt_consts Top "s" header_table) in
  let expected =
    [ mk_id_sort "s.a" 12;
      mk_bool_sort "s.a.valid";
      mk_id_sort "s.pkt_in" 32;
      mk_id_sort "s.pkt_in.length" 6;
      mk_id_sort "s.pkt_out" 32;
      mk_id_sort "s.pkt_out.length" 6
    ]
  in
  Logs.debug (fun m -> m "Consts: %a" (Fmt.list Pretty.pp_ident_sort) consts);
  Alcotest.(check id_sort_testable) "consts are equal" expected consts

let test_consts_refinement () =
  let hty = HeapType.Refinement ("x", Nothing, True) in
  let consts = sort_consts (Enc.smt_consts hty "s" header_table) in
  let expected =
    [ mk_id_sort "s.a" 12;
      mk_bool_sort "s.a.valid";
      mk_id_sort "s.pkt_in" 32;
      mk_id_sort "s.pkt_in.length" 6;
      mk_id_sort "s.pkt_out" 32;
      mk_id_sort "s.pkt_out.length" 6;
      mk_id_sort "x.a" 12;
      mk_bool_sort "x.a.valid";
      mk_id_sort "x.pkt_in" 32;
      mk_id_sort "x.pkt_in.length" 6;
      mk_id_sort "x.pkt_out" 32;
      mk_id_sort "x.pkt_out.length" 6
    ]
  in
  Logs.debug (fun m -> m "Consts: %a" (Fmt.list Pretty.pp_ident_sort) consts);
  Alcotest.(check id_sort_testable) "consts are equal" expected consts

let test_set =
  [ test_case "SMT consts generated for ∅ are correct" `Quick
      test_consts_nothing;
    test_case "SMT consts generated for ⊤ are correct" `Quick test_consts_top;
    test_case "SMT consts generated for refinement are correct" `Quick
      test_consts_refinement
  ]
