open Alcotest

module TestConfig = struct
  let verbose = true
  let maxlen = 16
end

module Test = Test_utils.TestRunner (TestConfig)

let test_typecheck_skip_empty () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      skip 
    |}
  in
  Test.check_program Test.typecheck program "(x: ε) -> ε"

let test_typecheck_extract () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      extract(a)
    |}
  in
  let typ = "(x: {y:ε|y.pkt_in.length==4}) -> a" in
  Test.check_program Test.typecheck program typ

let test_typeof_extract_fails () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      extract(a)
    |}
  in
  let typ = "(x: {y:ε|y.pkt_in.length==2}) -> a" in
  Test.check_program Test.not_typecheck program typ

let test_typecheck_reset () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      reset
    |}
  in
  let typ =
    {|
    (x: {u:ε|u.pkt_out[0:4]==0b0101 && u.pkt_out.length==4 && u.pkt_in[0:4]==0b1111 && u.pkt_in.length==4}) -> 
        Σy:{v:ε|v.pkt_out.length==0 && v.pkt_in==x.pkt_out}.{w:ε|w.pkt_out.length==0 && w.pkt_in==x.pkt_in}
  |}
  in
  Test.check_program Test.typecheck program typ

let test_typecheck_if () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      if(a.valid) { extract(b) } else { skip }
    |}
  in
  let typ =
    {| (x: {y:a|y.pkt_in.length == 4}) -> {y: a.b|x.a.valid} + {y:a|!x.a.valid} |}
  in
  Test.check_program Test.typecheck program typ

let test_typecheck_if_fail () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      if(a.valid) { extract(b) } else { skip }
    |}
  in
  let typ = "(x: ε) -> Σy:a.b" in
  Test.check_program Test.not_typecheck program typ

let test_typeof_remit_invalid_instance () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      remit(a)
    |}
  in
  let typ = "(x: ε) -> ε" in
  Test.check_program
    (Test.error "Instance 'a' not included in header type")
    program typ

let test_typecheck_remit () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      remit(a)
    |}
  in
  let typ =
    {|
    (x: {y:a|y.pkt_in.length==8 && y.pkt_out.length == 0}) -> 
      Σy:{y:a|y.pkt_in.length==8 && y.pkt_out.length == 0}.{z:ε|z.pkt_in.length == 0 && z.pkt_out.length==4 && z.pkt_out[0:4]==y.a[0:4]}
  |}
  in
  Test.check_program Test.typecheck program typ

let test_typecheck_remit_value () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      remit(a)
    |}
  in
  let typ =
    {|
    (x: {y:a|y.pkt_out.length == 2 && y.a[0:2] == 0b10}) -> 
      {y:a|y.pkt_out.length == 6 && 
            y.pkt_out[2:4] == 0b10 && 
            y.pkt_out[0:2] == x.pkt_out[0:2]}
  |}
  in
  Test.check_program Test.typecheck program typ

let test_typecheck_emit_value () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      if(a.valid) {
        remit(a)
      }
    |}
  in
  let typ =
    {|
    (x: {y:a|y.pkt_out.length == 2 && y.a[0:2] == 0b10}) -> 
        {y:a|y.pkt_out.length == 6 && 
              y.pkt_out[2:4] == 0b10 && 
              y.pkt_out[0:2] == x.pkt_out[0:2]}
  |}
  in
  Test.check_program Test.typecheck program typ

let test_typecheck_seq_skip () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t

      skip; skip
    |}
  in
  let typ = "(x: a) -> a" in
  Test.check_program Test.typecheck program typ

let test_typecheck_seq_extract_extract () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      extract(a);extract(b)
    |}
  in
  let typ = "(x: {y:ε|y.pkt_in.length>5}) -> Σy:a.b" in
  Test.check_program Test.typecheck program typ

let test_typecheck_seq_extract3 () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header_type c_t {
        c: 1;
      }
      header a : a_t
      header b : b_t
      header c : c_t
      extract(a);
      extract(b);
      extract(c)
    |}
  in
  let typ =
    "(x: {y:ε|y.pkt_in.length>8}) -> {y:⊤|y.a.valid ∧ y.b.valid ∧ y.c.valid}"
  in
  Test.check_program Test.typecheck program typ

let test_typecheck_seq_extract_skip () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      extract(a);skip
    |}
  in
  let typ = "(x: {y:ε|y.pkt_in.length>3}) -> a" in
  Test.check_program Test.typecheck program typ

let test_typecheck_add () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      add(a)
    |}
  in
  let typ = "(x: ε) -> a" in
  Test.check_program Test.typecheck program typ

let test_typecheck_assign () =
  let program =
    {|
      header_type a_t {
        a: 4;
        aa : 2;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      a.a := 0x4
    |}
  in
  let typ = "(x: {y:a| y.a.a == 0x3}) -> { y:a | y.a.a == 0x4 }" in
  Test.check_program Test.typecheck program typ

let test_typecheck_assign2 () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      extract(a);
      if(a.a == 0x3) {
        a.a := 0x4
      }
    |}
  in
  let typ =
    "(x: { y:ε | y.pkt_in.length==8 }) -> { y:a | y.pkt_in.length == 4 }"
  in
  Test.check_program Test.typecheck program typ

let test_typecheck_add_assign () =
  let program =
    {|
      header_type vlan_t {
        prio: 3; 
        id: 1; 
        vlan: 12; 
        etherType: 16;
      }
      header vlan : vlan_t
      
      add(vlan);
      vlan.etherType := 0x0000
    |}
  in
  let typ = "(x: ε) -> { y:vlan | y.vlan.etherType == 0x0000 }" in
  Test.check_program Test.typecheck program typ

let test_typecheck_cond_add_assign () =
  let program =
    {|
      header_type vlan_t {
        prio: 3; 
        id: 1; 
        vlan: 12; 
        etherType: 16;
      }
      header vlan : vlan_t
      
      if(!vlan.valid) {
        add(vlan);
        vlan.etherType := 0x0000
      }
    |}
  in
  let typ = "(x: ε) -> { y:vlan | y.vlan.etherType == 0x0000 }" in
  Test.check_program Test.typecheck program typ

(* TODO: Fix test cases *)
(* let test_typeof_concat () = let open Term in let tm = Concat (Concat (bv_s
   "1010", Packet (0, PktIn)), Concat (bv_s "000", bv_s "1111")) in let tytm =
   Typechecker.typeof_tm tm in Alcotest.(check (result (Testable.ty []) string))
   "types should be equal" (Ok (BitVec MaxLen)) tytm *)

(* let test_typeof_exp_tmeq_concat_fail () = let open Term in let tm1 = Concat
   (bv_s "1111", bv_s "0000") in let tm2 = Concat (bv_s "00", Packet (0, PktIn))
   in let tmeq = TmEq (tm1, tm2) in let tye = Typechecker.typeof_exp tmeq in
   Alcotest.(check bool) "types should be equal" true (Result.is_error tye)

   let test_typeof_exp_tmeq_concat () = let open Term in let tm1 = Concat (bv_s
   "1111", bv_s "0000") in let tm2 = Concat (bv_s "00", bv_s "101010") in let
   tmeq = TmEq (tm1, tm2) in let tye = Typechecker.typeof_exp tmeq in
   Alcotest.(check (result (Testable.ty []) string)) "types should be equal" (Ok
   Bool) tye *)

let test_reset_reset () =
  let program =
    {|
      header_type a_t {
        f: 8;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      reset;reset
    |}
  in
  let typ =
    {|
    (x: Σy:a.{z:ε| z.pkt_in.length==0 && z.pkt_out.length==8 && z.pkt_out[0:8]==y.a[0:8]}) -> ε
  |}
  in
  Test.check_program Test.typecheck program typ

(* let prog = Seq (Reset, Reset) in let inst_h = Instance.{ name = "H"; fields =
   [ { name = "f"; typ = 8 } ] } in let ht = HeaderTable.populate [ inst_h ] in
   let hty1 = Parsing.header_type_of_string "\\sigma x:H.{y:\\empty |
   y.pkt_in.length==0 && y.pkt_out.length==8 && \ y.pkt_out[0:8]==x.H[0:8]}" ht
   [] in let hty2 = Parsing.header_type_of_string "\\empty" ht [] in
   Test.typecheck ht prog hty1 hty2 *)

let test_ascription () =
  let program =
    {|
      header_type a_t {
        a: 4;
      }
      header_type b_t {
        b: 2;
      }
      header a : a_t
      header b : b_t
      
      extract(a) as (x: {y:ε|y.pkt_in.length>7}) -> {y:a|y.pkt_in.length>3}
    |}
  in
  let typ = "(x: {x:ε|x.pkt_in.length==12}) -> a" in
  Test.check_program Test.typecheck program typ

let test_ascription_seq_extract () =
  let program =
    {|
      header_type g_t {
        f: 4;
      }
      header_type h_t {
        f: 2;
      }
      header g : g_t
      header h : h_t

      (extract(g) as (v:{z1:ε|z1.pkt_in.length == 8}) → {z2:g|z2.pkt_in.length + 4 == v.pkt_in.length});
      (extract(h) as (w:{z3:g|z3.pkt_in.length == 4}) → {z4:⊤|z4.g.valid ∧ z4.h.valid ∧ z4.pkt_in.length + 2 == w.pkt_in.length})
    |}
  in
  let typ =
    {| 
      (u:{z5:ε|z5.pkt_in.length == 8}) -> 
        {z6:⊤|z6.g.valid ∧ z6.h.valid ∧ z6.pkt_in.length + 2 == y.pkt_in.length}[y↦{w:g|w.pkt_in.length==4}]
    |}
  in
  Test.check_program Test.typecheck program typ

let test_ascription_seq_extract_step () =
  let program =
    {|
      header_type g_t {
        f: 4;
      }
      header_type h_t {
        f: 2;
      }
      header g : g_t
      header h : h_t

      skip;
      (extract(h) as (w:{z3:g|z3.pkt_in.length == 4}) → {z4:⊤|z4.g.valid ∧ z4.h.valid ∧ z4.pkt_in.length + 2 == w.pkt_in.length})
    |}
  in
  let typ =
    {| 
      (u:{z1:g|z1.pkt_in.length == 4}) -> 
        {z2:⊤|z2.g.valid ∧ z2.h.valid ∧ z2.pkt_in.length + 2 == y.pkt_in.length}[y↦{v:g|v.pkt_in.length==4}]
    |}
  in

  Test.check_program Test.typecheck program typ

let test_remove () =
  let program =
    {|
    header_type h_t {
      f: 4;
    }
    header h : h_t

    remove(h)
  |}
  in
  let typ = {| (x:h) → ε |} in
  Test.check_program Test.typecheck program typ

let test_set =
  [ test_case "'Skip' typechecks" `Quick test_typecheck_skip_empty;
    test_case "'Extract' typechecks" `Quick test_typecheck_extract;
    test_case "'Extract' fails if not enough bits in pkt_in" `Quick
      test_typeof_extract_fails;
    test_case "'Reset' typechecks" `Quick test_typecheck_reset;
    test_case "'If' typechecks" `Quick test_typecheck_if;
    test_case "'If fails to typecheck" `Quick test_typecheck_if_fail;
    test_case "'Remit' fails if instance is not valid" `Quick
      test_typeof_remit_invalid_instance;
    test_case "'Remit' typechecks" `Quick test_typecheck_remit;
    test_case "Remit writes instance to pkt_out" `Quick
      test_typecheck_remit_value;
    test_case "Emit writes instance to pkt_out" `Quick test_typecheck_emit_value;
    test_case "skip;skip typechecks" `Quick test_typecheck_seq_skip;
    test_case "'extract(A);extract(B)' typechecks" `Quick
      test_typecheck_seq_extract_extract;
    test_case "Extracting three instances typechecks" `Quick
      test_typecheck_seq_extract3;
    test_case "'extract(A);skip' typechecks" `Quick
      test_typecheck_seq_extract_skip;
    test_case "'add' typechecks" `Quick test_typecheck_add;
    test_case "Assignment typechecks" `Quick test_typecheck_assign;
    test_case "Assignment typechecks 2" `Quick test_typecheck_assign2;
    test_case "Assignment after adding instance typechecks" `Quick
      test_typecheck_add_assign;
    test_case "Conditional assignment after adding instance typechecks" `Quick
      test_typecheck_cond_add_assign;
    (* test_case "Computed type of concatenation is correct" `Quick
       test_typeof_concat; *)
    (* test_case "Term equality does not typecheck with bit vector types of
       different sizes" `Quick test_typeof_exp_tmeq_concat_fail; test_case "Term
       equality typechecks with bit vector types of same size" `Quick
       test_typeof_exp_tmeq_concat; *)
    test_case "reset;reset" `Quick test_reset_reset;
    test_case "Ascription succeeds" `Quick test_ascription;
    test_case "Ascription typechecks" `Quick test_ascription_seq_extract;
    test_case "Ascription typechecks after stepping" `Quick
      test_ascription_seq_extract_step;
    test_case "Remove single instance" `Quick test_remove
  ]
