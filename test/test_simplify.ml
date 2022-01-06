open Alcotest
open Core
open Result.Let_syntax
open Pi4
open Syntax
open Formula
open Expression
open HeapType

module TestConfig = struct
  let verbose = true

  let maxlen = 320
end

module Test = Test_utils.TestRunner (TestConfig)

let ether =
  Parsing.parse_instance_exn
    {| ether { dstAddr: 48; srcAddr: 48; etherType: 16; } |}

let ipv4 =
  Parsing.parse_instance_exn
    {|
      ipv4 {
        version: 4; 
        ihl: 4; 
        tos: 8; 
        len: 16; 
        id: 16; 
        flags: 3; 
        frag: 13; 
        ttl: 8; 
        proto: 8; 
        chksum: 16; 
        src: 32; 
        dst: 32;
      }
  |}

let vlan =
  Parsing.parse_instance_exn
    {|
      vlan {
            prio: 3; 
            id: 1; 
            vlan: 12; 
            etherType: 16;
          }
    |}

let test_simplify_plus () =
  let tm =
    Plus (Plus (Plus (Plus (Length (0, PktIn), Num 1), Num 1), Num 1), Num 16)
  in
  Logs.debug (fun m ->
      m "Term: %a" (Pretty.pp_expr [ ("x", NameBind) ]) (ArithExpr tm));
  let simplified = ArithExpr (Simplify.fold_plus tm) in
  let expected = ArithExpr (Plus (Length (0, PktIn), Num 19)) in
  Alcotest.(check Testable.term) "terms are equal" expected simplified

let test_simplified_type_equal () =
  let header_table = HeaderTable.populate [ ether; ipv4; vlan ] in
  let s =
    Parsing.parse_heap_type header_table []
      {|
        ({x:
          ⊤
          | ((¬(x.vlan.valid) ∧
              ¬(y.vlan.valid)) ∨
            ((x.vlan.valid ∧
              y.vlan.valid) ∧
            x.vlan[0:32] == y.vlan[0:32])) ∧
            (((¬(x.ipv4.valid) ∧
              ¬(y.ipv4.valid)) ∨
            ((x.ipv4.valid ∧
              y.ipv4.valid) ∧
            x.ipv4[0:160] == y.ipv4[0:160])) ∧
            (x.pkt_out == y.pkt_out ∧
            (x.ether[0:112]@x.pkt_in == y.pkt_in ∧
            ((x.pkt_in.length + 112) == y.pkt_in.length ∧
            (x.pkt_out.length == y.pkt_out.length ∧
            (x.ether.valid ∧
            x.ether[96:112] == 0x8100))))))})[y ↦ 
              {x:
                ⊤
                | true ∧
                  ¬(x.ether.valid) ∧
                  ¬(x.ipv4.valid) ∧
                  ¬(x.vlan.valid) ∧
                  x.pkt_out.length == 0 ∧
                  x.pkt_in.length == 304}]
      |}
  in
  let t =
    Parsing.parse_heap_type header_table []
      {|
        {x:
          ⊤
          | ¬(x.vlan.valid) ∧
            ¬(x.ipv4.valid) ∧
            (x.pkt_in.length + 112) == 304 ∧
            x.pkt_out.length == 0 ∧
            x.ether.valid ∧ x.ether[96:112] == 0x8100}
      |}
  in
  Test.is_equiv s t [] header_table

let includes (header_table : HeaderTable.t) (ctx : Env.context)
    (hty : HeapType.t) (inst : Instance.t) =
  let x = Env.pick_fresh_name ctx "x" in
  let refined = HeapType.Refinement (x, Top, IsValid (0, inst)) in
  Test.check_subtype hty refined ctx header_table

let included_instances header_table hty =
  match
    HeaderTable.to_list header_table
    |> List.map ~f:(fun inst -> (inst, includes header_table [] hty inst))
    |> Map.of_alist (module Instance)
  with
  | `Duplicate_key inst -> Error (Fmt.str "Key '%s' already exists" inst.name)
  | `Ok m -> Ok m

type inst_bool_map = bool Map.M(Instance).t [@@deriving sexp]

let rec propagate_substitution header_table hty =
  match hty with
  | Nothing -> return Nothing
  | Top -> return Top
  | Sigma (x, l, r) ->
    let%bind prop_l = propagate_substitution header_table l in
    let%map prop_r = propagate_substitution header_table r in
    Sigma (x, prop_l, prop_r)
  | Choice (l, r) ->
    let%bind prop_l = propagate_substitution header_table l in
    let%map prop_r = propagate_substitution header_table r in
    Choice (prop_l, prop_r)
  | Refinement (x, t, e) ->
    let%map prop_t = propagate_substitution header_table t in
    Refinement (x, prop_t, e)
  | Substitution (t, x, s) ->
    let%bind _valid_insts = included_instances header_table s in
    let%map subst = substitute_instances _valid_insts 1 t in
    (* print_endline (Sexplib.Sexp.to_string_hum (sexp_of_inst_bool_map
       _valid_insts)); *)
    Substitution (subst, x, s)

and substitute_instances inst_validity offset hty =
  match hty with
  | Nothing -> return Nothing
  | Top -> return Top
  | Sigma (x, l, r) ->
    let%bind subst_l = substitute_instances inst_validity offset l in
    let%map subst_r = substitute_instances inst_validity (offset + 1) r in
    Sigma (x, subst_l, subst_r)
  | Choice (l, r) ->
    let%bind subst_l = substitute_instances inst_validity offset l in
    let%map subst_r = substitute_instances inst_validity offset r in
    Choice (subst_l, subst_r)
  | Refinement (x, t, e) ->
    let%bind subst_t = substitute_instances inst_validity offset t in
    let%map subst_e = substitute_instances_form inst_validity offset e in
    Refinement (x, subst_t, subst_e)
  | Substitution (t, x, s) ->
    let%bind subst_t = substitute_instances inst_validity (offset + 1) t in
    let%map subst_s = substitute_instances inst_validity offset s in
    Substitution (subst_t, x, subst_s)

and substitute_instances_form inst_validity offset form =
  match form with
  | True -> return True
  | False -> return False
  | IsValid (x, inst) ->
    Fmt.pr "Offset: %d, index: %d" offset x;
    if x = offset then
      let%map is_valid =
        Map.find inst_validity inst
        |> Option.map ~f:return
        |> Option.value ~default:(Error "Could not look up instance validity.")
      in
      if is_valid then
        True
      else
        False
    else
      return (IsValid (x, inst))
  | Eq _ as e -> return e
  | Gt _ as e -> return e
  | Neg e ->
    let%map e_subst = substitute_instances_form inst_validity offset e in
    Neg e_subst
  | And (e1, e2) ->
    let%bind e1_subst = substitute_instances_form inst_validity offset e1 in
    let%map e2_subst = substitute_instances_form inst_validity offset e2 in
    And (e1_subst, e2_subst)
  | Or (e1, e2) ->
    let%bind e1_subst = substitute_instances_form inst_validity offset e1 in
    let%map e2_subst = substitute_instances_form inst_validity offset e2 in
    Or (e1_subst, e2_subst)
  | Implies (e1, e2) ->
    let%bind e1_subst = substitute_instances_form inst_validity offset e1 in
    let%map e2_subst = substitute_instances_form inst_validity offset e2 in
    Implies (e1_subst, e2_subst)

let test_subst_propagation () =
  let header_table = HeaderTable.populate [ ether; ipv4; vlan ] in
  let s =
    Parsing.parse_heap_type header_table []
      {|
        ({x:
          ⊤
          | ((¬(x.vlan.valid) ∧
              ¬(y.vlan.valid)) ∨
            ((x.vlan.valid ∧
              y.vlan.valid) ∧
            x.vlan[0:32] == y.vlan[0:32])) ∧
            (((¬(x.ipv4.valid) ∧
              ¬(y.ipv4.valid)) ∨
            ((x.ipv4.valid ∧
              y.ipv4.valid) ∧
            x.ipv4[0:160] == y.ipv4[0:160])) ∧
            (x.pkt_out == y.pkt_out ∧
            (x.ether[0:112]@x.pkt_in == y.pkt_in ∧
            ((x.pkt_in.length + 112) == y.pkt_in.length ∧
            (x.pkt_out.length == y.pkt_out.length ∧
            (x.ether.valid ∧
            x.ether[96:112] == 0x8100))))))})[y ↦ 
              {x:
                ⊤
                | true ∧
                  ¬(x.ether.valid) ∧
                  ¬(x.ipv4.valid) ∧
                  ¬(x.vlan.valid) ∧
                  x.pkt_out.length == 0 ∧
                  x.pkt_in.length == 304}]
      |}
  in
  let prop = propagate_substitution header_table s |> Result.ok_or_failwith in
  Fmt.pr "%a" (Pretty.pp_header_type []) prop;
  Test.is_equiv s prop [] header_table

let test_set =
  [ test_case "Plus is simplified correctly" `Quick test_simplify_plus;
    test_case "Simplified types are equal" `Quick test_simplified_type_equal;
    test_case "Substitution propagation" `Quick test_subst_propagation
  ]
