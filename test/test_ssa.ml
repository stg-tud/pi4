open Core_kernel
open Alcotest
open Pi4
open Syntax

let inst_a = Test_utils.mk_inst "A" [ ("a", 4); ("b", 4); ("c", 2) ]

let inst_a0 = Test_utils.mk_inst "A_0" [ ("a", 4); ("b", 4); ("c", 2) ]

let inst_a1 = Test_utils.mk_inst "A_1" [ ("a", 4); ("b", 4); ("c", 2) ]

let inst_b = Test_utils.mk_inst "B" [ ("b", 2) ]

let inst_b0 = Test_utils.mk_inst "B_0" [ ("b", 2) ]

let header_table = HeaderTable.populate [ inst_a; inst_b ]

let header_table_ssa = HeaderTable.populate [ inst_a0; inst_a1; inst_b0 ]

let init_versions = Ssa.InstanceMap.of_alist_exn [ (inst_a, 0); (inst_b, 0) ]

let compare cmd1 cmd2 = [%compare.equal: command] cmd1 cmd2

let test_cmd_to_ssa () =
  let cmd =
    Parsing.parse_command
      {|
        extract(A);
        if(A.a == pkt_in[0:4]) {
          A.a := pkt_in[4:8]
        }
      |}
      header_table
  in
  let ssa_cmd, _ =
    (* TODO: Use correct max versions *)
    Ssa.command_to_ssa header_table Ssa.InstanceMap.empty Ssa.InstanceMap.empty
      cmd
    |> Result.ok_or_failwith
  in
  let expected =
    Parsing.parse_command
      {|
      extract(A_0);
      if(A_0.a == pkt_in[0:4]) {
        (add(A_1);
        A_1.a := pkt_in[4:8]);
        A_1[4:10] := A_0[4:10]
      } else {
        skip;
        if(A_0.valid) {
          add(A_1);
          A_1[0:10] := A_0[0:10]
        }
      }
    |}
      header_table_ssa
  in
  Logs.debug (fun m -> m "@[<v>Expected: %a@]" Pi4.Pretty.pp_command expected);
  Logs.debug (fun m -> m "@[<v>Actual: %a@]" Pi4.Pretty.pp_command ssa_cmd);
  Alcotest.(check bool) "commands are equal" true (compare expected ssa_cmd)

let test_extract () =
  let cmd = Parsing.parse_command {|
      extract(A)
    |} header_table in
  let actual, _ =
    (* TODO: Use correct max versions *)
    Ssa.command_to_ssa header_table Ssa.InstanceMap.empty init_versions cmd
    |> Result.ok_or_failwith
  in
  let expected =
    Parsing.parse_command {|
        extract(A_1)
      |} header_table_ssa
  in
  Logs.debug (fun m -> m "@[<v>Expected: %a@]" Pi4.Pretty.pp_command expected);
  Logs.debug (fun m -> m "@[<v>Actual: %a@]" Pi4.Pretty.pp_command actual);
  Alcotest.(check bool) "commands are equal" true (compare expected actual)

let test_ascribe_extract () =
  let cmd =
    Parsing.parse_command
      {|
        extract(A) as (x:ε) → A
      |}
      header_table
  in
  let mv = Ssa.get_max_versions init_versions cmd in
  let actual, _ =
    Ssa.command_to_ssa header_table mv init_versions cmd
    |> Result.ok_or_failwith
  in
  let expected =
    Parsing.parse_command
      {|
        extract(A_1) as (x:ε) → {x':⊤|x'.A_1.valid ∧ ¬x'.B_0.valid}
      |}
      header_table_ssa
  in
  Logs.debug (fun m -> m "@[<v>Expected: %a@]" Pi4.Pretty.pp_command expected);
  Logs.debug (fun m -> m "@[<v>Actual: %a@]" Pi4.Pretty.pp_command actual);
  Alcotest.(check bool) "commands are equal" true (compare expected actual)

let test_input_ref () =
  let cmd = Parsing.parse_command {| A.a := 0x1 |} header_table in
  let hty_in = Parsing.parse_header_type "{y:A|y.A.a=0x0}" header_table [] in
  let hty_out =
    Parsing.parse_header_type "{y:A|y.A=x.A}" header_table
      [ ("x", Env.VarBind hty_in) ]
  in
  let ssa =
    Ssa.to_ssa header_table cmd ("x", hty_in) hty_out |> Result.ok_or_failwith
  in
  Logs.debug (fun m ->
      m "%a" (Pi4.Pretty.pp_header_type [ ("x", Env.NameBind) ]) ssa.output_type);
  Alcotest.(check bool) "commands are equal" true false

let test_determined_forwarding_ssa () =
  let program = Parsing.parse_program  {|
    header_type ipv4_t {
      dst: 1;
    }
    header_type standard_metadata_t {
      egress_spec: 1;
    }
    header ipv4 : ipv4_t
    header stdmeta : standard_metadata_t
    if(ipv4.valid) {
      if(!ipv4.dst == 0b1) {
        stdmeta.egress_spec := 0b1
      } else {
        if(stdmeta.valid) {
          stdmeta.egress_spec := 0b0
        } else {
          skip
        }
      }
    } else {
      if(stdmeta.valid) {
        stdmeta.egress_spec := stdmeta.egress_spec
      } else {
        skip
      }
    }
  |}     
  in
  (* let ssa_program = Parsing.parse_program {| add(stdmeta_1); stdmeta_1.egress_spec := 0b000000001|} in *)
  let header_table = HeaderTable.of_decls program.declarations in
  let hty_in = Parsing.parse_header_type {|{y:⊤|y.ipv4.valid && y.stdmeta.valid && y.stdmeta.egress_spec == 0b0}|} header_table [] in
  let hty_out = Parsing.parse_header_type {|{y:⊤|y.ipv4.valid && y.stdmeta.valid && (!y.stdmeta.egress_spec == 0b0)}|} header_table [] in
  let ssa = Ssa.to_ssa header_table program.command ("x", hty_in) hty_out |> Result.ok_or_failwith in
  Logs.debug (fun m ->
      m "%a" (Pi4.Pretty.pp_header_type [ ("x", Env.NameBind) ]) ssa.input_type);
  Logs.debug (fun m -> m "%a" Pi4.Pretty.pp_command ssa.command);  
  Logs.debug (fun m ->
      m "%a" (Pi4.Pretty.pp_header_type [ ("x", Env.NameBind) ]) ssa.output_type);
  Alcotest.(check bool) "commands are equal" true false
  
  
    
  
let test_set =
  [ test_case "SSA transformation is correct" `Quick test_cmd_to_ssa;
    test_case "Extract is transformed correctly" `Quick test_extract;
    test_case "Ascribed extract is transformed correctly" `Quick
      test_ascribe_extract;
    test_case "References to the input type are transformed correctly" `Quick test_input_ref;
    test_case "artifact determined forwarding SSA is correct" `Quick test_determined_forwarding_ssa;
  ]
