open Core
open Result.Let_syntax
open Pi4

let colorize colors s = ANSITerminal.sprintf colors "%s" s

module Conf : Petr4.Common.Parse_config = struct
  let red s = colorize [ ANSITerminal.red ] s

  let green s = colorize [ ANSITerminal.green ] s

  let preprocess include_dirs p4file =
    let cmd =
      String.concat ~sep:" "
        ([ "cc" ]
        @ List.map include_dirs ~f:(Printf.sprintf "-I%s")
        @ [ "-undef"; "-nostdinc"; "-E"; "-x"; "c"; p4file ])
    in
    Logs.debug (fun m -> m "%s" cmd);
    let in_chan = Unix.open_process_in cmd in
    let str = In_channel.input_all in_chan in
    (* let _ = Unix.close_process_in in_chan in *)
    str
end

module P4Parse = Petr4.Common.Make_parse (Conf)

module T = Typechecker.Make (Typechecker.CompleteChecker (struct
  let maxlen = 320
end))

let run benchmark z3 verbose =
  Format.pp_set_geometry Format.err_formatter ~max_indent:239 ~margin:240;
  Logs.set_reporter @@ Logs_fmt.reporter ();
  Logs.set_level ~all:true
  @@ Some
       (if verbose then
         Logs.Debug
       else
         Logs.Info);
  (* Logs.Src.set_level Pi4.Logging.typechecker_src @@ Some Logs.Debug; *)
  match
    P4Parse.parse_file [ "./p4/includes" ] "./p4/roundtripping.p4" verbose
  with
  | `Ok p4prog ->
    Prover.make_prover (Option.value z3 ~default:"z3");
    (let%bind header_table = Frontend.build_header_table p4prog in
     let%bind parser_cfg = Frontend.build_parser_cfg p4prog header_table in
     let%bind parser = Frontend.build_parser parser_cfg in
     let%bind ingress =
       Frontend.control_to_command "MyIngress" p4prog header_table
     in

     let%map cmd, ty =
       match benchmark with
       | "parser" ->
         let ty_parser =
           Parsing.parse_type
             {|
           (x:{y:ε|y.pkt_in.length=320}) -> (ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))
         |}
             header_table
         in
         return (parser, ty_parser)
       | "ingress" ->
         let ty_ingress =
           Parsing.parse_type
             {| 
                (x:(ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))) ->
                ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} + {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid}) 
             |}
             header_table
         in
         return (ingress, ty_ingress)
       | "complete" ->
         let ty_complete =
           Parsing.parse_type
             {| 
                (x:{y:ε|y.pkt_in.length=320}) ->
                ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} +
                {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid}) 
             |}
             header_table
         in
         return (Syntax.Seq (parser, ingress), ty_complete)
       | "ascribe" ->
         let hty_in =
           Parsing.parse_heap_type "{y:ε|y.pkt_in.length=320}" header_table
             []
         in
         let hty_parser =
           Parsing.parse_heap_type
             "(ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))"
             header_table
             [ ("x", Env.VarBind hty_in) ]
         in
         (* let hty_out =
           Parsing.parse_header_type
             {|
            ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} +
            {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid})
          |}
             header_table []
         in *)
         (* let ty_complete =
           Parsing.parse_type
             {| 
                 (x:{y:ε|y.pkt_in.length=320}) ->
                 ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} +
                 {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid}) 
              |}
             header_table
         in *)
         let parser_ascribed =
           Syntax.Ascription (parser, "x", hty_in, hty_parser)
         in
         (* let ingress_ascribed =
           Syntax.Ascription (ingress, "x", hty_parser, hty_out)
         in *)
         let ty_parser =
          Parsing.parse_type
            {|
          (x:{y:ε|y.pkt_in.length=320}) -> (ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))
        |}
            header_table
        in
         (* return (Syntax.Seq (parser_ascribed, ingress_ascribed), ty_complete) *)
         return (parser_ascribed, ty_parser)
       | _ ->
         Error
           "Invalid benchmark. Possible options include 'parser', 'ingress', 'complete', 'ascribe'"
     in
     match T.check_type cmd ty header_table with
     | Typechecker.TypecheckingResult.Success ->
       print_endline "Successfully typechecked"
     | Typechecker.TypecheckingResult.TypeError e ->
       print_endline "Program did not typecheck";
       print_endline e)
    |> Result.ok_or_failwith
  | `Error (_, _) -> print_endline "Petr4 could not parse the input file."

let command =
  Command.basic ~summary:"Run extract micro-benchmark"
    ~readme:(fun () -> "")
    Command.Let_syntax.(
      let%map_open benchmark = anon ("benchmark" %: string)
      and verbose = flag "-v" no_arg ~doc:"Enable debug output"
      and z3 = flag "-z3" (optional string) ~doc:"string Path to z3 binary" in
      fun () -> run benchmark z3 verbose)

let () = Command.run ~version:"1.0" command
