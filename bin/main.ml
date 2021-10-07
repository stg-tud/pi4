open Core
open Result.Let_syntax
open Petr4
open Common
open Pi4

let log_src = Logs.Src.create "main" ~doc:"Logs application-level events"

module Log = (val Logs.src_log log_src : Logs.LOG)

let colorize colors s = ANSITerminal.sprintf colors "%s" s

module Conf : Parse_config = struct
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

module P4Parse = Make_parse (Conf)

let to_result ~success result =
  match result with
  | Typechecker.TypecheckingResult.Success -> return success
  | Typechecker.TypecheckingResult.TypeError e -> Error e

let build_parser header_table p4prog =
  let%bind parser_cfg = Frontend.build_parser_cfg p4prog header_table in
  Frontend.build_parser parser_cfg

let find_roundtrip_annotation (Petr4.Types.Program decls) =
  Frontend.find_parser_annotations decls
  |> Option.bind ~f:(fun annotations ->
         match Frontend.find_type_annotation annotations with
         | Some (RoundtripAnnotation ty_annot) -> Some ty_annot
         | _ -> None)

let p4_check filename includes maxlen ingress verbose print_parser_ir print_ingress_ir
    print_roundtrip_ir =
  match P4Parse.parse_file includes filename verbose with
  | `Ok p4prog ->
    Prover.make_prover "z3";
    let module T = Typechecker.Make (Typechecker.CompleteChecker (struct
      let maxlen = maxlen
    end)) in
    (let%bind header_table = Frontend.build_header_table p4prog in
     if print_roundtrip_ir then
       let%bind parser_cmd = build_parser header_table p4prog in
       (* let%bind ingress_cmd = Frontend.control_to_command ingress p4prog header_table in *)
       let%bind deparser_cmd = Frontend.control_to_command "Deparser" p4prog header_table in
       let roundtrip_cmd = Syntax.Seq (
         deparser_cmd,
         Syntax.Seq (
           Syntax.Reset,
           parser_cmd)) in
       (* let prog_cmd = Syntax.Seq (
         parser_cmd,
         Syntax.Seq (ingress_cmd, roundtrip_cmd)
       ) in *)
       let%map roundtrip_ssa = Ssa.to_ssa header_table roundtrip_cmd ("x", Syntax.HeapType.Nothing) Syntax.HeapType.Nothing in
       (* let%map prog_ssa = Ssa.to_ssa header_table prog_cmd ("x", Syntax.HeapType.Nothing) Syntax.HeapType.Nothing in *)
       print_endline (Fmt.str "%a" Pretty.pp_command (roundtrip_ssa.command));
       (* print_endline "\nSSA full roundtripping program:"; *)
       (* print_endline (Fmt.str "%a" Pretty.pp_command prog_ssa.command); *)
       (* Ok (print_endline "Pi4: Typechecker skipped") *)
     else
       let%bind parser_result =
         if print_parser_ir then
           let%bind parser = build_parser header_table p4prog in
           let%map parser_ssa = Ssa.to_ssa header_table parser ("x", Syntax.HeapType.Nothing) Syntax.HeapType.Nothing in
           Fmt.str "%a\n" Pretty.pp_command (parser_ssa.command)
           (* let%bind parser_type =
             Frontend.annotated_parser_type p4prog header_table
           in *)
           (* let%bind parser_type = Result.of_option maybe_parser_type
              ~error:"Could not find a type annotation for the parser." in *)
           (* T.check_type parser parser_type header_table
           |> to_result ~success:"Parser was successfully typechecked." *)
         else
           Ok ""
       in
       print_string parser_result;

       let%map ingress_result =
         if print_ingress_ir then (
           let%bind ingress_cmd =
             Frontend.control_to_command ingress p4prog header_table
           in
           let%bind ingress_ssa = Ssa.to_ssa header_table ingress_cmd ("x", Syntax.HeapType.Nothing) Syntax.HeapType.Nothing in
           Ok (Fmt.str "%a\n" Pretty.pp_command (ingress_ssa.command))
           (* Logs.app (fun m ->
               m "Ingress command: %a" Pretty.pp_command ingress_cmd);
           let%bind ingress_type =
             Frontend.find_type_for_control ingress p4prog header_table
           in *)
           (* let%bind ingress_type = Result.of_option maybe_ingress_type
              ~error:"Could not find a type annotation for the ingress." in *)
           (* T.check_type ingress_cmd ingress_type header_table
           |> to_result ~success:"Ingress was successfully typechecked." *)
         ) else
           Ok ""
       in
       print_endline ingress_result)
    |> Result.ok_or_failwith
  | `Error (_, _) -> print_endline "Petr4 could not parse the input file."

let union r =
  match r with
  | Error s -> Printf.sprintf "[×] %s" s
  | Ok s -> Printf.sprintf "[✓] %s" s

let pi4_check program_filename type_filename maxlen ssa : unit =
  let program = Parsing.parse_program_from_file program_filename in
  Prover.make_prover "z3";
  let module Config = struct let maxlen = maxlen end in
  let module CC = Typechecker.CompleteChecker (Config) in
  let module T = Typechecker.Make (CC) in
  let module SSA_T = Typechecker.MakeSSAChecker (CC) in
  let header_table = Syntax.HeaderTable.of_decls program.declarations in
  let typ = Parsing.parse_type_from_file type_filename header_table in
  let check_type = if ssa then SSA_T.check_type else T.check_type in
  check_type program.command typ header_table
  |> to_result ~success:"passed typechecker" 
  |> union
  |> print_endline

                   
let command =
  Command.basic ~summary:"Check a P4 program with Pi4's typechecker"
    Command.Let_syntax.(
      let%map_open filename = anon ("filename" %: string)
      and includes =
        flag "-i" (listed string) ~doc:"<dir> add directory to include path for p4 programs [unused if -ir is set]"
      and verbose = flag "-v" no_arg ~doc:"verbose mode for parser [unused if -ir is set]"
      and maxlen =
        flag "-m"
          (optional_with_default 1500 int)
          ~doc:"int set maxlen (default 1500)"
      and ingress =
        flag "-ingress"
          (optional_with_default "Ingress" string)
          ~doc:"string name of ingress control (default 'Ingress') [unused if -ir is set]"
      and print_parser_ir =
        flag "-print-parser-ir" no_arg ~doc:"Enable checking of parser [unused if -ir is set]"
      and print_ingress_ir =
        flag "-print-ingress-ir" no_arg ~doc:"Enable checking of ingress for p4 programs [unused if -ir is set]"
      and print_roundtrip_ir =
        flag "-print-roundtrip-ir" no_arg
          ~doc:"Enable checking of parser-deparser compatibility for p4 frograms [unused if -ir is set]"
      and ir =
        flag "-ir" no_arg
          ~doc:"Assume the programs in the input files are written in the Π4 IR"
      and typ =
        flag "-typ" (optional string)
          ~doc:"pass types to check IR programs files [unused if -ir is not set]"
      and ssa =
        flag "-ssa" no_arg
          ~doc:"For SSA mode. Assumes the input files and types are written in SSA"
      in
      fun () ->
        if ir then
          begin match typ with
          | Some typfile -> pi4_check filename typfile maxlen ssa
          | None -> failwith "Error. expected type file for Π4 IR mode." 
          end
        else
          p4_check filename includes maxlen ingress verbose print_parser_ir
          print_ingress_ir print_roundtrip_ir)

let () =
  Fmt_tty.setup_std_outputs ();
  Logs.set_reporter @@ Logs_fmt.reporter ();
  (* Logs.set_level @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.ssa_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.prover_src @@ Some Logs.Debug;     *)
  (* Logs.Src.set_level Pi4.Logging.typechecker_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.frontend_src @@ Some Logs.Debug; *)
  Command.run ~version:"0.1" command
