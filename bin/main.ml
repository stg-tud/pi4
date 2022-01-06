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

let union r =
  match r with
  | Error s -> Printf.sprintf "[×] %s" s
  | Ok s -> Printf.sprintf "[✓] %s" s

let pi4_check program_filename type_filename maxlen : unit =
  let program = Parsing.parse_program_from_file program_filename in
  Prover.make_prover "z3";
  let module Config = struct
    let maxlen = maxlen
  end in
  let module C = Typechecker.SemanticChecker (Config) in
  let module T = Typechecker.Make (C) in
  let header_table = Syntax.HeaderTable.of_decls program.declarations in
  let typ = Parsing.parse_type_from_file type_filename header_table in
  T.check_type program.command typ header_table
  |> to_result ~success:"passed typechecker"
  |> union |> print_endline

let p4_check filename includes _maxlen verbose =
  match P4Parse.parse_file includes filename verbose with
  | `Ok p4prog -> (
    let result =
      let%map header_table = Frontend.build_header_table p4prog in
      Log.debug (fun m ->
          m "Header table: %a\n" Pretty.pp_header_table header_table);
      let annotations = Frontend.collect_annotations header_table p4prog in
      Log.debug (fun m ->
          m "Annotations: %s"
            (Sexplib.Sexp.to_string_hum
               (List.sexp_of_t Syntax.Annotation.sexp_of_t annotations)))
    in
    match result with Ok _ -> () | _ -> print_endline "error")
  | `Error (_, _) -> print_endline "Petr4 could not parse the input file."

let command =
  Command.basic ~summary:"Check a P4 program with Pi4's typechecker"
    Command.Let_syntax.(
      let%map_open filename = anon ("filename" %: string)
      and verbose =
        flag "-v" no_arg ~doc:"verbose mode for parser [unused if -ir is set]"
      and includes =
        flag "-i" (listed string)
          ~doc:
            "<dir> add directory to include path for P4 programs [unused if \
             -ir is set]"
      and maxlen =
        flag "-m"
          (optional_with_default 1500 int)
          ~doc:"int set maxlen (default 1500)"
      and ir =
        flag "-ir" no_arg
          ~doc:"Assume the programs in the input files are written in the Π4 IR"
      and typ =
        flag "-typ" (optional string)
          ~doc:
            "pass types to check IR programs files [unused if -ir is not set]"
      in
      fun () ->
        Fmt_tty.setup_std_outputs ();
        Logs.set_reporter @@ Logs_fmt.reporter ();
        if verbose then Logs.set_level @@ Some Logs.Debug
          (* Logs.Src.set_level Pi4.Logging.ssa_src @@ Some Logs.Debug; *)
          (* Logs.Src.set_level Pi4.Logging.prover_src @@ Some Logs.Debug;     *)
          (* Logs.Src.set_level Pi4.Logging.typechecker_src @@ Some Logs.Debug; *)
          (* Logs.Src.set_level Pi4.Logging.frontend_src @@ Some Logs.Debug; *)
        else ();
        if ir then
          match typ with
          | Some typfile -> pi4_check filename typfile maxlen
          | None -> failwith "Error. expected type file for Π4 IR mode."
        else p4_check filename includes maxlen verbose)

let () = Command.run ~version:"0.1" command
