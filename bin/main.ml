open Core
open Result.Let_syntax
open Petr4
open Pi4
module P4Info = Info
module Info = P4Info
module Env = Prog.Env

let print pp = Format.printf "%a@." Pp.to_fmt pp

module type Parse_config = sig
  val red : string -> string
  val green : string -> string
  val preprocess : string list -> string -> string
end

module Make_parse (Conf : Parse_config) = struct
  let parse_file include_dirs p4_file verbose =
    let () = Petr4.Lexer.reset () in
    let () = Petr4.Lexer.set_filename p4_file in
    let p4_string = Conf.preprocess include_dirs p4_file in
    let lexbuf = Lexing.from_string p4_string in
    try
      let prog = Petr4.Parser.p4program Petr4.Lexer.lexer lexbuf in
      if verbose then (
        Format.eprintf "[%s] %s@\n%!" (Conf.green "Passed") p4_file;
        prog |> Petr4.Pretty.format_program |> print;
        Format.print_string "@\n%!";
        Format.printf "----------@\n";
        Format.printf "%s@\n%!"
          (prog |> Petr4.Types.program_to_yojson |> Yojson.Safe.pretty_to_string));
      `Ok prog
    with err ->
      if verbose then Format.eprintf "[%s] %s@\n%!" (Conf.red "Failed") p4_file;
      `Error (Petr4.Lexer.info lexbuf, err)
end

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
    let in_chan = Core_unix.open_process_in cmd in
    let str = Core.In_channel.input_all in_chan in
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
    Prover.make_prover "z3";
    let module C = Typechecker.SemanticChecker (struct
      let maxlen = _maxlen
    end) in
    let module T = Typechecker.Make (C) in
    match p4prog with
    | Petr4.Types.Program decls -> (
      let result =
        let%bind type_decls = Frontend.get_type_declarations decls in
        let%bind header_table = Frontend.build_header_table type_decls p4prog in
        Log.debug (fun m ->
            m "Header table: %a\n" Pretty.pp_header_table header_table);
        let%bind constants = Frontend.collect_constants type_decls p4prog in
        let%map instantiated_controls =
          Frontend.instantiated_controls header_table constants decls
        in
        let annotations = Frontend.collect_annotations header_table p4prog in
        List.iter annotations ~f:(fun annot ->
            match annot with
            | TypeAnnotation (body, typ) -> (
              let result =
                let%map prog =
                  Frontend.annotation_to_command header_table constants
                    instantiated_controls decls annot
                in
                Log.debug (fun m -> m "Program: %a" Pretty.pp_command prog);
                T.check_type prog typ header_table
              in
              match result with
              | Ok tc_result ->
                tc_result
                |> to_result
                     ~success:
                       (Fmt.str
                          "@[%a passed the typechecker with type\n @[%a@]@]\n"
                          Pretty.pp_annotation_body body (Pretty.pp_pi_type [])
                          typ)
                |> union |> print_endline
              | Error (`ConversionError e) ->
                Fmt.pr "@[A conversion error\n                 occurred: %s@]" e
              | Error (`FieldAccessError e) ->
                Fmt.pr "@[A field access error\n                 occurred: %s@]"
                  e
              | Error (`FrontendError e) ->
                Fmt.pr "@[A frontend error occurred: %s@]" e
              | Error (`InvalidArgumentError e) ->
                Fmt.pr
                  "@[A not implemented\n                 error occurred: %s@]" e
              | Error (`NotImplementedError e) ->
                Fmt.pr
                  "@[A not implemented\n                 error occurred: %s@]" e
              | Error (`LookupError e) ->
                Fmt.pr "@[A lookup error occurred:\n                 %s@]" e
              | Error _ -> print_endline "An error occurred."))
      in
      match result with
      | Ok _ -> ()
      | Error (`FrontendError e) -> print_endline e
      | Error (`ConversionError e) ->
        Fmt.pr "@[A conversion error occurred:\n         %s@]" e
      | Error (`NotImplementedError e) ->
        Fmt.pr "@[A not implemented error occurred: %s@]" e
      | Error (`HeaderTypeNotDeclaredError e) ->
        Fmt.pr "@[A header type not declared error occurred:\n         %s@]" e
      | Error (`TypeDeclarationNotFoundError e) ->
        Fmt.pr "@[An error occurred:\n      %s@]" e
      | Error (`LookupError e) ->
        Fmt.pr "@[A lookup error occurred:\n      %s@]" e
      | Error (`FieldAccessError e) ->
        Fmt.pr "@[A field access error occurred: %s@]" e
      | Error (`InvalidArgumentError e) ->
        Fmt.pr "@[An invalid argument error occurred: %s@]" e))
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
        if verbose then (
          Logs.set_level @@ Some Logs.Debug;
          (* Logs.Src.set_level Pi4.Logging.prover_src @@ Some Logs.Debug; *)
          Logs.Src.set_level Pi4.Logging.typechecker_src @@ Some Logs.Debug;
          Logs.Src.set_level Pi4.Logging.substitution_src @@ Some Logs.Info;
          Logs.Src.set_level Pi4.Logging.prover_profile_src @@ Some Logs.Info;
          Logs.Src.set_level Pi4.Logging.prover_src @@ Some Logs.Info;
          Logs.Src.set_level Pi4.Logging.frontend_src @@ Some Logs.Info)
        else Logs.set_level @@ Some Logs.Info;
        if ir then
          match typ with
          | Some typfile -> pi4_check filename typfile maxlen
          | None -> failwith "Error. expected type file for Π4 IR mode."
        else p4_check filename includes maxlen verbose)

let () = Command_unix.run ~version:"0.1" command
