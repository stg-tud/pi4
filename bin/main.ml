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

let pi4_check program_filename type_filename maxlen disable_cache disable_inlining : unit =
  let program = Parsing.parse_program_from_file program_filename in
  Prover.make_prover "z3";
  let module Config = struct
    let maxlen = ref(maxlen)
  end in
  let module C = Typechecker.SemanticChecker (Config) in
  let module T = Typechecker.Make (C) in
  let header_table = Syntax.HeaderTable.of_decls program.declarations in
  let typ = Parsing.parse_type_from_file type_filename header_table in
  T.check_type program.command typ header_table ~incl_cache:(not disable_cache)
    ~len_cache:(not disable_cache) ~smpl_subs:(not disable_inlining)
  |> to_result ~success:"passed typechecker"
  |> union |> print_endline

let p4_check filename includes _maxlen verbose disable_cache disable_inlining =
  match P4Parse.parse_file includes filename verbose with
  | `Ok p4prog -> (
    Prover.make_prover "z3";
    let module C = Typechecker.SemanticChecker (struct
      let maxlen = ref(_maxlen)
    end) in
    let module T = Typechecker.Make (C) in
    match p4prog with
    | Petr4.Types.Program decls -> (
      let result =
        let%map header_table = Frontend.build_header_table p4prog in
        Log.debug (fun m ->
            m "Header table: %a\n" Pretty.pp_header_table header_table);
        let annotations = Frontend.collect_annotations header_table p4prog in
        List.iter annotations ~f:(fun annot ->
            match annot with
            | TypeAnnotation (body, typ) -> (
              let result =
                let%map prog =
                  Frontend.annotation_to_command header_table decls annot
                in
                Log.debug (fun m -> m "Program: %a" Pretty.pp_command prog);
                T.check_type prog typ header_table ~incl_cache:(not disable_cache)
                ~len_cache:(not disable_cache) ~smpl_subs:(not disable_inlining)
              in
              match result with
              | Ok tc_result ->
                tc_result
                |> to_result
                     ~success:
                       (Fmt.str "@[%a passed the typechecker with type\n @[%a@]@]\n"
                          Pretty.pp_annotation_body body (Pretty.pp_pi_type [])
                          typ)
                |> union |> print_endline
              | Error `FrontendError e -> print_endline e
              | Error _ -> print_endline "An error occurred."))
      in
      match result with
      | Ok _ -> ()
      | Error (`FrontendError e) -> print_endline e
      | _ -> print_endline "An error occurred"))
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
      and disable_cache =
        flag "-disable-cache" no_arg
          ~doc:
            "pass types to check IR programs files [unused if -ir is not set]"
      and disable_inlining =
        flag "-disable-inlining" no_arg
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
        else Logs.set_level @@ Some Logs.Info;
        if ir then
          match typ with
          | Some typfile -> pi4_check filename typfile maxlen disable_cache disable_inlining
          | None -> failwith "Error. expected type file for Π4 IR mode."
        else p4_check filename includes maxlen verbose disable_cache disable_inlining)

let () = Command.run ~version:"0.1" command
