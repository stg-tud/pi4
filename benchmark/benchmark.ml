open Core
open Result.Let_syntax
open Pi4

let to_result ~success result =
  match result with
  | Typechecker.TypecheckingResult.Success -> return success
  | Typechecker.TypecheckingResult.TypeError e -> Error e

let union r =
  match r with
  | Error _ -> 
    Printf.sprintf "false"
  | Ok _ -> 
    Printf.sprintf "true"

let time f =
  let time = Time_ns.now () in
  let res = f () in
  let time_diff = Time_ns.abs_diff (Time_ns.now ()) time in
  Printf.printf "%f\n" (Time_ns.Span.to_ms time_diff);
  res

let typecheck program_file type_file dyn_max lenc inclc folds : unit =
  let program = Parsing.parse_program_from_file program_file in
  Prover.make_prover "z3";
  let module Config = struct
    let maxlen = ref(12000)
  end in
  let module C = Typechecker.SemanticChecker (Config) in
  let module T = Typechecker.Make (C) in
  let header_table = Syntax.HeaderTable.of_decls program.declarations in
  let typ = Parsing.parse_type_from_file type_file header_table in
  time(
    fun () ->
      T.check_type 
        program.command 
        typ
        header_table
        ~dynamic_maxlen: dyn_max
        ~len_cache: lenc
        ~incl_cache: inclc
        ~smpl_subs: folds
  )
  |> to_result ~success:"passed typechecker"
  |> union 
  |> print_endline

let command = 
  Command.basic ~summary:"Minimal Pi4 cli for benchmarking"
    Command.Let_syntax.( 
      let%map_open filename = anon ("filename" %: string)
      and typ = 
        flag "-t" (required string)
            ~doc:"Type file"
      and dynamic_maxlen = 
        flag "-d" no_arg ~doc:"Enable dynamic maxlen"
      and len_cache = 
        flag "-n" no_arg ~doc:"Enable length  cache"
      and incl_cache =
        flag "-i" no_arg ~doc:"Enable includes cache"
      and fold_subs = 
        flag "-f" no_arg ~doc:"Enable substitution folding"
      and cache_log = 
        flag "-c" no_arg ~doc:"Enable logging of cache metrics to stdout"
      in
      fun () -> 
        if cache_log then
          begin
          Fmt_tty.setup_std_outputs ();
          Logs.set_reporter @@ Logs_fmt.reporter ();
          Logs.set_level @@ Some Logs.Error;
          Logs.Src.set_level Pi4.Logging.cache_src @@ Some Logs.Debug;
          end
        else ();
        typecheck filename typ dynamic_maxlen len_cache incl_cache fold_subs
    )

let () = Command.run ~version:"0.1" command