open Core
open Pi4
open Syntax

let header_table =
  HeaderTable.populate
    [ Parsing.parse_instance "A { a : 4 }";
      Parsing.parse_instance "B { b : 2 }"
    ]

let input_type =
  Parsing.parse_heap_type "{y:ε|y.pkt_in.length > 5}" header_table []

let context = [ ("x", Env.VarBind input_type) ]

let subtype =
  Parsing.parse_heap_type
    {|
      {z:⊤
        | 
          z.A.valid ∧ 
          z.B.valid ∧ 
          z.pkt_in.length + 4 > 5 ∧
          z.A@z.pkt_in = x.pkt_in ∧ 
          z.pkt_out = x.pkt_out ∧ 
          x.A.valid => z.A.valid ∧ z.A = x.A ∧
          x.B.valid => z.B.valid ∧ z.B = x.B }
  |}
    header_table context

let supertype = Parsing.parse_heap_type "Σy:A.B" header_table []

let run maxlen_start maxlen_end reps z3_path smt_tactic output_path verbose =
  Format.pp_set_geometry Format.err_formatter ~max_indent:239 ~margin:240;
  Logs.set_reporter @@ Logs_fmt.reporter ();
  Logs.set_level
  @@ Some
       (if verbose then
         Logs.Debug
       else
         Logs.App);

  Prover.make_prover (Option.value z3_path ~default:"z3");

  let tactic =
    Option.map smt_tactic ~f:(fun str -> Parsing.parse_smt_tactic str)
    |> Option.value ~default:Prover.default_tactic
  in

  let outfile =
    Option.value output_path
      ~default:
        (Printf.sprintf "extract_optimized_%s.csv"
           (Time.to_filename_string ~zone:Time.Zone.utc (Time.now ())))
  in

  Out_channel.with_file outfile ~f:(fun file ->
      fprintf file "MAXLEN;REP;RESULT;TIME\n";
      let reps = Option.value reps ~default:5 in
      assert (maxlen_end >= maxlen_start);
      for l = maxlen_start to maxlen_end do
        for i = 1 to reps do
          let t = Time_ns.now () in
          let module P =
          Prover.Make (Encoding.FixedWidthBitvectorEncoding (struct
            let maxlen = l
          end)) in
          let result =
            match (P.check_subtype_with_tactic subtype supertype context header_table tactic) with
            | Ok b -> b
            | Error (`EncodingError e) -> failwith e
            | Error (`VariableLookupError e) -> failwith e
          in
          let diff = Time_ns.abs_diff (Time_ns.now ()) t in
          Printf.fprintf file "%d;%d;%b;%f\n" l i result
            (Time_ns.Span.to_ms diff);
          Out_channel.flush file
        done
      done)

let command =
  Command.basic ~summary:"Run extract micro-benchmark"
    ~readme:(fun () -> "")
    Command.Let_syntax.(
      let%map_open maxlen_start = anon ("maxlen_start" %: int)
      and maxlen_end = anon ("maxlen_end" %: int)
      and output_path = flag "-o" (optional string) ~doc:"string Output path"
      and reps =
        flag "-r" (optional int) ~doc:"int Number of repetitions. Default = 5"
      and smt_tactic =
        flag "-t" (optional string) ~doc:"string SMT tactic used by the solver"
      and verbose = flag "-v" no_arg ~doc:"Enable debug output"
      and z3 = flag "-z3" (optional string) ~doc:"string Path to z3 binary" in
      fun () ->
        run maxlen_start maxlen_end reps z3 smt_tactic output_path verbose)

let () = Command.run ~version:"1.0" command
