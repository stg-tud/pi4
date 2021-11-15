open Core
open Pi4
open Syntax

exception InvalidArgument of string

let repetitions = 5

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

let supertype_opt =
  Parsing.parse_heap_type "{y:⊤|y.A.valid ∧ y.B.valid}" header_table []

let run (benchmark : string) (maxlen_intv : string) (outfile : string)
    (smt_tactic : string option) (verbose : bool) (z3_path : string option) =
  Format.pp_set_geometry Format.err_formatter ~max_indent:239 ~margin:240;
  Logs.set_reporter @@ Logs_fmt.reporter ();
  Logs.set_level
  @@ Some
       ( if verbose then
         Logs.Debug
       else
         Logs.App );

  let maxlen_start, maxlen_end =
    try
      let bounds =
        List.map ~f:int_of_string (String.split maxlen_intv ~on:':')
      in
      (List.hd_exn bounds, List.nth_exn bounds 1)
    with _ ->
      raise
        (InvalidArgument
           (Printf.sprintf
              "Invalid value '%s' for maxlen, expected 'start:end'."
              maxlen_intv))
  in
  assert (maxlen_end >= maxlen_start);

  Prover.make_prover (Option.value z3_path ~default:"z3");

  let tactic =
    Option.map ~f:Parsing.parse_smt_tactic smt_tactic
    |> Option.value ~default:Z3.Smtlib.UFBV
  in

  let hty =
    match benchmark with
    | "subtype" -> subtype
    | "supertype" -> supertype
    | "supertype_opt" -> supertype_opt
    | b ->
      raise (InvalidArgument (Printf.sprintf "Unsupported benchmark '%s'" b))
  in

  Out_channel.with_file outfile ~f:(fun file ->
      fprintf file "MAXLEN;REP;RESULT;TIME\n";
      for maxlen = maxlen_start to maxlen_end do
        for i = 1 to repetitions do
          let t = Time_ns.now () in

          let module P =
          Prover.Make (Encoding.FixedWidthBitvectorEncoding (struct
            let maxlen = maxlen
          end)) in
          let result =
            match P.has_model_with_tactic hty context header_table tactic with
            | Ok b -> b
            | Error (`EncodingError e) -> failwith e
            | Error (`VariableLookupError e) -> failwith e
          in
          let diff = Time_ns.abs_diff (Time_ns.now ()) t in
          Printf.fprintf file "%d;%d;%b;%f\n" maxlen i result
            (Time_ns.Span.to_ms diff);
          Out_channel.flush file
        done
      done)

let command =
  Command.basic
    ~summary:
      "Measure time until solver finds model for type [header_type] for different [maxlen] values (start:end)"
    ~readme:(fun () -> "")
    Command.Let_syntax.(
      let%map_open outfile =
        flag "-o" (required string) ~doc:"string Output file"
      and smt_tactic =
        flag "-t" (optional string)
          ~doc:"string SMT tactic used by the solver (default UFBV)"
      and verbose = flag "-v" no_arg ~doc:"Enable debug output"
      and z3 = flag "-z3" (optional string) ~doc:"string Path to z3 binary"
      and benchmark = anon ("benchmark" %: string)
      and maxlen = anon ("maxlen" %: string) in
      fun () -> run benchmark maxlen outfile smt_tactic verbose z3)

let () = Command.run ~version:"1.0" command
