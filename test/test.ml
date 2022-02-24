(* open Landmark *)

let test_suite =
  [ 
    ("z3_encoding", Test_encoding.test_set);
    ("equivalence", Test_equiv.test_set);
    ("subtyping", Test_subtyping.test_set);
    ("term_chomping", Test_chomp_term.test_set);
    ("expr_chomping", Test_chomp_exp.test_set);
    ("ref_chomping", Test_chomp_ref.test_set);
    ("type_chomping", Test_chomp_hty.test_set);
    ("type_checking", Test_typecheck.test_set);
    ("syntax", Test_syntax.test_set);
    ("roundtrip", Test_artifact_roundtrip.test_set);
    ("mutual_exclusion", Test_artifact_mutual_exclusion.test_set);
    ("header_validity", Test_header_validity.test_set);
    ("determined_forwarding", Test_artifact_determined_forwarding.test_set);
    ("header_dependency", Test_artifact_header_dependency.test_set);
    ("ipv4_ttl", Test_artifact_ipv4_ttl.test_set);
    ("ipv4_options", Test_artifact_ipv4_opt.test_set);
    ("parser", Test_parser.test_set);
    ("simplification", Test_simplify.test_set);
    ("cisco_example", Test_cisco.test_set);
    ("composition", Test_composition.test_set);
    ("examples", Test_examples.test_set);
    ("substitution", Test_substitution.test_set);
    ("split_concat", Test_split_concat.test_set);
  ]

let () =
  Format.pp_set_geometry Format.err_formatter ~max_indent:239 ~margin:240;
  Fmt_tty.setup_std_outputs ();
  Logs.set_reporter @@ Logs.format_reporter ();
  Logs.set_level ~all:true @@ Some Logs.Debug;
  Logs.Src.set_level Pi4.Logging.typechecker_src @@ Some Logs.Debug;


  (* start_profiling (); *)
  Alcotest.run "Pi4" test_suite
