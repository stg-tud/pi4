
let test_suite =
  [ 
    ("z3_encoding", Test_encoding.test_set);
    ("equivalence", Test_equiv.test_set);
    ("subtyping", Test_subtyping.test_set);
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
    ("substitution_base", Test_substitution.test_set);
    ("substitution_ext", Test_substitution_ext.test_set);
    ("ipv4opt", Test_ipv4opt.test_set);
	  ("vlan_decap", Test_vlan_decap.test_set);
  ]

let () =
  Format.pp_set_geometry Format.err_formatter ~max_indent:239 ~margin:240;
  Fmt_tty.setup_std_outputs ();
  Logs.set_reporter @@ Logs.format_reporter ();
  Logs.set_level ~all:true @@ Some Logs.Warning;
  (* Logs.Src.set_level Pi4.Logging.cache_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.substitution_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.prover_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.prover_profile_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.encoding_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.typechecker_src @@ Some Logs.Debug; *)
  (* Logs.Src.set_level Pi4.Logging.cache_src @@ Some Logs.Debug; *)

  Alcotest.run "Pi4" test_suite
