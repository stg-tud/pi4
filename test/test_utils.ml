open Core_kernel
open Pi4
open Syntax
open Pretty

module type TestConfig = sig
  val maxlen : int

  val verbose : bool
end

module TestRunner (Config : TestConfig) : sig
  val check_subtype :
    HeapType.t -> HeapType.t -> Env.context -> HeaderTable.t -> bool

  val is_subtype :
    HeapType.t -> HeapType.t -> Env.context -> HeaderTable.t -> unit

  val not_subtype :
    HeapType.t -> HeapType.t -> Env.context -> HeaderTable.t -> unit

  val typecheck : HeaderTable.t -> Command.t -> pi_type -> unit

  val not_typecheck : HeaderTable.t -> Command.t -> pi_type -> unit

  val error : HeaderTable.t -> Command.t -> pi_type -> string -> unit

  val is_equiv :
    HeapType.t -> HeapType.t -> Env.context -> HeaderTable.t -> unit

  val not_equiv :
    HeapType.t -> HeapType.t -> Env.context -> HeaderTable.t -> unit
end = struct
  let init_prover = Prover.make_prover "z3"

  module M = struct
    let maxlen = Config.maxlen
  end

  module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (M))
  module T = Typechecker.Make (Typechecker.SemanticChecker (M))

  let check_subtype hty_s hty_t ctx ht =
    init_prover;
    match P.check_subtype hty_s hty_t ctx ht with
    | Ok b -> b
    | Error (`EncodingError e) -> failwith e
    | Error (`VariableLookupError e) -> failwith e

  let test_subtype hty_s hty_t ctx header_table assert_msg expected =
    Alcotest.(check bool)
      assert_msg expected
      (check_subtype hty_s hty_t ctx header_table)

  let is_subtype hty_s hty_t ctx ht =
    if Config.verbose then
      Fmt.pr "@[<v>Checking subtyping relation:@ %a <: %a@]@."
        (Pretty.pp_header_type ctx)
        hty_s
        (Pretty.pp_header_type ctx)
        hty_t
    else
      ();
    test_subtype hty_s hty_t ctx ht
      (Fmt.str "%a <: %a"
         (Pretty.pp_header_type ctx)
         hty_s
         (Pretty.pp_header_type ctx)
         hty_t)
      true

  let not_subtype hty_s hty_t ctx ht =
    if Config.verbose then
      Fmt.pr "@[<v>Checking subtyping relation:@ %a not <: %a@]@."
        (Pretty.pp_header_type ctx)
        hty_s
        (Pretty.pp_header_type ctx)
        hty_t
    else
      ();
    test_subtype hty_s hty_t ctx ht
      (Fmt.str "%a not <: %a"
         (Pretty.pp_header_type ctx)
         hty_s
         (Pretty.pp_header_type ctx)
         hty_t)
      false

  let typecheck ht cmd ty =
    init_prover;
    Alcotest.(check Testable.typechecker_result)
      (Fmt.str "%a" (pp_pi_type []) ty)
      Typechecker.TypecheckingResult.Success (T.check_type cmd ty ht)

  let not_typecheck ht cmd ty =
    init_prover;
    Alcotest.(check bool)
      (Fmt.str "%a" (pp_pi_type []) ty)
      true
      (Typechecker.TypecheckingResult.is_error (T.check_type cmd ty ht))

  let error ht cmd ty error =
    init_prover;
    Alcotest.(check Testable.typechecker_result)
      "" (Typechecker.TypecheckingResult.TypeError error)
      (T.check_type cmd ty ht)

  let is_equiv hty1 hty2 ctx ht =
    Alcotest.(check bool)
      "types are equivalent" true
      (check_subtype hty1 hty2 ctx ht && check_subtype hty2 hty1 ctx ht)

  (* (Pi4.Equiv.htyeqv ht [] Config.maxlen hty1 hty2) *)

  let not_equiv hty1 hty2 ctx ht =
    Alcotest.(check bool)
      "types are not equivalent" false
      (check_subtype hty1 hty2 ctx ht && check_subtype hty2 hty1 ctx ht)
end

let mk_inst name fields =
  Instance.
    { name;
      fields =
        List.map fields ~f:(fun (fn, ft) -> Declaration.{ name = fn; typ = ft })
    }
