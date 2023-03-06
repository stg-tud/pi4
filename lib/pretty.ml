open Core
open Fmt
open Syntax
open Z3.Smtlib

let pp_bit (pp : Format.formatter) (bit : Bit.t) =
  match bit with Zero -> pf pp "0" | One -> pf pp "1" | B n -> pf pp "b_%d" n

let rec pp_bitvector (pp : Format.formatter) (bitvec : BitVector.t) =
  match bitvec with
  | Nil -> pf pp ""
  | Cons (b, bv) -> pf pp "%a%a" pp_bit b pp_bitvector bv

let pp_packet (pp : Format.formatter) (packet : packet) =
  match packet with PktIn -> pf pp "pkt_in" | PktOut -> pf pp "pkt_out"

 
let rec pp_arith_expr (ctx : Env.context) (pp : Format.formatter)
    (expr : Expression.arith) =
  match expr with
  | Num n -> pf pp "%d" n
  | Length (x, p) ->
    let name = Env.index_to_name_exn ctx x in
    pf pp "%a.%a.length" string name pp_packet p
  | Plus (t1, t2) ->
    pf pp "(%a + %a)" (pp_arith_expr ctx) t1 (pp_arith_expr ctx) t2

let rec pp_bv_expr (ctx : Env.context) (pp : Format.formatter)
    (expr : Expression.bv) =
  match expr with
  | Minus (t1, t2) -> pf pp "(%a - %a)" (pp_bv_expr ctx) t1 (pp_bv_expr ctx) t2
  | Bv bv -> pf pp "0b%a" pp_bitvector bv
  | Concat (tm1, tm2) -> pf pp "%a@%a" (pp_bv_expr ctx) tm1 (pp_bv_expr ctx) tm2
  | Slice (s, l, r) -> pf pp "(%a)[%a:%a]" (pp_bv_expr ctx) s int l int r
  | Instance (x, inst) -> 
    let name = Env.index_to_name_exn ctx x in
    pf pp "%a.%a" string name string inst.name
  | Packet (x, p) ->
    let name = Env.index_to_name_exn ctx x in
    pf pp "%a.%a" string name pp_packet p

let pp_expr (ctx : Env.context) (pp : Format.formatter) (expr : Expression.t) =
  match expr with
  | ArithExpr e -> pp_arith_expr ctx pp e
  | BvExpr e -> pp_bv_expr ctx pp e

let rec pp_arith_expr_raw (pp : Format.formatter) (expr : Expression.arith) =
  match expr with
  | Num n -> pf pp "%d" n
  | Length (x, p) -> pf pp "%a.%a.length" int x pp_packet p
  | Plus (t1, t2) -> pf pp "%a + %a" pp_arith_expr_raw t1 pp_arith_expr_raw t2

let rec pp_bv_expr_raw (pp : Format.formatter) (expr : Expression.bv) =
  match expr with
  | Minus (t1, t2) -> pf pp "%a - %a" pp_bv_expr_raw t1 pp_bv_expr_raw t2
  | Bv bv -> pf pp "0b%a" pp_bitvector bv
  | Concat (tm1, tm2) -> pf pp "%a@%a" pp_bv_expr_raw tm1 pp_bv_expr_raw tm2
  | Slice (s, l, r) -> pf pp "(%a)[%a:%a]" pp_bv_expr_raw s int l int r
  | Instance (x, inst) -> pf pp "%a.%a" int x string inst.name
  | Packet (x, p) -> pf pp "%a.%a" int x pp_packet p

let pp_expr_raw (pp : Format.formatter) (expr : Expression.t) =
  match expr with
  | ArithExpr e -> pp_arith_expr_raw pp e
  | BvExpr e -> pp_bv_expr_raw pp e

let rec pp_form (ctx : Env.context) (pp : Format.formatter) (expr : Formula.t) =
  match expr with
  | True -> pf pp "true"
  | False -> pf pp "false"
  | IsValid (x, inst) ->
    let name = Env.index_to_name_exn ctx x in
    pf pp "%a.%a.valid" string name string inst.name
  | Eq (tm1, tm2) -> pf pp "%a == %a" (pp_expr ctx) tm1 (pp_expr ctx) tm2
  | Gt (tm1, tm2) -> pf pp "%a > %a" (pp_expr ctx) tm1 (pp_expr ctx) tm2
  | Neg e -> pf pp "¬(%a)" (pp_form ctx) e
  | And (e1, e2) -> pf pp "@[<v>(%a ∧@ %a)@]" (pp_form ctx) e1 (pp_form ctx) e2
  | Or (e1, e2) -> pf pp "@[<v>(%a ∨@ %a)@]" (pp_form ctx) e1 (pp_form ctx) e2
  | Implies (e1, e2) ->
    pf pp "@[<v 2>(%a ⇒@ (%a))@]" (pp_form ctx) e1 (pp_form ctx) e2

let rec pp_form_raw (pp : Format.formatter) (expr : Formula.t) =
  match expr with
  | True -> pf pp "true"
  | False -> pf pp "false"
  | IsValid (x, inst) -> pf pp "%a.%a.valid" int x string inst.name
  | Eq (tm1, tm2) -> pf pp "%a == %a" pp_expr_raw tm1 pp_expr_raw tm2
  | Gt (tm1, tm2) -> pf pp "%a > %a" pp_expr_raw tm1 pp_expr_raw tm2
  | Neg e -> pf pp "¬(%a)" pp_form_raw e
  | And (e1, e2) -> pf pp "@[<v>(%a ∧@ %a)@]" pp_form_raw e1 pp_form_raw e2
  | Or (e1, e2) -> pf pp "@[<v>%a ∨@ %a@]" pp_form_raw e1 pp_form_raw e2
  | Implies (e1, e2) ->
    pf pp "@[<v 2>(%a ⇒@ (%a))@]" pp_form_raw e1 pp_form_raw e2

let rec pp_header_type (ctx : Env.context) (pp : Format.formatter)
    (header_type : HeapType.t) =
  match header_type with
  | Nothing -> pf pp "∅"
  | Top -> pf pp "⊤"
  | Sigma (x, hty1, hty2) ->
    let x_fresh = Env.pick_fresh_name ctx x in
    let ctx' = Env.add_binding ctx x_fresh Env.NameBind in
    pf pp "@[<v 2>Σ%s:@ (%a).@ (%a)@]" x_fresh (pp_header_type ctx) hty1
      (pp_header_type ctx') hty2
  | Choice (hty1, hty2) ->
    pf pp "@[<v>%a@ +@ %a@]" (pp_header_type ctx) hty1 (pp_header_type ctx) hty2
  | Refinement (x, hty, e) ->
    let x_fresh = Env.pick_fresh_name ctx x in
    let ctx' = Env.add_binding ctx x_fresh Env.NameBind in
    pf pp "@[<v 2>{%s:@ %a@ | %a}@]" x_fresh (pp_header_type ctx) hty
      (pp_form ctx') e
  | Substitution (hty1, x, hty2) ->
    let x_fresh = Env.pick_fresh_name ctx x in
    let ctx' = Env.add_binding ctx x_fresh Env.NameBind in
    pf pp "@[<v 2>(%a)[@[<v 2>%s ↦@ %a@]]@]" (pp_header_type ctx') hty1 x_fresh
      (pp_header_type ctx) hty2

and pp_header_type_raw (pp : Format.formatter) (header_type : HeapType.t) =
  match header_type with
  | Nothing -> pf pp "∅"
  | Top -> pf pp "⊤"
  | Sigma (x, hty1, hty2) ->
    pf pp "@[<v 2>Σ%s:@ (%a).@ (%a)@]" x pp_header_type_raw hty1
      pp_header_type_raw hty2
  | Choice (hty1, hty2) ->
    pf pp "@[<v>(%a)@ +@ (%a)@]" pp_header_type_raw hty1 pp_header_type_raw hty2
  | Refinement (x, hty, e) ->
    pf pp "@[<v 2>{%s:@ %a@ | %a}@]" x pp_header_type_raw hty pp_form_raw e
  | Substitution (hty1, x, hty2) ->
    pf pp "@[<v 2>(%a)[@[<v 2>%s ↦@ %a@]]@]" pp_header_type_raw hty1 x
      pp_header_type_raw hty2

let pp_context (pp : Format.formatter) (ctx : Env.context) =
  let open Fmt in
  (* let pp_binding pp (x, binding) = match binding with | Env.NameBind -> pf pp
     "%a" string x | Env.VarBind hty -> pf pp "(%a, %a)" string x
     pp_header_type_raw hty in *)
  pf pp "@[<v>[";
  List.iteri ctx ~f:(fun idx (x, binding) ->
      match binding with
      | Env.NameBind -> pf pp "%s" x
      | Env.VarBind hty ->
        let _, ctx' = List.split_n ctx (idx + 1) in
        pf pp "%s → %a@ " x (pp_header_type ctx') hty);
  pf pp "]@]"

let pp_type (pp : Format.formatter) (ty : ty) =
  match ty with
  | Bool -> pf pp "bool"
  | BitVec MaxLen -> pf pp "bv(MAXLEN)"
  | BitVec (StaticSize n) -> pf pp "bv(%d)" n
  | Nat -> pf pp "nat"

let pp_pi_type (ctx : Env.context) (pp : Format.formatter) (ty : pi_type) =
  match ty with
  | Pi (x, hty1, hty2) ->
    let ctx' = Env.add_binding ctx x NameBind in
    pf pp "@[(%s: %a)@ →@ %a@]@." x (pp_header_type ctx') hty1
      (pp_header_type ctx') hty2

let pp_pi_type_raw (pp : Format.formatter) (ty : pi_type) =
  match ty with
  | Pi (x, hty1, hty2) ->
    pf pp "@[(%s: %a)@ →@ %a@]@." x pp_header_type_raw hty1 pp_header_type_raw
      hty2

let rec pp_command (pp : Format.formatter) (cmd : Command.t) =
  match cmd with
  | Extract inst -> pf pp "extract(%a)" string inst.name
  | If (e, c1, c2) ->
    pf pp "@[<v 2>if(%a) {@ %a@]@;<1 0>@[<v 2>} else {@ %a@ }@]"
      (pp_form (Env.add_binding [] "" NameBind))
      e pp_command c1 pp_command c2
  | Assign (inst, left, right, value) ->
    pf pp "%s[%d:%d] := %a" inst.name left right
      (pp_expr [ ("", NameBind) ])
      value
  | Remit inst -> pf pp "remit(%s)" inst.name
  | Remove inst -> pf pp "remove(%s)" inst.name
  | Reset -> pf pp "reset"
  | Seq (c1, c2) -> pf pp "@[<v>%a;@ %a@]" pp_command c1 pp_command c2
  | Skip -> pf pp "skip"
  | Add inst -> pf pp "add(%s)" inst.name
  | Ascription (cmd, x, hty_in, hty_out) ->
    pf pp "@[(%a@ as@ (%a:%a)@ -> %a)@]" pp_command cmd string x
      (pp_header_type []) hty_in
      (pp_header_type [ (x, Env.NameBind) ])
      hty_out

let pp_header_field (pp : Format.formatter) (header_field : Declaration.field) =
  pf pp "(%a:%a)" string header_field.name int header_field.typ

let pp_instance (pp : Format.formatter) (inst : Instance.t) =
  pf pp "%a {%a}" string inst.name (list pp_header_field) inst.fields

let pp_table_entry (pp : Format.formatter) (inst : Instance.t) =
  pf pp "@[<v 2>%a ->@ %a@]" string inst.name (list pp_header_field) inst.fields

let pp_header_table (pp : Format.formatter) (header_table : HeaderTable.t) =
  pf pp "@[<v>%a@]@."
    (list ~sep:cut pp_table_entry)
    (HeaderTable.to_list header_table)

let pp_declaration (pp : Format.formatter) (decl : Declaration.t) =
  match decl with
  | HeaderTypeDecl { name; fields } ->
    pf pp "@[<v>header_type %a {@ %a@ }@]" string name (list pp_header_field)
      fields
  | HeaderInstanceDecl { name; type_name } ->
    pf pp "@[<v>header %a: %a@]" string name string type_name

let pp_program (pp : Format.formatter) (program : Program.t) =
  pf pp "@[<v 2>Declarations:@ %a@ Command:@ %a@]@."
    (list ~sep:cut pp_declaration)
    program.declarations pp_command program.command

let pp_ident (pp : Format.formatter) (ident : Z3.Smtlib.identifier) =
  match ident with Id x -> string pp x

let rec pp_sort (pp : Format.formatter) (sort : Z3.Smtlib.sort) =
  match sort with
  | Sort x -> pp_ident pp x
  | SortApp (x, sorts) -> pf pp "(%a %a)" pp_ident x (list pp_sort) sorts
  | BitVecSort n -> pf pp "(_ BitVec %a)" int n

let pp_ident_sort is = parens (pair ~sep:sp pp_ident pp_sort) is

let rec pp_smtlib_term (pp : Format.formatter) (term : Z3.Smtlib.term) =
  match term with
  | String s -> string pp s
  | Literal lit -> string pp lit
  | Int n -> int pp n
  | BitVec (n, w) -> pf pp "(_ bv%a %a)" int n int w
  | BitVec64 n -> pf pp "(_ bv%a 64)" int64 n
  | BigBitVec (n, w) -> pf pp "(_ bv%a %a)" string (Bigint.to_string n) int w
  | Const (Id x) -> string pp x
  | ForAll (lst, t) ->
    pf pp "@[<v 2>(forall (@ %a)@ %a)@]" (list pp_ident_sort) lst pp_smtlib_term
      t
  | App (Id f, args) ->
    pf pp "@[<v 2>(%a@ %a)@]" string f (list pp_smtlib_term) args
  | Let (x, t1, t2) ->
    pf pp "@[<v 2>(let@ (@[<v 2>(%a@ %a)@])@ %a)@]@ " string x pp_smtlib_term t1
      pp_smtlib_term t2

let rec pp_tactic (pp : Format.formatter) (tactic : Z3.Smtlib.tactic) =
  match tactic with
  | Simplify -> pf pp "simplify"
  | SolveEQs -> pf pp "solve-eqs"
  | BitBlast -> pf pp "bit-blast"
  | AIG -> pf pp "aig"
  | BV -> pf pp "bv"
  | Repeat t -> pf pp "repeat %a" pp_tactic t
  | SAT -> pf pp "sat"
  | SMT -> pf pp "smt"
  | QFBV -> pf pp "qfbv"
  | UFBV -> pf pp "ufbv"
  | QE -> pf pp "qe"
  | UsingParams (t, params) ->
    pf pp "@[<v 2>(using-params@ %a %a)@]" pp_tactic t
      (list (pair string bool))
      params
  | Then ts -> pf pp "@[<v 2>(then@ %a)@]" (list pp_tactic) ts
  | ParOr (t1, t2) ->
    pf pp "@[<v 2>(par-or@ %a@ %a)@]" pp_tactic t1 pp_tactic t2

let rec pp_annotation_body (pp : Format.formatter)
    (annot : Annotation.annotation_body) =
  match annot with
  | Reset -> pf pp "reset"
  | Block b -> pf pp "%s" b
  | TypedBlock (body, typ) ->
    pf pp "@[((%a) as %a)@]" pp_annotation_body body (pp_pi_type []) typ
  | Sequence (l, r) -> pf pp "%a;%a" pp_annotation_body l pp_annotation_body r
