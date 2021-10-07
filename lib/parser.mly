%{
    open Syntax
    open Expression
    open HeapType

    module Pi4 = struct end
%}

%token <string> BITSTRING
%token <string> HEXSTRING
%token <int> INT
%token <string> ID
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LSQUARE
%token RSQUARE
%token DOT
// %token CDOT
%token COLON
%token SEMI
%token PLUS
%token MINUS
%token BANG
%token QUERY
%token TILDE
%token AND
%token VBAR
%token OR
%token ARROW
%token DARROW
%token INST_EQ
%token EQ
%token AT
%token LT
%token GT
%token TRUE
%token FALSE
%token NOTHING
%token EMPTY
%token SIGMA
%token TOP
%token VALID
%token LENGTH
%token PKTIN
%token PKTOUT
%token AS
%token ADD
%token EXTRACT
%token RESET
%token REMIT
%token SKIP
%token IF
%token ELSE
%token HEADER
%token HEADERTYPE
%token EOF
%token NEG
%token AIG
%token BITBLAST
%token PAR_OR
%token QE
%token SIMPLIFY
%token SOLVE_EQS
%token THEN
%token UFBV
%token QFBV

%right PLUS MINUS LSQUARE
%left AS
%right SEMI
%left AND AT
%left BANG
%left NEG
%left OR DARROW
%nonassoc prec_sigma

%start header_type
%start program
%start command
%start ty
%start instance
%start smt_tactic

%type <HeaderTable.t -> Env.context -> HeapType.t> header_type
%type <Program.t> program
%type <HeaderTable.t -> Syntax.command> command
%type <HeaderTable.t -> Expression.t> cexpr
%type <HeaderTable.t -> Term.t> cterm
%type <HeaderTable.t -> Syntax.ty > ty
%type <Instance.t> instance
%type <Z3.Smtlib.tactic> smt_tactic

%%

program :
| decls=list(declaration) cmd EOF { 
  let ht = HeaderTable.of_decls decls in
  let cmd = $2 ht in
  Program.{ declarations=decls; command=cmd} }

declaration: 
| HEADERTYPE id=ID LBRACE f=nonempty_list(terminated(header_field, opt_semi)) RBRACE { 
  Declaration.HeaderTypeDecl { name=id; fields=f } }
| HEADER name=ID COLON typ=ID { 
  Declaration.HeaderInstanceDecl { name=name; type_name=typ } }

header_field:
| name=ID COLON typ=INT { Declaration.{ name; typ } }

instance:
| name=ID LBRACE fields=nonempty_list(terminated(header_field, opt_semi)) RBRACE {
  Instance.{ name; fields }
}

command:
| cmd EOF { 
  fun ht -> $1 ht}

cmd:
| LPAREN cmd RPAREN { 
  fun ht -> $2 ht }
| ADD LPAREN inst_name=ID RPAREN {
  fun ht -> 
    let inst = HeaderTable.lookup_instance_exn inst_name ht in
    Add inst }
| cmd AS LPAREN x=ID COLON hty RPAREN ARROW hty {
  fun ht ->
    let cmd = $1 ht in
    let hty_in = $6 ht [] in
    let hty_out = $9 ht [ (x, Env.VarBind hty_in) ] in
    Ascription (cmd, x, hty_in, hty_out)}
| EXTRACT LPAREN inst_str=ID RPAREN { 
  fun ht -> 
  let inst = HeaderTable.lookup_instance_exn inst_str ht in
  Extract inst }
| cmd SEMI cmd { 
  fun ht -> 
    let c1 = $1 ht in
    let c2 = $3 ht in 
    Seq (c1, c2) }
| IF cexpr LBRACE cmd RBRACE { 
  fun ht -> 
    let e = $2 ht in 
    let c = $4 ht in 
    If (e, c, Skip)}
| IF cexpr LBRACE cmd RBRACE ELSE LBRACE cmd RBRACE { 
  fun ht -> 
    let e = $2 ht in
    let c1 = $4 ht in
    let c2 = $8 ht in 
    If (e, c1, c2) }
| inst_name=ID DOT field_name=ID COLON EQ cterm {
  fun ht -> 
    let tm = $6 ht in
    let inst = HeaderTable.lookup_instance_exn inst_name ht in
    let left, right = 
      Instance.field_bounds inst field_name 
      |> Core.Result.ok_or_failwith in
    Assign (inst, left, right, tm) }
| inst_name=ID LSQUARE left=INT COLON right=INT RSQUARE COLON EQ cterm {
  fun ht ->
    let inst = HeaderTable.lookup_instance_exn inst_name ht in
    let tm = $9 ht in 
    Assign (inst, left, right, tm)
}
| REMIT LPAREN inst_name=ID RPAREN {
  fun ht -> 
    let inst = HeaderTable.lookup_instance_exn inst_name ht in
    Remit inst}
| RESET { 
  fun _ -> Reset }
| SKIP { 
  fun _ -> Skip }

cexpr:
| LPAREN cexpr RPAREN { 
  fun ht -> $2 ht }
| TRUE { 
  fun _ -> True }
| FALSE { 
  fun _ -> False }
| inst_name=ID DOT VALID {
  fun ht -> 
    let inst = HeaderTable.lookup_instance_exn inst_name ht in
    IsValid (0, inst) }
| cterm EQ EQ cterm { 
  fun ht -> 
    let t1 = $1 ht in
    let t2 = $4 ht in 
    TmEq (t1, t2) }
| cterm GT cterm {
    fun ht -> 
      let tm1 = $1 ht in 
      let tm2 = $3 ht in 
      TmGt (tm1, tm2) }
| cexpr AND cexpr {
    fun ht -> 
      let e1 = $1 ht in
      let e2 = $3 ht in
      And (e1, e2) }
| cexpr OR cexpr {
    fun ht -> 
      let e1 = $1 ht in
      let e2 = $3 ht in 
      Neg (And (Neg e1, Neg e2)) }
| preceded(BANG, cexpr) {
    fun ht -> 
      let e = $1 ht in
      Neg e }
| preceded(NEG, cexpr) {
    fun ht -> 
      let e = $1 ht in
      Neg e }

cterm:
| LPAREN cterm RPAREN { 
  fun ht -> $2 ht }
| inst_name=ID DOT field_name=ID { 
  fun ht -> 
    let inst = HeaderTable.lookup_instance_exn inst_name ht in
    Term.field_to_slice_exn inst field_name 0 }
| bs=BITSTRING {
  fun _ -> bv_s (Core_kernel.String.drop_prefix bs 2)}
| hs=HEXSTRING { 
  fun _ -> bv_x (Core_kernel.String.drop_prefix hs 2)}
| pkt=packet LSQUARE l=INT COLON r=INT RSQUARE {
    fun _ -> 
      Term.Slice (Packet (0, pkt), l, r)}
| inst_name=ID LSQUARE l=INT COLON r=INT RSQUARE {
  fun ht ->
    let inst = HeaderTable.lookup_instance_exn inst_name ht in 
    Term.Slice (Instance (0, inst), l, r)
}
| cterm MINUS cterm {
 fun ht ->
  let tm1 = $1 ht in
  let tm2 = $3 ht in
  Term.Minus (tm1, tm2) 
}

ty: 
  | LPAREN x=ID COLON hty RPAREN ARROW hty EOF {
    fun ht ->
      let hty_in = $4 ht [] in
      let hty_out = $7 ht [ (x, Env.VarBind hty_in) ] in
      Pi (x, hty_in, hty_out)
  } 

header_type:
  | hty = hty EOF { hty }
  
hty:
| LPAREN hty RPAREN { fun ht ctx -> $2 ht ctx }
| NOTHING { fun _ _ -> Nothing }
| EMPTY { fun _ _ -> Empty }
| inst_str=ID { 
    fun ht ctx -> 
      let inst = Syntax.HeaderTable.lookup_instance_exn inst_str ht in
      let x = Env.pick_fresh_name ctx "x" in
      HeapType.instance inst ht x }
| inst_str=ID TILDE {
  fun ht ctx -> 
    let inst = Syntax.HeaderTable.lookup_instance_exn inst_str ht in
    let x = Env.pick_fresh_name ctx "x" in
    HeapType.weak_instance inst x }
| QUERY inst_str=ID {
  fun ht ctx -> 
    let inst = Syntax.HeaderTable.lookup_instance_exn inst_str ht in
    let x = Env.pick_fresh_name ctx "x" in
    HeapType.weak_instance inst x }
| TOP { fun _ _ -> Top }
| SIGMA x=ID COLON hty DOT hty %prec prec_sigma {
    fun header_table ctx ->  
      let hty1 = $4 header_table ctx in
      let ctx' = Env.add_binding ctx x (Env.VarBind hty1) in
      let hty2 = $6 header_table ctx' in
      Sigma (x, hty1, hty2) }
// | inst_fst=ID CDOT inst_snd=ID {
//   fun ht ctx -> 
//     let fst = Syntax.HeaderTable.lookup_instance_exn inst_fst ht in
//     let snd = Syntax.HeaderTable.lookup_instance_exn inst_snd ht in
//     let x = Env.pick_fresh_name ctx "x" in
//     HeapType.pair fst snd x ht
// }
| hty PLUS hty {
    fun ht ctx ->
      let hty1 = $1 ht ctx in
      let hty2 = $3 ht ctx in
      Choice (hty1, hty2) }
| LBRACE x=ID COLON hty VBAR expr RBRACE {
    fun ht ctx -> 
      let hty1 = $4 ht ctx in
      let ctx' = Env.add_binding ctx x (Env.VarBind hty1) in
      let e = $6 ht ctx' in
      Refinement (x, hty1, e) }
| hty LSQUARE x=ID ARROW hty RSQUARE {
    fun ht ctx -> 
      let hty2 = $5 ht ctx in
      let ctx' = Env.add_binding ctx x (Env.VarBind hty2) in
      let hty1 = $1 ht ctx' in
      Substitution (hty1, x, hty2)
}

packet:
| PKTIN { PktIn }
| PKTOUT { PktOut }

term:
| LPAREN term RPAREN {
    fun ht ctx -> $2 ht ctx }
| n=INT { fun _ _ -> Num n }
| term PLUS term {
    fun ht ctx -> 
      let tm1 = $1 ht ctx in
      let tm2 = $3 ht ctx in
      Plus (tm1, tm2) }
| x=ID DOT pkt=packet DOT LENGTH {
    fun _ ctx -> 
      let binder = Env.name_to_index_exn ctx x in
      Length (binder, pkt) }
| LT GT { fun _ _ -> Bv Nil }
| bv=BITSTRING { 
    fun _ _ -> 
      bv_s (Core.String.drop_prefix bv 2) }
| hs=HEXSTRING {
    fun _ _ -> 
      bv_x (Core.String.drop_prefix hs 2) }
| term AT term { 
    fun ht ctx -> 
      let tm1 = $1 ht ctx in
      let tm2 = $3 ht ctx in 
      Concat (tm1, tm2) }
| x=ID DOT pkt=packet LSQUARE l=INT COLON r=INT RSQUARE {
    fun _ ctx -> 
      let binder = Env.name_to_index_exn ctx x in
      Slice (Packet (binder, pkt), l, r)}
| x=ID DOT inst_str=ID LSQUARE l=INT COLON r=INT RSQUARE {
    fun ht ctx -> 
      let binder = Env.name_to_index_exn ctx x in
      let inst = HeaderTable.lookup_instance_exn inst_str ht in
      Slice (Instance (binder, inst), l, r) }
| x=ID DOT inst_str=ID DOT field_name=ID {
    fun ht ctx -> 
      let binder = Env.name_to_index_exn ctx x in
      let inst = HeaderTable.lookup_instance_exn inst_str ht in 
      Term.field_to_slice_exn inst field_name binder }
| x=ID DOT pkt=packet {
    fun _ ctx -> 
      let binder = Env.name_to_index_exn ctx x in
      Term.Packet (binder, pkt) }
| x=ID DOT inst_str=ID {
  fun ht ctx -> 
    let binder = Env.name_to_index_exn ctx x in
    let inst = HeaderTable.lookup_instance_exn inst_str ht in 
    Term.Slice(Sliceable.Instance(binder, inst), 0, Instance.sizeof inst) }

expr:
| LPAREN expr RPAREN { 
    fun ht ctx -> $2 ht ctx }
| TRUE { 
    fun _ _ -> True }
| FALSE { 
    fun _ _ -> False }
| ID DOT ID DOT VALID { 
    fun ht ctx -> 
      let inst = HeaderTable.lookup_instance_exn $3 ht in
      let binder = Env.name_to_index_exn ctx $1 in
      IsValid (binder, inst)}
| term EQ EQ term {
    fun ht ctx -> 
      let tm1 = $1 ht ctx in 
      let tm2 = $4 ht ctx in 
      TmEq (tm1, tm2) }
| term EQ term {
    fun ht ctx -> 
      let tm1 = $1 ht ctx in 
      let tm2 = $3 ht ctx in 
      TmEq (tm1, tm2) }
| term GT term {
    fun ht ctx -> 
      let tm1 = $1 ht ctx in 
      let tm2 = $3 ht ctx in 
      TmGt (tm1, tm2) }
| expr AND expr {
    fun ht ctx -> 
      let e1 = $1 ht ctx in
      let e2 = $3 ht ctx in
      And (e1, e2) }
| expr OR expr {
    fun ht ctx -> 
      let e1 = $1 ht ctx in
      let e2 = $3 ht ctx in 
      Or(e1, e2) }
| expr DARROW expr {
    fun ht ctx -> 
    let e1 = $1 ht ctx in
    let e2 = $3 ht ctx in 
    Implies(e1, e2) }
| preceded(BANG, expr) {
    fun ht ctx -> 
      let e = $1 ht ctx in
      Neg e }
| preceded(NEG, expr) {
    fun ht ctx -> 
      let e = $1 ht ctx in
      Neg e }
| x=ID EQ EQ EQ y=ID {
  fun ht ctx -> 
    let idx_x = Env.name_to_index_exn ctx x in
    let idx_y = Env.name_to_index_exn ctx y in
    heap_equality idx_x idx_y ht
  }
| x=ID INST_EQ y=ID {
  let open Core_kernel in 
  fun ht ctx -> 
    let idx_x = Env.name_to_index_exn ctx x in
    let idx_y = Env.name_to_index_exn ctx y in
    HeaderTable.to_list ht 
    |> List.fold 
        ~init:True
        ~f:(fun acc inst -> 
          let slice var = Term.Slice (Instance (var, inst), 0, Instance.sizeof inst) in
          And (acc, TmEq (slice idx_x, slice idx_y)))
}

opt_semi:
|      { () }
| SEMI { () }

smt_tactic:
| AIG { Z3.Smtlib.AIG }
| BITBLAST { Z3.Smtlib.BitBlast }
| LPAREN PAR_OR l=smt_tactic r=smt_tactic RPAREN { Z3.Smtlib.ParOr (l,r)}
| QE { Z3.Smtlib.QE }
| SIMPLIFY { Z3.Smtlib.Simplify }
| SOLVE_EQS { Z3.Smtlib.SolveEQs }
| LPAREN THEN tactics=list(smt_tactic) RPAREN {
  Z3.Smtlib.Then tactics }
| UFBV { Z3.Smtlib.UFBV }
| QFBV { Z3.Smtlib.QFBV }
