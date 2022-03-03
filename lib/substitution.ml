open Core_kernel
open Syntax
open Formula
open HeapType
open Result
open Expression
open Let_syntax
module Log = (val Logs.src_log Logging.substitution_src : Logs.LOG)

module FormulaId = struct
  module T = struct
    type t =
      | Valid of int * Instance.t * bool        (* x.τ.valid *)
      | InstEqual of int * Instance.t           (* x.τ == y.τ *)
      | ValidEqual of int * Instance.t          (* x.τ.valid == y.τ.valid *)
      | EqExp of Expression.t                   (* x.exp == y.exp *)
      | GtExp of Expression.t                   (* x.exp > y.exp *)
      | EqInst of int * Instance.t              (* x.τ == y.exp_bv *)
      | EqPkt of int * Syntax.packet
      | EqBvSl of (Sliceable.t * int * int)     (* x.τ[hi:lo] == y.exp_bv *)
      | EqBv of Expression.t                    (* x.τ == y.bv *)
      | Err of string
      [@@deriving compare, sexp] 
  end
  include T
  include Comparable.Make(T)
end

type fid_map =
  Formula.t Map.M(FormulaId).t
[@@deriving sexp]
let pp_fromula_id (pp : Format.formatter) (fid :FormulaId.t) = 
  let open Fmt in
  match fid with
    | Valid (v, i, b) -> pf pp "valid_%b_%i.%s" b v i.name
    | InstEqual (v, i) -> pf pp "inst_equal_%i.%s" v i.name
    | ValidEqual (v, i) ->  pf pp "valid_equal_%i.%s" v i.name
    | GtExp e -> pf pp "gt_exp_%a" Pretty.pp_expr_raw e
    | EqExp e -> pf pp "eq_exp_%a" Pretty.pp_expr_raw e
    | EqInst (v, i) -> pf pp "eq_inst_%i.%s" v i.name
    | EqPkt (v, p) -> pf pp "eq_pkt_%i.%a" v Pretty.pp_packet p
    | EqBvSl (i, s, e) -> pf pp "eq_bv_sl_%a[%i:%i]" Pretty.pp_sliceable_raw i s e
    | EqBv e -> pf pp "eq_bv_%a" Pretty.pp_expr_raw e
    | Err e -> pf pp "Error: %s" e

let pp_pkt_slice (pp : Format.formatter) (sl, hi, lo) =
  let open Fmt in
  pf pp "@[%a[%i:%i] @]" Pretty.pp_sliceable_raw sl hi lo 

let var_from_sliceable s =
  let open Sliceable in
  match s with
  | Packet(v, _)
  | Instance(v, _) -> v

let rec get_var expr = 
  let open Expression in
  let check_vars v1 v2 =
    match v1 with
    | Ok a1 -> (
      match v2 with
      | Ok a2 -> (
        if phys_equal a1 a2 
          then 
            Ok a1
          else 
            Error (`InvalidArgumentError "Found conflictng vars"))
      | Error _ -> Ok a1)
    | Error _ -> (
      match v2 with
      | Ok a2 -> Ok a2
      | Error _ -> Error (`InvalidArgumentError "No valid vars found"))
  in
  match expr with
  | ArithExpr(Length(v, _)) -> Ok(v)
  | ArithExpr(Plus(arith1, arith2)) -> (
    let a1_res = get_var (ArithExpr (arith1)) in
    let  a2_res = get_var (ArithExpr (arith2)) in
    check_vars a1_res a2_res)
  | BvExpr(Concat(bv1, bv2))
  | BvExpr(Minus(bv1, bv2)) -> (
    let b1_res = get_var (BvExpr (bv1)) in
    let  b2_res = get_var (BvExpr (bv2)) in
    check_vars b1_res b2_res)
  | ArithExpr(Num _)
  | BvExpr(Bv(_)) -> Error (`InvalidArgumentError "No var found")
  | BvExpr(Slice(s, _, _)) -> Ok (var_from_sliceable s)
  | BvExpr(Packet(v, _)) -> Ok v

let get_subs_expr exp =
  (* Log.debug (fun m -> m "@[Finding substitution for %a @]" Pretty.pp_expr_raw exp); *)
  let open Expression in
  let rec get_exp e = 
    match e with
    | ArithExpr (Plus (a1, a2)) -> (
      let opt1 = get_exp (ArithExpr a1) in
      match opt1 with
      | Some _ -> opt1
      | None ->  get_exp (ArithExpr a2))
    | ArithExpr (Length (_)) ->  Some e
    | ArithExpr (Num (_)) ->  None
    | BvExpr (Concat (b1, b2)) -> (
      let opt1 = get_exp (BvExpr b1) in
      let opt2 = get_exp (BvExpr b2) in
      match (opt1, opt2) with
        | Some BvExpr Packet _, Some BvExpr Slice _ -> opt1
        | Some BvExpr Packet _, Some BvExpr Packet _
        | Some BvExpr Slice _, Some BvExpr Packet _ -> opt2
        | Some _ , None ->  opt1
        | None , Some _ -> opt2
        | _ -> None)
    | BvExpr (Slice (_)) -> Some e
    | BvExpr (Packet (_)) -> Some e
    | BvExpr (Minus (_))
    | BvExpr (Bv (_)) -> None
  in
  let exp_o = get_exp exp in
  match exp_o with
  | Some e -> 
      (* Log.debug (fun m -> m "@[Found: %a @]" Pretty.pp_expr_raw e);  *)
      e
  | None -> 
      (* Log.debug (fun m -> m "@[Nothing found, returning: %a @]" Pretty.pp_expr_raw exp); *)
      exp

let replace_expression exp_i exp_o exp_r =
  let open Expression in
  if [%compare.equal: Expression.t ] exp_i exp_o then Ok exp_r
  else
  let rec replace_arith exp_i exp_o exp_r : Expression.arith = 
    let open Expression in
    if [%compare.equal: Expression.arith ] exp_i exp_o then exp_r
    else
    match exp_i with
    | Plus (a1, a2) -> Plus(replace_arith a1 exp_o exp_r, replace_arith a2 exp_o exp_r)
    | Length (_)
    | Num (_) ->  exp_i
  in
  let rec replace_bv exp_i exp_o exp_r : Expression.bv = 
    let open Expression in
    if [%compare.equal: Expression.bv ] exp_i exp_o then exp_r
    else
    match exp_i with
    | Concat (b1, b2) -> Concat(replace_bv b1 exp_o exp_r, replace_bv b2 exp_o exp_r)
    | Minus (b1, b2) -> Minus(replace_bv b1 exp_o exp_r, replace_bv b2 exp_o exp_r)
    | Slice (_)
    | Packet (_)
    | Bv (_) -> exp_i
  in
  match exp_i, exp_o, exp_r with
  | ArithExpr exp1, ArithExpr exp2, ArithExpr exp3 -> Ok (ArithExpr(replace_arith exp1 exp2 exp3))
  | BvExpr exp1, BvExpr exp2, BvExpr exp3 -> Ok (BvExpr(replace_bv exp1 exp2 exp3))
  | _ -> Error(`InvalidArgumentError "All arguments must be of type ArithExpr or BvExpr")


let extract_to_map form : (FormulaId.t, Formula.t , FormulaId.comparator_witness) Map.t=
  let update_instance m_in i_exp exp = 
    let open FormulaId in
    match i_exp with
    | Sliceable.Instance(var, inst) -> (
      let k_i = EqInst (var, inst) in
      let inst_opt = Map.find m_in k_i in
      let data =
        match inst_opt with
        | Some inst -> 
          And(inst, exp)
        | None -> 
          exp
        in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k_i Pretty.pp_form_raw  data);
        let m_t = Map.set m_in ~key:k_i ~data:data in
        m_t)
    | _ -> (
      Log.debug (fun m -> m "@[Nothing to update since %a is no instance@]" Pretty.pp_sliceable_raw i_exp);
      m_in)
  in
  let rec ext f m_in : (FormulaId.t, Formula.t , FormulaId.comparator_witness) Core.Map.t =
    let open FormulaId in
    match f with
    | And(f1, f2) -> 
      let m_tmp1 = ext f1 m_in in
      ext f2 m_tmp1

      (* x.τ.valid == y.τ.valid *)
    | Or
      ( And
        ( Neg(IsValid(v1, i1)),
          Neg(IsValid(_))
        ),
        And
        ( IsValid(_),
          IsValid(_)
        )
      ) ->
      let k = ValidEqual(v1, i1) in
      Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
      Map.set m_in ~key:k ~data:f

      (* x.τ == y.τ *)
    | Or
      ( And
        ( Neg(IsValid(v1, i1)),
          Neg(IsValid(_))),
        And
        ( And
          ( IsValid(_),
            IsValid(_)),
          And(_)
        )
      )

    | Or
      ( And
        ( Neg(IsValid(v1, i1)),
          Neg(IsValid(_))
        ),
        And
        ( And
          ( IsValid(_),
            IsValid(_)
          ),
          Eq 
          ( BvExpr(_),
            BvExpr(_)
          )
        )
      ) -> 
      let k = InstEqual (v1, i1) in
      Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
      Map.set m_in ~key:k ~data:f

      (* true --> ignore *)
    | True -> m_in

    | Gt (exp1, _) -> (
      let subs_exp = get_subs_expr exp1 in
      match subs_exp with
      | ArithExpr _ ->  
        let k = GtExp exp1 in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f
      | _ -> m_in)

    | Eq (exp1, _) -> (
      let subs_exp = get_subs_expr exp1 in
      match subs_exp with
      | BvExpr(Slice(inst, hi, lo)) -> (
        let k = EqBvSl (inst, hi, lo) in
        let m_in = update_instance m_in inst f in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f)
      | BvExpr (Packet(v,p)) -> 
        let k = EqPkt (v, p) in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f
      | BvExpr _ ->  
        let k = EqBv subs_exp in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f
      | ArithExpr _ ->  
        let k = EqExp subs_exp in
        Log.debug (fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw  f);
        Map.set m_in ~key:k ~data:f)

      (* x.τ.valid  *)
    | Neg(IsValid(v, i)) -> 
      let k = Valid (v, i, false) in
      Log.debug(fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw f);
      Map.set m_in ~key:k ~data:f


    | IsValid(v, i) -> 
      let k = Valid (v, i, true) in
      Log.debug(fun m -> m "@[%a: %a@]" pp_fromula_id k Pretty.pp_form_raw f);
      Map.set m_in ~key:k ~data:f
    | _ -> 
      Log.debug(fun m -> m "@[Unmatched Form: %a@]" Pretty.pp_form_raw f);
      m_in
    in
    let map = Map.empty(module FormulaId) in
    ext form map

let find_or_err map key = 
  let rslt = Core.Map.find map key in
  match rslt with
  | Some v -> Ok(v)
  | None -> Error(`NotFoundError "No entry found for given key")
 
let clean_concat_eqn form =
  Log.debug(fun m -> m "Called Cleanup");
  let rec cce f = 
    match f with
    | Eq(BvExpr(Packet(_, p_l) as pkt_l), BvExpr(Slice(Packet(v_r, p_r) as pkt_r, hi, _))) -> 
      if [%compare.equal: Syntax.packet] p_l p_r then
        if hi > 0 then
          Eq
          ( BvExpr ( Concat
            ( Slice(pkt_r, 0, hi),
              pkt_l
            )),
            BvExpr(Packet(v_r, p_r))
          )
        else
          Eq
          ( BvExpr ( pkt_l),
            BvExpr(Packet(v_r, p_r))
          )
      else
        f
    | And(f1, f2) -> 
      let cce1 = cce f1 in
      let cce2 = cce f2 in
      And( cce1, cce2)
    | Or(f1, f2) -> 
      let cce1 = cce f1 in
      let cce2 = cce f2 in
      Or( cce1, cce2)
    | _ -> f
    in
  cce form
  



let split_concat_eqn eqn maxlen =
  let rec get_bv bv ln = 
    match bv with
    | BitVector.Cons(b, tail) ->  
      if ln > 0 then
        let%bind t, c = get_bv tail (ln - 1) in
        Ok (BitVector.Cons(b, t), c)
      else
        Ok (BitVector.Cons(b, Nil), tail)
    | _ -> Error(`InvalidArgumentError "Index exceeded BitVector length")
  in 

  let split_assign inst hib lob bv = 
    let open Instance in
    let rec splt (fields : Declaration.field list) b =
      match fields with
      | f :: [] -> 
        let%bind hi, lo = field_bounds inst f.name in
        if hi < hib || lo > lob then
          Ok(True)
        else
          let%bind sl, _ = get_bv b (lo - hi) in
          Ok(
            Eq
              ( BvExpr(Slice(Instance(0, inst), hi,lo)),
                BvExpr(Bv(sl)))
          )
      | f :: tail -> 
        let%bind hi, lo = field_bounds inst f.name in
        if hi < hib || lo > lob then
          splt tail b
        else
          let%bind sl, b = get_bv b (lo - hi) in
          let%bind tl = splt tail b in
          Ok 
          ( And
            ( Eq
              ( BvExpr(Slice(Instance(0, inst), hi,lo)),
                BvExpr(Bv(sl))),
                tl
            )
          )
      | [] -> Error(`InvalidArgumentError "Nothing to split in given instance")
    in 
    splt inst.fields bv
  in


  let split_inst inst hib lob=
    let open Instance in
    let rec splt (fields : Declaration.field list) =
      match fields with
      | f :: [] -> 
        let%bind hi, lo = field_bounds inst f.name in
        if hi < hib || lo > lob then
          Ok (True)
        else
          Ok ( Eq
            ( BvExpr(Slice(Instance(0, inst), hi,lo)),
              BvExpr(Slice(Instance(1, inst), hi,lo))))

      | f :: tail -> 
        let%bind hi, lo = field_bounds inst f.name in
        if hi < hib || lo > lob then
          splt tail
        else
          let rslt_l = 
            Eq
            ( BvExpr(Slice(Instance(0, inst), hi,lo)),
              BvExpr(Slice(Instance(1, inst), hi,lo))) in
          let%bind rslt_r = splt tail in
          Ok (And(rslt_l, rslt_r))

      | [] -> Error(`InvalidArgumentError "Nothing to split in given instance")
    in
    splt inst.fields 
  in
  
  let split_inst_pkt v inst pkt_sl =
    let open Instance in
    let rec splt (fields : Declaration.field list) = 
      match fields with
      | f :: [] -> 
        let%bind hi, lo = field_bounds inst f.name in
        let p, hi_p,_ = pkt_sl in
        let rexp = 
          Eq
          ( BvExpr(Slice(Instance(v, inst), hi, lo)), 
            BvExpr(Slice(p, hi_p + hi, hi_p + lo))) in
        Ok (rexp)

      | f :: tail -> 
        let%bind hi, lo = field_bounds inst f.name in
        let p, hi_p,_ = pkt_sl in
        let rslt_l = 
          Eq
          ( BvExpr(Slice(Instance(v, inst), hi, lo)),
            BvExpr(Slice(p, hi_p + hi, hi_p + lo))) in
        let%bind rslt_r = splt tail in
        Ok (And(rslt_l, rslt_r))
        
      | [] -> Error(`InvalidArgumentError "Nothing to split in given instance")
    in
    let%bind rsplt = splt inst.fields in
    let len = Instance.sizeof inst in
    let (p, hi, lo) = pkt_sl in
    Ok(rsplt, (p, hi + len, lo))
  in
  let rec split_exp exp pkt=
    (* Log.debug (fun m -> m "@[Splitting expression %a with %a@]" Pretty.pp_expr_raw (BvExpr(exp)) pp_pkt_slice pkt); *)
    match exp with
    | Concat
      ( Slice(Instance(v_l,i_l), _, _),
       bv_exp_r
      ) -> 
      let%bind rslt_l, pkt_l = split_inst_pkt v_l i_l pkt in
      let%bind rslt_r = split_exp bv_exp_r pkt_l in
      Ok (And(rslt_l, rslt_r))

    | _ -> 
      let pkt_p, pkt_hi, pkt_lo = pkt in
      Ok( Eq
          ( BvExpr(exp),
            BvExpr(Slice(pkt_p, pkt_hi, pkt_lo))))
  in 
  let rec sce e =
    (* Log.debug (fun m -> m "@[Splitting %a@]" Pretty.pp_form_raw e); *)
    match e with
    | Eq
      ( BvExpr(Slice(Instance(_,i_l), hi , lo)),
        BvExpr(Bv(bv))
      ) -> split_assign i_l hi lo bv

    | Eq
      ( BvExpr(Concat(bv1, bv2)),
        BvExpr(Slice(pkt, hi_pkt, lo_pkt))
      ) -> 
      split_exp (Concat(bv1, bv2)) (pkt, hi_pkt, lo_pkt)

    | Eq
      ( BvExpr(exp),
        BvExpr(Packet(var, pkt))
      ) -> 
      sce ( Eq
            ( BvExpr(exp),
             BvExpr(Slice(Packet(var, pkt), 0, maxlen)))
          )

    | Eq 
      ( BvExpr(Slice(Instance(_,i_l), hi , lo)),
        BvExpr(Slice(Instance(_,i_r), _,_))
      ) ->
      if [%compare.equal: Instance.t] i_l i_r then
        split_inst i_l hi lo
      else
        Error (`InvalidArgumentError "Cannot split different instances")

    | And(e1, e2) -> 
      let%bind sce1 = sce e1 in
      let%bind sce2 = sce e2 in
      Ok (And(sce1, sce2))

    | Or(e1, e2) -> 
      let%bind sce1 = sce e1 in
      let%bind sce2 = sce e2 in
      Ok (Or(sce1, sce2))
    | _ -> Ok e
    in
  sce eqn

let some_or_default opt def =
  match opt with
  | Some x -> x
  | None -> def

let ok_or_default result def = 
  match result with
  | Ok v -> v
  | _ ->  def

let shift_slices form n =
  Log.debug(fun m -> m "Shifting slices by: %i" n);
  let rec ss f = 
    match f with 
    | Eq(BvExpr(Packet(0,PktIn)), BvExpr(Slice(Packet(1, PktIn), hi, lo))) ->
      Eq(BvExpr(Packet(0,PktIn)), BvExpr(Slice(Packet(1, PktIn), hi + n, lo)))
    | Eq(BvExpr(Slice(Instance(_),_,_)) as bv_l, BvExpr(Slice(Packet(1, PktIn), hi, lo))) ->
      Eq( bv_l, BvExpr(Slice(Packet(1, PktIn), hi + n, lo + n)))
    | And(f1, f2) -> And(ss f1, ss f2)
    | Or(f1, f2) -> Or(ss f1, ss f2)
    | _ -> f
  in
  let fm = ss form in
  Log.debug(fun m -> m "Result: %a" Pretty.pp_form_raw fm);
  fm

let simplify_formula form (m_in: (FormulaId.t, Formula.t, FormulaId.comparator_witness) Map_intf.Map.t) maxlen: Formula.t option=
  let rec sf form m_in maxlen = 
    let open FormulaId in
    match form with
    | And(f1, f2) -> 
      let fs1 = ok_or_default (sf f1 m_in maxlen) f1 in
      let fs2 = ok_or_default (sf f2 m_in maxlen) f2 in
      Ok (And(fs1, fs2))
      
    | Or
      ( And
        ( Neg(IsValid(v1, i1)),
          Neg(IsValid(_))),
        And
        ( IsValid(_),
          IsValid(_))
      ) -> (
      let valid_opt = Map.find m_in (Valid(v1, i1, true)) in
      let invalid_opt = Map.find m_in (Valid(v1, i1, false)) in
      match  (valid_opt, invalid_opt) with
      | Some _, None -> 
        let smpl = IsValid(v1, i1) in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
        Ok smpl

      | None, Some _ -> 
        let smpl = Neg(IsValid(v1, i1)) in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw smpl);
        Ok smpl

      | Some _, Some _ -> Error (`InvalidExpressionError "Valid and Invalid entry found")

      | _ -> Ok(form))
      
    | Or
      ( And
        ( Neg(IsValid(v1, i1)),
          Neg(IsValid(v2, i2))),
        And
        ( And
          ( IsValid(v3, i3),
            IsValid(v4, i4)
          ),
          f_r
        )
      ) -> (
      let f_l_neg = 
        And            
        ( Neg(IsValid(v1, i1)),
          Neg(IsValid(v2, i2))) 
        in
      let f_l_pos = 
        And
        ( IsValid(v3, i3),
          IsValid(v4, i4))
        in
      let f_l = Or(f_l_neg, f_l_pos)in
      let smpl_l =  ok_or_default (sf f_l m_in maxlen) f_l in
      let smpl_r = sf f_r m_in maxlen in
      match smpl_l with

      | Neg(IsValid(_)) | IsValid(_) -> (
        match smpl_r with
        | Ok s -> Ok(And(smpl_l, s))
        | _ -> Ok smpl_l)
      | _ -> Ok(Or(f_l_neg, And(f_l_pos, ok_or_default smpl_r f_r))))
    
    | Eq(exp1, exp2) -> (
      let subs_id =
        match exp2 with
        | ArithExpr Length (_, pkt) -> Some (EqExp(ArithExpr(Length(0, pkt))))

        | BvExpr Slice(s, hi, lo) -> (
          match s with
          | Packet (_,p) -> 
            if [%compare.equal: var] hi 0 && [%compare.equal: var] lo maxlen 
            then
              Some (EqPkt(0,p))
            else
              Some (EqBv (BvExpr (Slice (Packet (0,p), hi, lo))))

          | Instance (_, i) -> 
            if [%compare.equal: var](lo - hi) (Instance.sizeof i) 
            then
              Some (EqInst (0,i))
            else
              Some (EqBvSl (Instance (0,i), hi, lo)))

        | BvExpr Packet (_, p) -> Some (EqPkt(0,p))

        | _ -> None 
      in
      match subs_id with
      | Some (EqInst (v,i)) -> 
        Log.debug (fun m -> m "@[Looking for: %a@]" pp_fromula_id (EqInst(v,i))); 
        let subs = ok_or_default (find_or_err m_in (EqInst(v,i))) True in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw subs);
        Ok(subs)

      | Some (EqPkt (v,p)) -> 
        Log.debug (fun m -> m "@[Looking for: %a@]" pp_fromula_id (EqPkt(v,p))); 
        let%bind subs = find_or_err m_in (EqPkt(v,p)) in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@]" Pretty.pp_form_raw form Pretty.pp_form_raw subs);
        Ok(subs)

      | Some id -> (
        Log.debug (fun m -> m "@[Looking for: %a@]" pp_fromula_id id); 
        let%bind subs = find_or_err m_in id in
        let%bind substitution_l = 
          match subs with
          | Eq (subs_l, _)
          | Gt (subs_l, _) -> Ok subs_l
          | _ -> Error (`InvalidArgumentError "Nothing to replace")
        in 
        Log.debug (fun m -> m "@[subs_l: %a@]" Pretty.pp_expr_raw substitution_l); 
        let%bind substitution_r = 
          match subs with
          | Eq (_ , subs_r)
          | Gt (_, subs_r) -> Ok subs_r
          | _ -> Error (`InvalidArgumentError "Nothing to replace")
        in
        Log.debug (fun m -> m "@[subs_r: %a@]" Pretty.pp_expr_raw substitution_r); 
        let%bind exp_old = 
          match id with
          | EqBv exp
          | EqExp exp
          | GtExp exp -> Ok exp
          | EqBvSl (s, hi, lo) -> Ok (BvExpr(Slice(s,hi, lo)))
          | _ -> Error (`InvalidArgumentError "Unexpected FormulaId")
        in
        Log.debug (fun m -> m "@[exp_old: %a@]" Pretty.pp_expr_raw exp_old);
        let%bind exp_new = replace_expression substitution_l exp_old exp1
        in
        Log.debug (fun m -> m "@[--> replaced @ %a @ by@ %a@ in %a@]" 
        Pretty.pp_expr_raw exp_old 
        Pretty.pp_expr_raw exp1 
        Pretty.pp_expr_raw substitution_l);
        Ok (Eq(exp_new, substitution_r)))
      | _ ->
        Log.debug (fun m -> m "@[--> replaced nothing @]");
        Ok form)
    | _ -> 
      Log.debug (fun m -> m "@[--> replaced nothing @]");
      Ok form
  in 

  let pkt_in = Map.find m_in (FormulaId.EqPkt(0, PktIn)) in
  let form = 
    match pkt_in with
    | Some(Eq(_, BvExpr(Slice(Packet(1, PktIn), hi ,_ )))) ->
      shift_slices form hi
    | _ -> form
  in
  let result = sf form m_in maxlen in
  match result with
  | Ok f -> 
    Some (clean_concat_eqn f)
  | _ -> None

let rec simplify hty maxlen : HeapType.t =
  let hty = Simplify.fold_refinements hty in
  let result = (
    match hty with
    | Choice (hty1, hty2) ->
      Ok 
      ( Choice
        ( simplify hty1 maxlen,
          simplify hty2 maxlen))
    | Refinement( s, h ,f) ->
      Ok (Refinement (s, simplify h maxlen, f))
    | Substitution (h, _, subs) -> (
      let h = simplify h maxlen in
      let subs = simplify subs maxlen in
      Log.debug (fun m -> m "====== Building substitution map ======");
      let%bind subs_map = 
        match subs with
        | Refinement(_,_,f_subs) -> 
          let%bind split_subs = split_concat_eqn f_subs maxlen in
          Log.debug (fun m -> m "@[Extracting formula %a@]" Pretty.pp_form_raw split_subs);
          Ok (extract_to_map split_subs)
        | _ ->  Error (`InvalidArgumentError "subs is not a Refinement")
      in
      match h with
      | Refinement(s,ht,f) -> 
        Log.debug (fun m -> m "====== Simplifying formula ======");
        let%bind f_split = split_concat_eqn f maxlen in
        Log.debug (fun m -> m "@[Simplfying formula %a@]" Pretty.pp_form_raw f_split);
        Ok
        ( Refinement(s, ht, some_or_default (simplify_formula f_split subs_map maxlen) f))
      | Choice(Refinement(s1,ht1,f1), (Choice(_,_) as ch)) ->
        let%bind f1_split = split_concat_eqn f1 maxlen in
        Log.debug (fun m -> m "@[Simplfying formula %a@]" Pretty.pp_form_raw f1_split);
        Ok 
          ( Choice
            ( Refinement(s1, ht1, some_or_default (simplify_formula f1_split subs_map maxlen) f1),
              simplify ch maxlen)
          )
      | Choice((Choice(_,_) as ch), Refinement(s1,ht1,f1)) ->
        let%bind f1_split = split_concat_eqn f1 maxlen in
        Log.debug (fun m -> m "@[Simplfying formula %a@]" Pretty.pp_form_raw f1_split);
        Ok 
          ( Choice
            (simplify ch maxlen,
            Refinement(s1, ht1, some_or_default (simplify_formula f1_split subs_map maxlen) f1))
          )

      | Choice((Choice(_,_) as ch1), (Choice(_,_) as ch2)) ->
        Ok 
          ( Choice
            ( simplify ch1 maxlen,
              simplify ch2 maxlen)
          )
      | Choice(Refinement(s1,ht1,f1), Refinement(s2,ht2,f2)) -> 
        let%bind f1_split = split_concat_eqn f1 maxlen in
        Log.debug (fun m -> m "@[Simplfying formula %a@]" Pretty.pp_form_raw f1_split);
        let%bind f2_split = split_concat_eqn f2 maxlen in
        Log.debug (fun m -> m "@[Simplfying formula %a@]" Pretty.pp_form_raw f2_split);
        Ok 
          ( Choice
            ( Refinement(s1, ht1, some_or_default (simplify_formula f1_split subs_map maxlen) f1),
              Refinement(s2, ht2, some_or_default (simplify_formula f2_split subs_map maxlen) f2)))

      | Choice(hty1, hty2) ->
        Ok 
        ( Choice
          ( simplify hty1 maxlen,
            simplify hty2 maxlen))

      | _ ->  Error (`InvalidArgumentError  "h is not a Refinement"))   

    | _ -> Error (`InvalidArgumentError  "hty is not a substitution"))
  in
  match result with
  | Ok ht -> 
    Log.debug (fun m -> m "@[Simplfied %a@]" Pretty.pp_header_type_raw hty);
    Log.debug (fun m -> m "@[Resulting hty %a@]" Pretty.pp_header_type_raw ht);
    ht
  | Error (`FieldAccessError e)
  | Error (`InvalidArgumentError e) -> 
    Log.debug(fun m -> m "Error: %s" e);
    hty 