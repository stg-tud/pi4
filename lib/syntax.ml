open Core_kernel

type var = int [@@deriving compare, sexp]

module Declaration = struct
  type field =
    { name : string;
      typ : int
    }
  [@@deriving compare, sexp]

  type t =
    | HeaderTypeDecl of
        { name : string;
          fields : field list
        }
    | HeaderInstanceDecl of
        { name : string;
          type_name : string
        }
  [@@deriving compare, sexp]
end

module Instance = struct
  module T = struct
    type t =
      { name : string;
        fields : Declaration.field list
      }
    [@@deriving compare, sexp]
  end

  include T
  include Comparator.Make (T)

  let field_exists inst field_name =
    List.exists inst.fields ~f:(fun field -> String.(field.name = field_name))

  let field_bounds inst field =
    let rec aux (fields : Declaration.field list) field offset =
      match fields with
      | [] ->
        Error
          (`FieldAccessError
            (Printf.sprintf "Field '%s' does not exist on instance '%s'" field
               inst.name))
      | f :: rest ->
        if String.(f.name = field) then Ok (offset, offset + f.typ)
        else aux rest field (offset + f.typ)
    in
    aux inst.fields field 0

  let field_bounds_exn inst field =
    match field_bounds inst field with
    | Ok bounds -> bounds
    | Error (`FieldAccessError e) -> failwith e

  let sizeof inst =
    List.fold inst.fields ~init:0 ~f:(fun acc field -> acc + field.typ)

  let find_field inst field_name =
    List.find inst.fields ~f:(fun field -> String.(field.name = field_name))

  let get_field inst field_name =
    find_field inst field_name
    |> Result.of_option
         ~error:
           (`FieldAccessError
             (Printf.sprintf "Field '%s' is not defined on instance '%s'"
                field_name inst.name))

  let slice_matches_field inst left right =
    let _, bounds =
      List.fold inst.fields ~init:(0, Int.Map.empty)
        ~f:(fun (total, acc) field ->
          let new_total = total + field.typ in
          (new_total, Map.set acc ~key:total ~data:new_total))
    in
    let size = sizeof inst in
    let maybe_right_bound_matches =
      Int.Map.find bounds left |> Option.map ~f:(fun r -> r = right)
    in
    (left = 0 && right = size)
    || Option.value maybe_right_bound_matches ~default:false

  let equals = [%compare.equal: t]
end

module HeaderTable = struct
  type t = Declaration.field list String.Map.t

  let empty = String.Map.empty

  let find_instance inst_str header_table =
    Map.find header_table inst_str
    |> Option.map ~f:(fun fields -> Instance.{ name = inst_str; fields })

  let to_string header_table =
    header_table
    |> String.Map.fold ~init:"" ~f:(fun ~key:inst ~data:fields acc ->
           let fields_string =
             fields
             |> List.map ~f:(fun (field : Declaration.field) ->
                    Printf.sprintf "(%s,%d)" field.name field.typ)
             |> List.fold ~init:"" ~f:(fun acc field -> acc ^ field)
           in
           Printf.sprintf "%s\n%s -> [%s]" acc inst fields_string)

  let lookup_instance inst_str header_table =
    find_instance inst_str header_table
    |> Result.of_option
         ~error:
           (`LookupError
             (Fmt.str
                "@[<v>Could not look up instance '%s' from header table %s.@]"
                inst_str (to_string header_table)))

  let lookup_instance_exn inst header_table =
    match lookup_instance inst header_table with
    | Ok inst -> inst
    | Error (`LookupError e) -> failwith e

  let populate (inst_list : Instance.t list) =
    List.fold inst_list ~init:String.Map.empty ~f:(fun acc inst ->
        String.Map.set ~key:inst.name ~data:inst.fields acc)

  let of_decls (decls : Declaration.t list) =
    let types =
      List.fold decls ~init:String.Map.empty ~f:(fun acc decl ->
          match decl with
          | HeaderTypeDecl { name; fields } ->
            Map.set acc ~key:name ~data:fields
          | _ -> acc)
    in
    List.fold decls ~init:String.Map.empty ~f:(fun acc decl ->
        match decl with
        | HeaderInstanceDecl { name; type_name } ->
          let typ = String.Map.find_exn types type_name in
          Map.set acc ~key:name ~data:typ
        | _ -> acc)

  let to_list header_table =
    String.Map.to_alist header_table ~key_order:`Increasing
    |> List.map ~f:(fun (inst_name, fields) ->
           Instance.{ name = inst_name; fields })

  let max_header_size header_table =
    let ht_list = to_list header_table in
    let rec get_size hl =
      match hl with
      | a :: t -> Instance.sizeof a + get_size t
      | [] -> 0
    in
    get_size ht_list
end

type packet =
  | PktIn
  | PktOut
[@@deriving compare, sexp]

module Bit = struct
  type t =
    | Zero
    | One
    | B of int
  [@@deriving compare, sexp]

  let bit_list_of_string bv_str =
    String.fold bv_str ~init:[] ~f:(fun acc -> function
      | '1' -> One :: acc
      | '0' -> Zero :: acc
      | _ as c -> failwith (Printf.sprintf "Unrecognized character '%c'" c))
    |> List.rev
end

module BitVector = struct
  type t =
    | Nil
    | Cons of (Bit.t * t)
  [@@deriving compare, sexp]

  let rec sizeof = function Nil -> 0 | Cons (_, bs) -> 1 + sizeof bs

  let rec concat (bv1 : t) (bv2 : t) =
    match bv1 with Nil -> bv2 | Cons (b, bs) -> Cons (b, concat bs bv2)

  let of_bit_list bits =
    List.rev bits |> List.fold ~init:Nil ~f:(fun acc b -> Cons (b, acc))

  let of_bit_str bv_str = of_bit_list (Bit.bit_list_of_string bv_str)

  let bitstr_of_hex_char c =
    match c with
    | '0' -> "0000"
    | '1' -> "0001"
    | '2' -> "0010"
    | '3' -> "0011"
    | '4' -> "0100"
    | '5' -> "0101"
    | '6' -> "0110"
    | '7' -> "0111"
    | '8' -> "1000"
    | '9' -> "1001"
    | 'a' | 'A' -> "1010"
    | 'b' | 'B' -> "1011"
    | 'c' | 'C' -> "1100"
    | 'd' | 'D' -> "1101"
    | 'e' | 'E' -> "1110"
    | 'f' | 'F' -> "1111"
    | _ -> failwith (Printf.sprintf "Unrecognized character '%c'" c)

  let of_hex_str hex_str =
    String.concat_map ~f:bitstr_of_hex_char hex_str |> of_bit_str

  let zero size = of_bit_list (List.init size ~f:(fun _ -> Bit.Zero))
end

module Sliceable = struct
  type t =
    | Packet of var * packet
    | Instance of var * Instance.t
  [@@deriving compare, sexp]
end

module Expression = struct
  (* All arith expressions evaluate to natural numbers *)
  type arith =
    | Num of int (* n *)
    | Length of var * packet (* |x.p| *)
    | Plus of arith * arith (* t1 + t2 where t1 and t2 must have natural number types *)
  [@@deriving compare, sexp]

  type bv =
    | Minus of bv * bv (* t1 - t2 where t1 and t2 must have bitvector types *)
    | Bv of BitVector.t (* bv *)
    | Concat of bv * bv (* t1 @ t2 where t1 and t2 must have bitvector types *)
    | Slice of Sliceable.t * int * int (* x.p[hi:lo] or x.h[hi:lo] *)
    | Packet of var * packet (* x.p *)
  [@@deriving compare, sexp]

  type t =
    | ArithExpr of arith
    | BvExpr of bv
  [@@deriving compare, sexp]

  let field_to_slice inst field binder =
    let open Result.Let_syntax in
    let%map l, r = Instance.field_bounds inst field in
    Slice (Instance (binder, inst), l, r)

  let field_to_slice_exn inst field binder =
    match field_to_slice inst field binder with
    | Ok slice -> slice
    | Error (`FieldAccessError e) -> failwith e

  let instance_slice x inst = Slice (Instance (x, inst), 0, Instance.sizeof inst)
  let bit_access sliceable idx = BvExpr (Slice (sliceable, idx, idx + 1))
end

(* φ *)
module Formula = struct
  type t =
    | True (* true *)
    | False (* false *)
    | IsValid of var * Instance.t (* x.ι.valid *)
    | Eq of Expression.t * Expression.t (* e = e *)
    | Gt of Expression.t * Expression.t (* e > e *)
    | Neg of t (* ¬φ *)
    | And of t * t (* φ ∧ φ *)
    | Or of t * t (* φ | φ *)
    | Implies of t * t (* φ ⟹ φ / Q: Not in formal definition? *)
  [@@deriving compare, sexp]

  let ands forms = List.fold forms ~init:True ~f:(fun e1 e2 -> And (e1, e2))
end

(* τ *)
module HeapType = struct
  type t =
    | Nothing (* ⌀ *)
    | Top (* ⊤ *)
    | Sigma of string * t * t (* Σx:τ.τ *)
    | Choice of t * t (* τ + τ *)
    | Refinement of string * t * Formula.t (* {x : τ | φ } *)
    | Substitution of t * string * t (* τ[x ↦ τ] *)
  [@@deriving compare, sexp]

  let empty (header_table : HeaderTable.t) (x : string) =
    let open Formula in
    let pred =
      HeaderTable.to_list header_table
      |> List.fold ~init:True ~f:(fun acc inst ->
             And (acc, Neg (IsValid (0, inst))))
    in
    Refinement (x, Top, pred)

  let instance (inst : Instance.t) (header_table : HeaderTable.t) (x : string) =
    let open Formula in
    let pred =
      HeaderTable.to_list header_table
      |> List.filter ~f:(fun elem -> String.(elem.name <> inst.name))
      |> List.fold
           ~init:(IsValid (0, inst))
           ~f:(fun acc elem -> And (acc, Neg (IsValid (0, elem))))
    in
    Refinement (x, Top, pred)

  let weak_instance (inst : Instance.t) (x : string) =
    let open Formula in
    Refinement (x, Top, IsValid (0, inst))

  let pair (i1 : Instance.t) (i2 : Instance.t) (x : string)
      (header_table : HeaderTable.t) =
    let open Formula in
    let valid = And (IsValid (0, i1), IsValid (0, i2)) in
    let e =
      HeaderTable.to_list header_table
      |> List.fold ~init:valid ~f:(fun acc inst ->
             if Instance.equals i1 inst || Instance.equals i2 inst then acc
             else And (acc, Neg (IsValid (0, inst))))
    in
    Refinement (x, Top, e)
end

type size =
  | StaticSize of int
  | MaxLen
[@@deriving compare, sexp]

type pi_type = Pi of string * HeapType.t * HeapType.t
[@@deriving compare, sexp]

type ty =
  | Bool
  | BitVec of size
  | Nat
[@@deriving compare, sexp]

module Command = struct
  type t =
    | Extract of Instance.t
    | If of Formula.t * t * t
    | Assign of Instance.t * int * int * Expression.t
    | Remit of Instance.t
    | Remove of Instance.t
    | Reset
    | Seq of t * t
    | Skip
    | Add of Instance.t
    | Ascription of t * string * HeapType.t * HeapType.t
  [@@deriving compare, sexp]
end

(* P *)
module Program = struct
  type t =
    { declarations : Declaration.t list;
      command : Command.t
    }
  [@@deriving compare, sexp]
end

(* Smart Constructors *)

let bv_l l = Expression.Bv (BitVector.of_bit_list l)
let bv_s s = Expression.Bv (BitVector.of_bit_str s)
let bv_x x = Expression.Bv (BitVector.of_hex_str x)

let pkt_eq ((i, p) : int * packet) (y : Expression.t) (y_len : int) =
  let open Expression in
  let s_len = Length (i, p) in
  Formula.And
    ( Eq (BvExpr (Slice (Packet (i, p), 0, y_len)), y),
      Eq (ArithExpr s_len, ArithExpr (Num y_len)) )

let pkt_eq_s (s : int * packet) (bv : string) =
  pkt_eq s (BvExpr (bv_s bv)) (String.length bv)

let pktin_slice (binder : var) (left : int) (right : int) =
  Expression.BvExpr (Slice (Packet (binder, PktIn), left, right))

let packet_equality (x : var) (y : var) (packet : packet) =
  Formula.And
    ( Eq (ArithExpr (Length (x, packet)), ArithExpr (Length (y, packet))),
      Eq (BvExpr (Packet (x, packet)), BvExpr (Packet (y, packet))) )

let inst_equality (idx_x : var) (idx_y : var) (insts : Instance.t list) =
  List.fold insts ~init:Formula.True ~f:(fun acc inst ->
      let slice var =
        Expression.Slice (Instance (var, inst), 0, Instance.sizeof inst)
      in
      let eq =
        Formula.(
          Or
            ( And (Neg (IsValid (idx_x, inst)), Neg (IsValid (idx_y, inst))),
              And
                ( And (IsValid (idx_x, inst), IsValid (idx_y, inst)),
                  Eq (BvExpr (slice idx_x), BvExpr (slice idx_y)) ) ))
      in
      And (acc, eq))

let heap_equality (idx_x : var) (idx_y : var) (header_table : HeaderTable.t) =
  let insts = HeaderTable.to_list header_table in
  Formula.And
    ( And (packet_equality idx_x idx_y PktIn, packet_equality idx_x idx_y PktOut),
      inst_equality idx_x idx_y insts )

module Annotation = struct
  type annotation_body =
    | Reset
    | Block of string
    | TypedBlock of annotation_body * pi_type
    | Sequence of annotation_body * annotation_body
  [@@deriving compare, sexp]

  type t = TypeAnnotation of annotation_body * pi_type
  [@@deriving compare, sexp]
end
