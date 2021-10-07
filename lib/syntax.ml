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
  type t =
    { name : string;
      fields : Declaration.field list
    }
  [@@deriving compare, sexp]

  let field_exists inst field_name =
    List.exists inst.fields ~f:(fun field -> String.(field.name = field_name))

  let field_bounds inst field =
    let rec aux (fields : Declaration.field list) field offset =
      match fields with
      | [] ->
        Error
          (Printf.sprintf "Field '%s' does not exist on instance '%s'" field
             inst.name)
      | f :: rest ->
        if String.(f.name = field) then
          Ok (offset, offset + f.typ)
        else
          aux rest field (offset + f.typ)
    in
    aux inst.fields field 0

  let sizeof inst =
    List.fold inst.fields ~init:0 ~f:(fun acc field -> acc + field.typ)

  let find_field inst field_name =
    List.find inst.fields ~f:(fun field -> String.(field.name = field_name))

  let get_field inst field_name =
    find_field inst field_name
    |> Result.of_option
         ~error:
           (Printf.sprintf "Field '%s' is not defined on instance '%s'"
              field_name inst.name)

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
           (Fmt.str
              "@[<v>Could not look up instance '%s' from header table %s.@]"
              inst_str (to_string header_table))

  let lookup_instance_exn inst header_table =
    lookup_instance inst header_table |> Result.ok_or_failwith

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

  let rec sizeof = function
    | Nil -> 0
    | Cons (_, bs) -> 1 + sizeof bs

  let rec concat (bv1 : t) (bv2 : t) =
    match bv1 with
    | Nil -> bv2
    | Cons (b, bs) -> Cons (b, concat bs bv2)

  let of_bit_list bits =
    List.rev bits |> List.fold ~init:Nil ~f:(fun acc b -> Cons (b, acc))

  let of_bit_str bv_str = of_bit_list (Bit.bit_list_of_string bv_str)

  let bv_of_hex_char c =
    match c with
    | '0' -> of_bit_str "0000"
    | '1' -> of_bit_str "0001"
    | '2' -> of_bit_str "0010"
    | '3' -> of_bit_str "0011"
    | '4' -> of_bit_str "0100"
    | '5' -> of_bit_str "0101"
    | '6' -> of_bit_str "0110"
    | '7' -> of_bit_str "0111"
    | '8' -> of_bit_str "1000"
    | '9' -> of_bit_str "1001"
    | 'a' | 'A' -> of_bit_str "1010"
    | 'b' | 'B' -> of_bit_str "1011"
    | 'c' | 'C' -> of_bit_str "1100"
    | 'd' | 'D'-> of_bit_str "1101"
    | 'e' | 'E'-> of_bit_str "1110"
    | 'f' | 'F'-> of_bit_str "1110"
    | _ -> failwith (Printf.sprintf "Unrecognized character '%c'" c)

  let of_hex_str hex_str =
    String.fold hex_str ~init:Nil ~f:(fun acc c ->
        concat acc (bv_of_hex_char c))
end

module Sliceable = struct
  type t =
    | Packet of var * packet
    | Instance of var * Instance.t
  [@@deriving compare, sexp]
end

module Term = struct
  type t =
    | Num of int (* n *)
    | Length of var * packet (* |x.p| *)
    | Plus of t * t
    (* t1 + t2 where t1 and t2 must have natural number types *)
    | Minus of t * t (* t1 - t2 where t1 and t2 must have bitvector types *)
    | Bv of BitVector.t (* bv *)
    | Concat of t * t
    (* t1 @ t2 where t1 and t2 must have bitvector types *)
    | Slice of Sliceable.t * int * int (* x.p[hi:lo] or x.h[hi:lo] *)
    | Packet of var * packet (* x.p *)
  [@@deriving compare, sexp]

  let field_to_slice inst field binder =
    let open Result.Let_syntax in
    let%map l, r = Instance.field_bounds inst field in
    Slice (Instance (binder, inst), l, r)

  let field_to_slice_exn inst field binder =
    field_to_slice inst field binder |> Result.ok_or_failwith

  let instance_slice x inst = Slice (Instance (x, inst), 0, Instance.sizeof inst)

  let bit_access sliceable idx = Slice (sliceable, idx, idx + 1)
end

module Expression = struct
  type t =
    | True
    | False
    | IsValid of var * Instance.t
    | TmEq of Term.t * Term.t
    | TmGt of Term.t * Term.t
    | Neg of t
    | And of t * t
    | Or of t * t
    | Implies of t * t
  [@@deriving compare, sexp]
end

module HeapType = struct
  type t =
    | Nothing
    | Empty
    | Top
    | Sigma of string * t * t
    | Choice of t * t
    | Refinement of string * t * Expression.t
    | Substitution of t * string * t
  [@@deriving compare, sexp]

  let empty (header_table : HeaderTable.t) (x : string) =
    let pred =
      HeaderTable.to_list header_table
      |> List.fold ~init:Expression.True ~f:(fun acc inst ->
             And (acc, Neg (Expression.IsValid (0, inst))))
    in
    Refinement (x, Top, pred)

  let instance (inst : Instance.t) (header_table : HeaderTable.t) (x : string) =
    let pred =
      HeaderTable.to_list header_table
      |> List.filter ~f:(fun elem -> String.(elem.name <> inst.name))
      |> List.fold
           ~init:(Expression.IsValid (0, inst))
           ~f:(fun acc elem -> And (acc, Neg (IsValid (0, elem))))
    in
    Refinement (x, Top, pred)

  let weak_instance (inst : Instance.t) (x : string) =
    Refinement (x, Top, Expression.IsValid (0, inst))

  let pair (i1 : Instance.t) (i2 : Instance.t) (x : string)
      (header_table : HeaderTable.t) =
    let valid = Expression.(And (IsValid (0, i1), IsValid (0, i2))) in
    let e =
      HeaderTable.to_list header_table
      |> List.fold ~init:valid ~f:(fun acc inst ->
             if Instance.equals i1 inst || Instance.equals i2 inst then
               acc
             else
               And (acc, Neg (IsValid (0, inst))))
    in
    Refinement (x, Top, e)
end

type size =
  | StaticSize of int
  | MaxLen
[@@deriving compare, sexp]

type ty =
  | Bool
  | BitVec of size
  | Nat
  | Pi of string * HeapType.t * HeapType.t
[@@deriving compare, sexp]

type command =
  | Extract of Instance.t
  | If of Expression.t * command * command
  | Assign of Instance.t * int * int * Term.t
  | Remit of Instance.t
  | Reset
  | Seq of command * command
  | Skip
  | Add of Instance.t
  | Ascription of command * string * HeapType.t * HeapType.t
[@@deriving compare, sexp]

module Program = struct
  type t =
    { declarations : Declaration.t list;
      command : command
    }
  [@@deriving compare, sexp]
end

let ensure_pi (ty : ty) =
  match ty with
  | Pi (x, hty1, hty2) -> Ok (x, hty1, hty2)
  | _ -> Error (Printf.sprintf "Expected a function type.")

(* Smart Constructors *)

let bv_l l = Term.Bv (BitVector.of_bit_list l)

let bv_s s = Bit.bit_list_of_string s |> bv_l

let bv_x x = Term.Bv (BitVector.of_hex_str x)

let pkt_eq ((i, p) : int * packet) (y : Term.t) (y_len : int) =
  let open Term in
  let s_len = Length (i, p) in
  Expression.And
    (TmEq (Slice (Packet (i, p), 0, y_len), y), TmEq (s_len, Num y_len))

let pkt_eq_s (s : int * packet) (bv : string) =
  pkt_eq s (bv_s bv) (String.length bv)

let pktin_slice (binder : var) (left : int) (right : int) =
  let open Term in
  Slice (Packet (binder, PktIn), left, right)

let packet_equality (packet : packet) (idx_x : var) (idx_y : var) =
  Expression.And
    ( TmEq (Length (idx_x, packet), Length (idx_y, packet)),
      TmEq (Packet (idx_x, packet), Packet (idx_y, packet)) )

let inst_equality (idx_x : var) (idx_y : var) (insts : Instance.t list) =
  List.fold insts ~init:Expression.True ~f:(fun acc inst ->
      let slice var =
        Term.Slice (Instance (var, inst), 0, Instance.sizeof inst)
      in
      let eq =
        (* Expression.( Or ( And (Neg (IsValid (idx_y, inst)), Neg (IsValid
           (idx_x, inst))), And ( IsValid (idx_y, inst), And (IsValid (idx_x,
           inst), TmEq (slice idx_y, slice idx_x)) ) )) *)
        Expression.(
          And
            ( Or
                ( And (Neg (IsValid (idx_x, inst)), Neg (IsValid (idx_y, inst))),
                  And (IsValid (idx_x, inst), IsValid (idx_y, inst)) ),
              TmEq (slice idx_y, slice idx_x) ))
      in
      And (acc, eq))

let heap_equality (idx_x : var) (idx_y : var) (header_table : HeaderTable.t) =
  let insts = HeaderTable.to_list header_table in
  Expression.And
    ( And (packet_equality PktIn idx_x idx_y, packet_equality PktOut idx_x idx_y),
      inst_equality idx_x idx_y insts )
