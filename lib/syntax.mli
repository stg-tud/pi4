open Core_kernel

type var = int [@@deriving compare]

module Declaration : sig
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

module Instance : sig
  type t =
    { name : string;
      fields : Declaration.field list
    }
  [@@deriving compare, sexp]

  val field_exists : t -> string -> bool

  val field_bounds : t -> string -> (int * int, string) result

  val find_field : t -> string -> Declaration.field option

  val get_field : t -> string -> (Declaration.field, string) result

  val sizeof : t -> int

  val slice_matches_field : t -> int -> int -> bool
end

module HeaderTable : sig
  type t = Declaration.field list String.Map.t

  val empty : t

  val find_instance : string -> t -> Instance.t option

  val lookup_instance : string -> t -> (Instance.t, string) result

  val lookup_instance_exn : string -> t -> Instance.t

  val populate : Instance.t list -> t

  val of_decls : Declaration.t list -> t

  val to_list : t -> Instance.t list
end

type packet =
  | PktIn
  | PktOut
[@@deriving compare, sexp]

module Bit : sig
  type t =
    | Zero
    | One
    | B of int
  [@@deriving compare, sexp]

  val bit_list_of_string : string -> t list
end

module BitVector : sig
  type t =
    | Nil
    | Cons of (Bit.t * t)
  [@@deriving compare, sexp]

  val sizeof : t -> int

  val concat : t -> t -> t

  val of_hex_str : string -> t

  val of_bit_str : string -> t

  val of_bit_list : Bit.t list -> t

  val zero : int -> t
end

module Sliceable : sig
  type t =
    | Packet of var * packet
    | Instance of var * Instance.t
  [@@deriving compare, sexp]
end

module Expression : sig
  type arith =
    | Num of int (* n *)
    | Length of var * packet (* |x.p| *)
    | Plus of arith * arith
  (* t1 + t2 where t1 and t2 must have natural number types *)
  [@@deriving compare, sexp]

  type bv =
    | Minus of bv * bv (* t1 - t2 where t1 and t2 must have bitvector types *)
    | Bv of BitVector.t (* bv *)
    | Concat of bv * bv
    (* t1 @ t2 where t1 and t2 must have bitvector types *)
    | Slice of Sliceable.t * int * int (* x.p[hi:lo] or x.h[hi:lo] *)
    | Packet of var * packet
  (* x.p *)
  [@@deriving compare, sexp]

  type t =
    | ArithExpr of arith
    | BvExpr of bv
  [@@deriving compare, sexp]

  val field_to_slice : Instance.t -> string -> var -> (bv, string) result

  val field_to_slice_exn : Instance.t -> string -> var -> bv

  val instance_slice : var -> Instance.t -> bv

  val bit_access : Sliceable.t -> var -> t
end

module Formula : sig
  type t =
    | True
    | False
    | IsValid of var * Instance.t
    | Eq of Expression.t * Expression.t
    | Gt of Expression.t * Expression.t
    | Neg of t
    | And of t * t
    | Or of t * t
    | Implies of t * t
  [@@deriving compare, sexp]

  val ands : t list -> t
end

module HeapType : sig
  type t =
    | Nothing
    | Top
    | Sigma of string * t * t
    | Choice of t * t
    | Refinement of string * t * Formula.t
    | Substitution of t * string * t
  [@@deriving compare, sexp]

  val empty : HeaderTable.t -> string -> t

  val instance : Instance.t -> HeaderTable.t -> string -> t

  val weak_instance : Instance.t -> string -> t

  val pair : Instance.t -> Instance.t -> string -> HeaderTable.t -> t
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
  | If of Formula.t * command * command
  | Assign of Instance.t * int * int * Expression.t
  | Remit of Instance.t
  | Reset
  | Seq of command * command
  | Skip
  | Add of Instance.t
  | Ascription of command * string * HeapType.t * HeapType.t
[@@deriving compare, sexp]

module Program : sig
  type t =
    { declarations : Declaration.t list;
      command : command
    }
  [@@deriving compare, sexp]
end

val ensure_pi : ty -> (string * HeapType.t * HeapType.t, string) result

(* Smart Constructors *)

val bv_l : Bit.t list -> Expression.bv

val bv_s : string -> Expression.bv

val bv_x : string -> Expression.bv

val pkt_eq_s : var * packet -> string -> Formula.t

val pktin_slice : var -> int -> int -> Expression.t

val packet_equality : var -> var -> packet -> Formula.t

val inst_equality : var -> var -> Instance.t list -> Formula.t

val heap_equality : var -> var -> HeaderTable.t -> Formula.t
