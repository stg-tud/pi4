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
end

module Sliceable : sig
  type t =
    | Packet of var * packet
    | Instance of var * Instance.t
  [@@deriving compare, sexp]
end

module Term : sig
  (* TODO: Split arithmetic and bitvector terms *)
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

  val field_to_slice : Instance.t -> string -> var -> (t, string) result

  val field_to_slice_exn : Instance.t -> string -> var -> t

  val instance_slice : var -> Instance.t -> t

  val bit_access : Sliceable.t -> var -> t
end

module Expression : sig
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

module HeapType : sig
  type t =
    | Nothing
    | Empty
    | Top
    | Sigma of string * t * t
    | Choice of t * t
    | Refinement of string * t * Expression.t
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
  | If of Expression.t * command * command
  | Assign of Instance.t * int * int * Term.t
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

val bv_l : Bit.t list -> Term.t

val bv_s : string -> Term.t

val bv_x : string -> Term.t

val pkt_eq_s : var * packet -> string -> Expression.t

val pktin_slice : var -> int -> int -> Term.t

val packet_equality : packet -> var -> var -> Expression.t

val inst_equality : var -> var -> Instance.t list -> Expression.t

val heap_equality : var -> var -> HeaderTable.t -> Expression.t
