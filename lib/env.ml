open Core_kernel
open Syntax

type binding =
  | NameBind
  | VarBind of HeapType.t
[@@deriving sexp]

type context = (string * binding) list

let add_binding (ctx : context) (x : string) (binding : binding) =
  (x, binding) :: ctx

let rec is_name_bound (ctx : (string * 'a) list) (x : string) : bool =
  match ctx with
  | [] -> false
  | (name, _) :: ys -> String.(name = x) || is_name_bound ys x

let rec pick_fresh_name_f ctx ~f x =
  if is_name_bound ctx x then
    pick_fresh_name_f ctx ~f (f x)
  else
    x

let pick_fresh_name (ctx : context) (x : string) =
  pick_fresh_name_f ctx ~f:(fun s -> s ^ "'") x
  (* if is_name_bound ctx x then
    pick_fresh_name ctx (x ^ "'")
  else
    x *)

let index_to_binding (ctx : context) (n : int) =
  match List.nth ctx n with
  | Some binding -> Ok binding
  | None ->
    Error
      (`VariableLookupError
        (Fmt.str "@[<v>Variable lookup failure (Index %d >= context size %d)@]"
           n (List.length ctx)))

let index_to_name (ctx : context) (n : int) =
  index_to_binding ctx n |> Result.map ~f:(fun (name, _) -> name)

let index_to_name_exn (ctx : context) (n : int) =
  match index_to_name ctx n with
  | Ok x -> x
  | Error (`VariableLookupError e) -> failwith e

let rec name_to_index (ctx : context) (x : string) =
  let open Result.Let_syntax in
  match ctx with
  | [] ->
    Error
      (`IdentifierUnboundError (Printf.sprintf "Identifier %s is unbound" x))
  | (name, _) :: rest ->
    if String.(name = x) then
      Ok 0
    else
      let%map index = name_to_index rest x in
      1 + index

let name_to_index_exn (ctx : context) (x : string) =
  match name_to_index ctx x with
  | Ok index -> index
  | Error (`IdentifierUnboundError e) -> failwith e
