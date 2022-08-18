open Core

let memoize_string_count f =
  let memoize () =
    let vars = ref String.Map.empty in
    fun x ->
      let x, _ = String.lsplit2 x ~on:'\'' |> Option.value ~default:(x, "") in
      let x, _ = String.lsplit2 x ~on:'_' |> Option.value ~default:(x, "") in
      let count = String.Map.find !vars x |> Option.value ~default:0 in
      vars := String.Map.set !vars ~key:x ~data:(count + 1);
      Printf.sprintf "%s_%d" x count
  in
  let memo = memoize () in
  f memo

let apply f x = f x

let rec sequence_error = function
  | [] -> Ok []
  | x :: xs -> (
    match x with
    | Error _ as e -> e
    | Ok y -> (
      match sequence_error xs with Error _ as e -> e | Ok ys -> Ok (y :: ys)))

let bin_of_int (d : int) =
  if d < 0 then invalid_arg "bin_of_int"
  else if d = 0 then "0"
  else
    let rec aux acc d =
      if d = 0 then acc else aux (string_of_int (d land 1) :: acc) (d lsr 1)
    in
    String.concat ~sep:"" (aux [] d)

let min_bit_width n =
  let open Owl_base in
  int_of_float (Maths.log2 (float_of_int n) +. 1.)

let count_commands command =
  let open Syntax.Command in
  let rec count_aux command acc =
    match command with
    | Extract _
    | Assign (_, _, _, _)
    | Remit _ | Remove _ | Reset | Skip | Add _ ->
      acc + 1
    | If (_, c1, c2)
    | Seq (c1, c2) ->
      let n1 = count_aux c1 acc in
      (count_aux c2 n1) + 1
    | Ascription (c, _, _, _) -> (count_aux c acc) + 1
  in
  count_aux command 0
