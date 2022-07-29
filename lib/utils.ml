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
      match sequence_error xs with
      | Error _ as e -> e
      | Ok ys -> Ok (y :: ys) ) )

let bin_of_int (d : int) =
  if d < 0 then invalid_arg "bin_of_int" else
  if d = 0 then "0" else
  let rec aux acc d =
    if d = 0 then acc else
    aux (string_of_int (d land 1) :: acc) (d lsr 1)
  in
  String.concat ~sep:"" (aux [] d)
