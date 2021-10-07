open Core_kernel
open Syntax

module InstanceMap : Map.S with type Key.t = Instance.t

type versions = int InstanceMap.t

type ssa_program =
  { command : command;
    header_table : HeaderTable.t;
    input_type : HeapType.t;
    output_type : HeapType.t
  }

type version_binding =
  | NopBind
  | VersionBind of versions

type version_context = version_binding list

val init_versions : HeaderTable.t -> int -> versions

val append_version : string -> int -> string

val get_max_versions : versions -> command -> int InstanceMap.t

val mk_versioned_inst : Instance.t -> int -> Instance.t

val command_to_ssa :
  HeaderTable.t ->
  versions ->
  versions ->
  command ->
  (command * versions, string) result

(** [type_to_ssa header_table max_versions versions ctx vctx header_type]
    transforms [header_type] into SSA. [max_versions] is a mapping from instance
    names to the maximum version created by the program. [versions] is the
    initial mapping from instance names to versions. [ctx] is the variable
    context. [vctx] is a context mapping binders to versions. *)
val heap_type_to_ssa :
  (* HeaderTable.t -> *)
  int InstanceMap.t ->
  versions ->
  Env.context ->
  version_context ->
  HeapType.t ->
  HeapType.t * versions

val header_table_to_ssa : HeaderTable.t -> versions -> HeaderTable.t

val to_ssa :
  HeaderTable.t ->
  command ->
  string * HeapType.t ->
  HeapType.t ->
  (ssa_program, string) result
