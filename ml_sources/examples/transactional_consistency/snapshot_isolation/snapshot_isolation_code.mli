
open Ast
type 'a connection_state

val init_server : 'a serializer -> saddr -> unit
val start : 'a connection_state -> unit
val read : 'a connection_state -> string -> 'a option
val write : 'a connection_state -> string -> 'a -> unit
val commit : 'a connection_state -> bool
val init_client_proxy : 'a serializer -> saddr -> saddr -> 'a connection_state
