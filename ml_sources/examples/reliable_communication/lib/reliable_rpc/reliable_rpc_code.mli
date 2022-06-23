open Ast
open List_code

type 'a embedding = ('a -> string) * (string -> 'a)
type ('a, 'b) rpc = string * ('a embedding * 'b embedding)
type handler
type chan

val implement : ('a, 'b) rpc -> (monitor -> 'a -> 'b) -> handler

val init_server_stub : saddr -> monitor -> handler alist -> unit
val init_client_stub : saddr -> saddr -> chan
val call : chan -> ('a, 'b) rpc -> 'a -> 'b
