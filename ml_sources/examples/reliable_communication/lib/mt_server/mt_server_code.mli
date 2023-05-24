open Ast

type ('a, 'b) rpc

val run_server : 'repl serializer -> 'req serializer ->
  saddr -> ('req -> 'repl) -> unit

val run_server_opt : 'repl serializer -> 'req serializer ->
  saddr -> ('req option -> 'repl option) -> unit

val make_request : ('req, 'repl) rpc -> ('req -> 'repl)

val init_client_proxy : 'req serializer -> 'repl serializer ->
  saddr -> saddr -> ('req, 'repl) rpc
