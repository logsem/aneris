open Ast

type ('a, 'b) rcb

val run_server : 'repl serializer -> 'req serializer ->
  saddr -> ('req -> 'repl) -> unit

val make_request : ('req, 'repl) rcb -> ('req -> 'repl)

val init_client_proxy : 'req serializer -> 'repl serializer ->
  saddr -> saddr -> ('req, 'repl) rcb
