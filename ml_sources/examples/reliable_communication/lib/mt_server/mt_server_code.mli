open Ast

val run_server : 'repl serializer -> 'req serializer ->
  saddr -> ('req -> 'repl) -> unit

val init_client_proxy : 'req serializer -> 'repl serializer ->
  saddr -> saddr -> ('req -> 'repl)
