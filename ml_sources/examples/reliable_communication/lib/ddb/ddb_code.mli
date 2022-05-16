open Ast

val install_proxy :
  'a serializer -> saddr -> saddr ->
  ((string -> 'a -> unit) * (string -> 'a option))

val init_server : 'a serializer -> saddr -> unit
