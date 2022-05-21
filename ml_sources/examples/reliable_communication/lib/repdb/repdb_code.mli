open !Ast

val init_leader : 'a serializer -> saddr -> saddr -> unit
val init_follower : 'a serializer -> saddr -> saddr -> saddr -> unit
val init_client_leader_proxy : 'a serializer -> saddr -> saddr ->
  (string -> 'a -> unit) * (string -> 'a option)
val init_client_follower_proxy : 'a serializer -> saddr -> saddr ->
  (string -> 'a option)
