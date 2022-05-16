open Ast

  type dlock
  val dlock_start_service : saddr -> 'a
  val dlock_subscribe_client : saddr -> saddr -> dlock
  val dlock_acquire : dlock -> unit
  val dlock_release : dlock -> unit
