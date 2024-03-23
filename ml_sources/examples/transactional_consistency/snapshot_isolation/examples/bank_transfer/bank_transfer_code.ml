open !Ast
open Serialization_code
open Snapshot_isolation_code
open Util_code

let transaction1 cst amount src dst =
  start cst;
  let vsrc = read cst src in
  if (amount <= vsrc) then (
    write cst src (vsrc - amount);
    let vdst = read cst dst in
    write cst dst (vdst + amount)
  )
  commitU cst
