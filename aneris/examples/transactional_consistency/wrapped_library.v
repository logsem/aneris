From aneris.aneris_lang Require Import ast.
From aneris.examples.transactional_consistency Require Import code_api.

Definition start_emit_event : val := 
  λ: "cst", ("cst", #"St").

Definition wrap_start (start : val) : val := 
  λ: "cst", 
  start "cst" ;;
  Emit (start_emit_event "cst") ;;
  #().

Definition read_emit_event : val :=
  λ: "cst" "key" "vo", ("cst", (#"Rd", ("key", "vo"))).

Definition wrap_read (read : val) : val := 
  λ: "cst" "k", 
  let: "vo" := read "cst" "k" in 
  Emit (read_emit_event "cst" "k" "vo") ;;
  "vo".

Definition write_emit_event : val :=
  λ: "cst" "key" "v", ("cst", (#"Wr", ("key", "v"))).

Definition wrap_write (write : val) : val := 
  λ: "cst" "k" "v", 
  Emit (write_emit_event "cst" "k" "v") ;;
  write "cst" "k" "v".

Definition commit_emit_event : val :=
  λ: "cst" "b", ("cst", (#"Cm", "b")).

Definition wrap_commit (commit : val) : val := 
  λ: "cst", 
  let: "b" := commit "cst" in 
  Emit (commit_emit_event "cst" "b") ;; 
  "b".
  
Global Instance KVS_wrapped_api (lib : KVS_transaction_api) :
KVS_transaction_api :=
  {|
    TC_init_server := TC_init_server;
    TC_start := wrap_start TC_start;
    TC_read := wrap_read TC_read;
    TC_write := wrap_write TC_write;
    TC_commit := wrap_commit TC_commit;
    TC_init_client_proxy := TC_init_client_proxy;
  |}.