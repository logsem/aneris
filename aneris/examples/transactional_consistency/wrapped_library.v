From aneris.aneris_lang Require Import ast.
From aneris.examples.transactional_consistency Require Import code_api.

Definition start_emit_event : val := #"St".

Definition wrap_start (start : val) : val := 
  λ: "cst_wrapped" "k" "v", 
  let: "cst" := Snd "cst_wrapped" in
  let: "tag" := ast.Fresh start_emit_event in
  let: "cst_new" := start "cst" in 
  ("tag", "cst_new").

Definition read_emit_event : val :=
  λ: "tag" "key" "vo", ("tag", (#"Rd", ("key", "vo"))).

Definition wrap_read (read : val) : val := 
  λ: "cst_wrapped" "k", 
  let: "tag" := Fst "cst_wrapped" in
  let: "cst" := Snd "cst_wrapped" in
  let: "vo" := read "cst" "k" in 
  Emit (read_emit_event "tag" "k" "vo")
  ;;
  "vo".

Definition write_emit_event : val :=
  λ: "tag" "key" "v", ("tag", (#"Wr", ("key", "v"))).

Definition wrap_write (write : val) : val := 
  λ: "cst_wrapped" "k" "v", 
  let: "tag" := Fst "cst_wrapped" in
  let: "cst" := Snd "cst_wrapped" in
  write "cst" "k" "v" 
  ;; 
  Emit (write_emit_event "tag" "k" "v").

Definition commit_emit_event : val :=
  λ: "tag" "b", ("tag", (#"Cm", "b")).

Definition wrap_commit (commit : val) : val := 
  λ: "cst_wrapped" "k" "v", 
  let: "tag" := Fst "cst_wrapped" in
  let: "cst" := Snd "cst_wrapped" in
  let: "cst_bool" := commit "cst" in 
  let: "cst_new" := Fst "cst_bool" in
  let: "bool" := Snd "cst_bool" in 
  Emit (commit_emit_event "tag" "k" "v")
  ;; 
  ((#"", "cst_new"), "bool").
  
Definition wrap_init_client_proxy (init : serializer → val) 
(ser : serializer) : val := 
  λ: "clt_addr" "srv_addr",
  let: "cst" := init ser "clt_addr" "srv_addr" in 
  (#"", "cst").
  
Global Instance KVS_wrapped_api (lib : KVS_transaction_api) :
KVS_transaction_api :=
  {|
    TC_init_server := TC_init_server;
    TC_start := wrap_start TC_start;
    TC_read := wrap_read TC_read;
    TC_write := wrap_write TC_write;
    TC_commit := wrap_commit TC_commit;
    TC_init_client_proxy := wrap_init_client_proxy TC_init_client_proxy;
  |}.