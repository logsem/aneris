From aneris.aneris_lang Require Import ast.
From aneris.examples.transactional_consistency Require Import code_api.

Definition start_pre_emit_event : val := 
  λ: "cst", ("cst", #"StPre").

Definition start_post_emit_event : val := 
  λ: "cst", ("cst", #"StPost").

Definition wrap_start (start : val) : val := 
  λ: "cst", 
  let: "tag" := Fresh (start_pre_emit_event "cst") in 
  start "cst" ;;
  Emit ("tag" , start_post_emit_event "cst").

Definition read_pre_emit_event : val := 
  λ: "cst", ("cst", #"RdPre").

Definition read_post_emit_event : val :=
  λ: "cst" "key" "vo", ("cst", (#"RdPre", ("key", "vo"))).

Definition wrap_read (read : val) : val := 
  λ: "cst" "k", 
  let: "tag" := Fresh (read_pre_emit_event "cst") in
  let: "vo" := read "cst" "k" in 
  Emit ("tag" ,read_post_emit_event "cst" "k" "vo") ;;
  "vo".

Definition write_pre_emit_event : val := 
  λ: "cst", ("cst", #"WrPre").

Definition write_post_emit_event : val :=
  λ: "cst" "key" "v", ("cst", (#"WrPost", ("key", "v"))).

Definition wrap_write (write : val) : val := 
  λ: "cst" "k" "v", 
  let: "tag" := Fresh (write_pre_emit_event "cst") in 
  write "cst" "k" "v" ;;
  Emit ("tag", write_post_emit_event "cst" "k" "v").

Definition commit_pre_emit_event : val := 
  λ: "cst", ("cst", #"CmPre").

Definition commit_post_emit_event : val :=
  λ: "cst" "b", ("cst", (#"CmPost", "b")).

Definition wrap_commit (commit : val) : val := 
  λ: "cst", 
  let: "tag" := Fresh (commit_pre_emit_event "cst") in 
  let: "b" := commit "cst" in 
  Emit ("tag", commit_post_emit_event "cst" "b") ;; 
  "b".

Definition init_pre_emit_event : val := #"InPre".

Definition init_post_emit_event : val :=
  λ: "cst", ("cst", #"InitPost").

Definition wrap_init_client_proxy (init_client_proxy : serializer → val) (ser : serializer) : val := 
  λ: "sa_cli" "sa_kvs", 
  let: "tag" := Fresh (init_pre_emit_event) in 
  let: "cst" := init_client_proxy ser "sa_cli" "sa_kvs" in 
  Emit ("tag", init_post_emit_event "cst") ;; 
  "cst".
  
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