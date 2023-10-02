(* This file is automatically generated from the OCaml source file
<repository_root>/ml_sources/examples/snapshot_isolation/snapshot_isolation_code.ml *)

From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.aneris_lang.lib Require Import map_code.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.examples.reliable_communication.lib.mt_server Require Import mt_server_code.

(**  The internal state of the server  *)

Definition req_ser val_ser :=
  sum_serializer (prod_serializer string_serializer int_serializer)
  (sum_serializer unit_serializer
   (prod_serializer int_serializer
    (list_serializer (prod_serializer string_serializer val_ser)))).

Definition repl_ser val_ser :=
  sum_serializer (option_serializer val_ser)
  (sum_serializer int_serializer bool_serializer).

Definition kvs_get : val :=
  λ: "k" "kvs",
  match: map_lookup "k" "kvs" with
    NONE => []
  | SOME "vlst" => assert: (~ ("vlst" = NONE));;
                   "vlst"
  end.

Definition kvs_get_last : val :=
  λ: "kt" "kvs",
  let: "k" := Fst "kt" in
  let: "t" := Snd "kt" in
  letrec: "aux" "l" :=
    match: "l" with
      NONE => NONE
    | SOME "p" =>
        let: "_k" := Fst (Fst "p") in
        let: "v" := Fst (Snd (Fst "p")) in
        let: "tv" := Snd (Snd (Fst "p")) in
        let: "tl" := Snd "p" in
        (if: "tv" = "t"
         then  assert: #false
         else  (if: "tv" < "t"
           then  SOME "v"
           else  "aux" "tl"))
    end in
    "aux" (kvs_get "k" "kvs").

Definition update_kvs : val :=
  λ: "kvs" "cache" "tc",
  letrec: "upd" "kvs_t" "cache_t" :=
    match: "cache_t" with
      NONE => "kvs_t"
    | SOME "chl" =>
        let: "kv" := Fst "chl" in
        let: "cache_l" := Snd "chl" in
        let: "k" := Fst "kv" in
        let: "v" := Snd "kv" in
        let: "vlst" := kvs_get "k" "kvs" in
        let: "newval" := ("k", ("v", "tc")) in
        let: "newvals" := "newval" :: "vlst" in
        let: "kvs_t'" := map_insert "k" "newvals" "kvs_t" in
        "upd" "kvs_t'" "cache_l"
    end in
    "upd" "kvs" "cache".

Definition check_at_key : val :=
  λ: "k" "ts" "tc" "vlst",
  assert: ("ts" < "tc");;
  match: "vlst" with
    NONE => #true
  | SOME "l" =>
      let: "vlast" := Fst "l" in
      let: "_hd" := Snd "l" in
      let: "_k" := Fst "vlast" in
      let: "_v" := Fst (Snd "vlast") in
      let: "t" := Snd (Snd "vlast") in
      (if: ("tc" ≤ "t") || ("t" = "ts")
       then  assert: #false
       else  "t" < "ts")
  end.

Definition commit_handler : val :=
  λ: "kvs" "cdata" "vnum" <>,
  let: "tc" := ! "vnum" + #1 in
  let: "kvs_t" := ! "kvs" in
  let: "ts" := Fst "cdata" in
  let: "cache" := Snd "cdata" in
  (if: list_is_empty "cache"
   then  #true
   else
     let: "b" := map_forall (λ: "k" "_v",
                             let: "vlsto" := map_lookup "k" "kvs_t" in
                             let: "vs" := (if: "vlsto" = NONE
                              then  []
                              else  unSOME "vlsto") in
                             check_at_key "k" "ts" "tc" "vs")
                 "cache" in
     (if: "b"
      then
        "vnum" <- "tc";;
        "kvs" <- (update_kvs "kvs_t" "cache" "tc");;
        #true
      else  #false)).

Definition lk_handle : val :=
  λ: "lk" "handler",
  acquire "lk";;
  let: "res" := "handler" #() in
  release "lk";;
  "res".

Definition read_handler : val :=
  λ: "kvs" "tk" <>, kvs_get_last "tk" ! "kvs".

Definition start_handler : val :=
  λ: "vnum" <>, let: "vnext" := ! "vnum" + #1 in
                 "vnum" <- "vnext";;
                 "vnext".

Definition client_request_handler : val :=
  λ: "lk" "kvs" "vnum" "req",
  let: "res" := match: "req" with
    InjL "tk" => InjL (lk_handle "lk" (read_handler "kvs" "tk"))
  | InjR "r" =>
      match: "r" with
        InjL "_tt" => InjR (InjL (lk_handle "lk" (start_handler "vnum")))
      | InjR "cdata" =>
          InjR (InjR (lk_handle "lk" (commit_handler "kvs" "cdata" "vnum")))
      end
  end in
  "res".

Definition start_server_processing_clients ser : val :=
  λ: "addr" "lk" "kvs" "vnum" <>,
  run_server (repl_ser ser) (req_ser ser) "addr"
  (λ: "req", client_request_handler "lk" "kvs" "vnum" "req").

Definition init_server ser : val :=
  λ: "addr",
  let: "kvs" := ref (map_empty #()) in
  let: "vnum" := ref #0 in
  let: "lk" := newlock #() in
  Fork (start_server_processing_clients ser "addr" "lk" "kvs" "vnum" #()).

Definition init_client_proxy ser : val :=
  λ: "clt_addr" "srv_addr",
  let: "rpc" := init_client_proxy (req_ser ser) (repl_ser ser) "clt_addr"
                "srv_addr" in
  let: "txt" := ref NONE in
  let: "lk" := newlock #() in
  ("clt_addr", ("lk", ("rpc", "txt"))).

Definition start : val :=
  λ: "cst",
  let: "_clt_addr" := Fst "cst" in
  let: "lk" := Fst (Snd "cst") in
  let: "rpc" := Fst (Snd (Snd "cst")) in
  let: "tst" := Snd (Snd (Snd "cst")) in
  acquire "lk";;
  match: ! "tst" with
    SOME "_abs" => assert: #false
  | NONE =>
      let: "repl" := make_request "rpc" (InjR (InjL #())) in
      match: "repl" with
        InjL "_abs" => assert: #false
      | InjR "s" =>
          match: "s" with
            InjL "ts" => "tst" <- (SOME ("ts", (ref (map_empty #()))))
          | InjR "_abs" => assert: #false
          end
      end
  end;;
  release "lk".

Definition read : val :=
  λ: "cst" "k",
  let: "_clt_addr" := Fst "cst" in
  let: "lk" := Fst (Snd "cst") in
  let: "rpc" := Fst (Snd (Snd "cst")) in
  let: "tst" := Snd (Snd (Snd "cst")) in
  acquire "lk";;
  let: "vo" := match: ! "tst" with
    NONE => assert: #false
  | SOME "st" =>
      let: "ts" := Fst "st" in
      let: "cache" := Snd "st" in
      match: map_lookup "k" ! "cache" with
        SOME "v" => SOME "v"
      | NONE =>
          let: "repl" := make_request "rpc" (InjL ("k", "ts")) in
          match: "repl" with
            InjL "vo" => "vo"
          | InjR "_abs" => assert: #false
          end
      end
  end in
  release "lk";;
  "vo".

Definition write : val :=
  λ: "cst" "k" "v",
  let: "_clt_addr" := Fst "cst" in
  let: "lk" := Fst (Snd "cst") in
  let: "_rpc" := Fst (Snd (Snd "cst")) in
  let: "tst" := Snd (Snd (Snd "cst")) in
  acquire "lk";;
  match: ! "tst" with
    NONE => assert: #false
  | SOME "st" =>
      let: "_ts" := Fst "st" in
      let: "cache" := Snd "st" in
      "cache" <- (map_insert "k" "v" ! "cache");;
      release "lk"
  end.

Definition commit : val :=
  λ: "cst",
  let: "_clt_addr" := Fst "cst" in
  let: "lk" := Fst (Snd "cst") in
  let: "rpc" := Fst (Snd (Snd "cst")) in
  let: "tst" := Snd (Snd (Snd "cst")) in
  acquire "lk";;
  let: "b" := match: ! "tst" with
    NONE => assert: #false
  | SOME "st" =>
      let: "ts" := Fst "st" in
      let: "cache" := Snd "st" in
      let: "repl" := let: "cch" := ! "cache" in
                     (if: "cch" = NONE
                      then  InjR (InjR #true)
                      else  make_request "rpc" (InjR (InjR ("ts", "cch")))) in
      match: "repl" with
        InjL "_abs" => assert: #false
      | InjR "r" =>
          match: "r" with
            InjL "_abs" => assert: #false
          | InjR "b" => "tst" <- NONE;;
                        "b"
          end
      end
  end in
  release "lk";;
  "b".

Definition run : val :=
  λ: "cst" "handler", start "cst";;
                       "handler" "cst";;
                       commit "cst".
