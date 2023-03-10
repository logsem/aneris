From iris.algebra Require Import agree gmap auth.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     network tactics proofmode lifting lang.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import network_util_proof lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.dscm.spec Require Import base events time init resources.
From aneris.examples.dscm.implementations.one_server Require Import
     one_server_client_proxy_code
     one_server_serialization_code.

Section serialization.
  Context `{!DB_params}.

  Definition seq_id_serialization := int_serialization.

  Definition req_read_serialization := string_serialization.

  Definition req_write_serialization :=
    prod_serialization string_serialization DB_serialization.

  Definition req_serialization :=
    prod_serialization
      (sum_serialization
         req_write_serialization
         req_read_serialization)
      seq_id_serialization.

  Definition resp_serialization :=
    prod_serialization
      (sum_serialization
         unit_serialization
         (option_serialization DB_serialization))
      seq_id_serialization.

  Global Instance:
    ∀ (sid : Z) (k : Key),
      Serializable req_serialization (InjRV #k, #sid).
  Proof. apply _. Qed.

  Global Instance:
    ∀ (sid : Z) (k : Key) (v : val),
      DB_Serializable v →
      Serializable req_serialization (InjLV (#k, v), #sid).
  Proof. apply _. Qed.

  Global Instance:
    ∀ sid : Z, Serializable resp_serialization (InjRV NONEV, #sid).
  Proof. apply _. Qed.

  Global Instance:
    ∀ (sid : Z) (v : val),
      DB_Serializable v →
      Serializable resp_serialization (InjRV (SOMEV v), #sid).
  Proof. apply _. Qed.

  Global Instance:
    ∀ sid : Z, Serializable resp_serialization (InjLV #(), #sid).
  Proof. apply _. Qed.

  (* Typeclasses Opaque req_serialization resp_serialization. *)
  (* Global Opaque req_serialization resp_serialization. *)

End serialization.


Section Protocols.

 Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events}.
 Context `{!DB_resources Mdl Σ}.
 Variable client_addr : socket_address.


  Definition client_si : socket_interp Σ :=
    (λ msg, ∃ (sid : nat), ⌜0 <= sid ⌝)%I.

End Protocols.


Section Spec.

  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events}.
  Context `{!DB_resources Mdl Σ}.
  Context `{!lockG Σ}.
  Variable client_addr : socket_address.

  Definition ip := ip_of_address client_addr.
  Lemma ip_eq : ip = ip_of_address client_addr. Proof. done. Qed.
  Typeclasses Opaque ip.
  Global Opaque ip.





  Definition SM_N : namespace := nroot.@"SM".

  Definition lock_inv (ip : ip_address) (* (γ : gname) *)
             (sid : loc) (sh : socket_handle) : iProp Σ :=
    (∃ (n : nat) R T,
         sid ↦[ip] #n
         ∗ sh ↪[ip] (mkSocket (Some client_addr) false)
         ∗ client_addr ⤳ (R, T)
       (*  ∗ ([∗ set] m ∈ R, ∃ (sid : nat) dres,
              ⌜s_is_ser reply_serializer DB_serialization
               (#sid, des_resp_to_val dres) (m_body m)⌝ ∗ ⌜sid < n⌝)
       *) )%I.

Theorem install_proxy_spec
        (srv_addr : socket_address):
    {{{ unbound ip {[ port_of_address client_addr ]} ∗
        unallocated {[client_addr]} ∗
        ⌜client_addr ∉ DB_addresses⌝ ∗
        ⌜DB_addresses = [srv_addr]⌝ ∗
        client_addr ⤳ (∅, ∅)
        }}}
      install_proxy
      DB_serialization.(s_serializer) #srv_addr #client_addr @[ip]
    {{{ fns, RET fns;
        ∃ wr rd, ⌜fns = (wr, rd)%V⌝
          ∗ (write_spec wr client_addr)
          ∗ (read_spec rd client_addr)
         }}}.
  Proof.
     iIntros (ϕ) "(Hfree & Hunallocated & %Hca2 & %Hdb & Hrs) Hcont".
     wp_lam; wp_pures.
     wp_socket sh as "Hsh /=". wp_pures.
     wp_alloc l as "Hl". wp_pures.
     rewrite ip_eq.
     set s := {| saddress := None |}.
     iApply (aneris_wp_socket_interp_alloc_singleton client_si with "Hunallocated").
     iIntros "#Hclient".
     wp_socketbind.
     wp_apply (aneris_wp_rcvtimeo_unblock with "[$Hsh]"); eauto with lia.
     iIntros "Hsh". wp_seq; simpl.
     wp_apply (newlock_spec SM_N _ (lock_inv ip l sh)  with "[Hl Hsh Hrs]").
     { rewrite /lock_inv. iExists 0, ∅, ∅.
       rewrite -ip_eq. iFrame. }
     iIntros (lock γ_lock) "#Hislock". wp_pures.
    rewrite -ip_eq.
    iApply "Hcont".
    do 2 iExists _. iSplit; first done.
    iSplit.
     - iIntros (E k v P Q) "!# %HinvN %Hks #Hvsh".
       iIntros (ϕ') "!# HP HPost".
       wp_pures.
       rewrite /request.
       wp_pures.
    Admitted.



End Spec.

(*

Definition write_proof_obligation
           (E : coPset) (k : Key) (v : SerializableVal) (sa : socket_address)
           (P : iProp Σ)  (Q : we → ghst → ghst → ghst → iProp Σ)  : iProp Σ :=
 □  (P
   ={⊤, E}=∗
   ∃ (h s: ghst) (a_old: option we),
       ⌜at_key k h = a_old⌝ ∗
       Obs h ∗
       k ↦ₖ mval_of_we_opt a_old ∗
       Writes sa s ∗
       ▷ (∀ (hf : ghst) (a_new : we),
              ⌜at_key k hf = None⌝ ∗
              ⌜a_new.(WE_key) = k⌝ ∗
              ⌜a_new.(WE_val) = v⌝ ∗
              ⌜a_new.(WE_origin) = sa⌝ ∗
              ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
                               k ↦ₖ Some (mval_of_we a_new) ∗
                               Obs (h ++ hf ++ [a_new]) ∗
                               Writes sa (s ++ [a_new]) ={E,⊤}=∗ Q a_new h hf s))%I.



Inductive log_rpl :=
| RplWr
    (E : coPset) (k : Key) (v : SerializableVal) (sa : socket_address)
    (P : iProp Σ)  (Q : we → ghst → ghst → ghst → iProp Σ)
     (h hf s : ghst) (a: we) (vsg: iProp Σ) (Hvsg: vsg = Q a h hf s).
| RplRd
    (E : coPset) (k : Key)
    (P : iProp Σ)
    (Q1 : option we → ghst → ghst → iProp Σ)
    (Q2 : we → ghst → ghst → iProp Σ)
    (vsg: iProp Σ) (Hvsg: vsg = read_proof_obligation E k P Q1 Q2).
 (* Deserialized response *)
  Inductive response :=
  | RespRead (v : val)
  | RespWrite.

  Definition resp_to_val (r : response) : val :=
    match r with
    | RespRead v => InjLV v
    | RespWrite => InjRV #()
    end.


  Definition srv_si : socket_interp Σ :=
    (λ msg, ∃ (sid : nat), ⌜0 <= sid ⌝)%I.

  Definition client_si : socket_interp Σ :=
    (λ msg, ∃ (sid : nat), ⌜0 <= sid ⌝)%I.

Definition client_si' (γ : gname) : socket_interp Σ :=
    (λ msg, ∃ (sid : nat) dres (vo : option val),
        ⌜resp_serialization.(s_is_ser)
         (resp_to_val dres, #sid) (m_body msg)⌝
         (* ∗ is_req γ sid lrq *)
         (* ∗  resp_body_post dres lrq vo *)
)%I.




  Definition req_db (lrq : log_req) : rep_id :=
    match lrq with
    | LInit db => db
    | LRead db _ _ _ => db
    | LWrite db _ _ _ _ => db
    end.

  Theorem session_exec_spec
          ( (* γ *) γ_lock : gname)
          (sh : socket_handle)
          (seq_id : loc) (lock req_body : val)
          (srv_addr : socket_address)
          (req : val) :
          (* {Hser : ∀ (sid : Z), Serializable req_serialization (#sid, req_body)}: *)
          (* des_req_to_val drq = req_body → *)
          let PQ :=
        (* match req with *)
        (* | InjL "kv" => *)
        (*   let (k, v) := "kv" in  True *)
        (* | InjR "k"  => True *)
        (* | DInit => (True, fun u => init_post db_id) *)
        (* | DRead k => (⌜k ∈ DB_keys⌝ ∗ Seen db_id s ∗ OwnMemSnapshot k h, *)
        (*              fun res => ∃ vo, ⌜res = (des_resp_to_val (RRead vo))⌝ ∗ *)
        (*                 read_post db_id k s h vo) *)
        (* | DWrite k v => *)
        (*   (⌜k ∈ DB_keys⌝ ∗ Seen db_id s ∗ OwnMemSnapshot k h *)
        (*     ∗ ⌜DB_Serializable v⌝, fun u => write_post db_id k v s h) *)
        end%I
    in
    {{{ client_addr ⤇ client_si (* γ *)
        (* ∗ db_addr ⤇ (db_si db_id)  *)
        ∗ is_lock SM_N ip γ_lock lock (lock_inv seq_id sh)
        ∗ PQ.1 }}}
      request (s_serializer DB_serialization)
              #srv_addr #(LitSocket sh) lock #seq_id req @[ip]
      {{{ v, RET v; PQ.2 v}}}.
(InjL ("k", "v")

1 subgoal (ID 21430)

  Mdl : resources.Model
  Σ : gFunctors
  anerisG0 : anerisG Mdl Σ
  H : DB_params
  H0 : DB_time
  H1 : DB_events
  DB_resources0 : DB_resources Mdl Σ
  lockG0 : lockG Σ
  client_addr : socket_address
  A : gset socket_address
  srv_addr : socket_address
  ϕ : val → iPropI Σ
  Hca : client_addr ∉ A
  Hca2 : client_addr ∉ DB_addresses
  Hdb : DB_addresses = [srv_addr]
  sh : socket_handle
  l : loc
  s := mkSocket None true : socket
  lock : val
  γ_lock : gname
  ============================
  "Hfixed" : fixed A
  "Hclient" : client_addr ⤇ client_si
  "Hislock" : is_lock SM_N ip γ_lock lock (lock_inv ip l sh)
  --------------------------------------□
  write_spec
    (λ: "k" "v",
       request (s_serializer DB_serialization) #srv_addr #
         (LitSocket sh) lock #l (InjL ("k", "v"))) client_addr

*)

(* Theorem install_proxy_spec *)
(*         (A : gset socket_address) *)
(*         (srv_addr : socket_address): *)
(*     {{{ unbound ip {[ port_of_address client_addr ]} ∗ *)
(*         fixed A ∗ *)
(*         ⌜client_addr ∉ A⌝ ∗ *)
(*         ⌜client_addr ∉ DB_addresses⌝ ∗ *)
(*         ⌜DB_addresses = [srv_addr]⌝ ∗ *)
(*         client_addr ⤳ (∅, ∅) *)
(*         }}} *)
(*       install_proxy *)
(*       DB_serialization.(s_serializer) #srv_addr #client_addr @[ip] *)
(*     {{{ fns, RET fns; *)
(*         ∃ wr rd, ⌜fns = (wr, rd)%V⌝ *)
(*           ∗ (write_spec wr client_addr) *)
(*           ∗ (read_spec rd client_addr) *)
(*          }}}. *)



(*
Section Resources.
 Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events}.
 Context `{!DB_resources Mdl Σ}.

 Definition seqIdUR : ucmra :=
   gen_heapUR socket_address nat.

 (* Definition reqUR : ucmra := *)
 (*   gen_heapUR socket_address (iProp Σ). *)

Class clientProxyResourcesG (Mdl : Model) Σ :=
  ClientProxyResourcesG { seqIdG :> inG Σ (authR seqIdUR); }.

Class clientProxyResourcesPreG Σ (Mdl : Model) :=
  ClientProxyResourcesPreG { seqIdPreG :> inG Σ (authR seqIdUR); }.

Definition clientProxyResourcesΣ : gFunctors := #[GFunctor (authR seqIdUR)].

End Resources.



gmap id  agreement (gnames)

Definition read_proof_obligation
           (E : coPset) (k : Key)
           (P : iProp Σ)
           (Q1 : option we → ghst → ghst → iProp Σ)
           (Q2 : we → ghst → ghst → iProp Σ) : iProp Σ :=
  □ (P ={⊤, E}=∗
     ∃ (h s : ghst) (q : Qp) (ao: option we),
         ⌜at_key k h = ao⌝ ∗
         Obs h ∗
         k ↦ₖ{q} mval_of_we_opt ao ∗
         ▷ ((⌜ao = None⌝ ∗ (k ↦ₖ{q} None) ={E,⊤}=∗ Q1 ao h s) ∧
            (∀ a, ⌜ao = Some a⌝ ∗ (k ↦ₖ{q} Some (mval_of_we a)) ={E,⊤}=∗ Q2 a h s))).


Inductive log_req :=
| ReqWr
    (E : coPset) (k : Key) (v : SerializableVal) (sa : socket_address)
    (P : iProp Σ)  (Q : we → ghst → ghst → ghst → iProp Σ)
    (vsg: iProp Σ) (Hvsg: vsg = write_proof_obligation E k v sa P Q)
| REqRd
    (E : coPset) (k : Key)
    (P : iProp Σ)
    (Q1 : option we → ghst → ghst → iProp Σ)
    (Q2 : we → ghst → ghst → iProp Σ)
    (vsg: iProp Σ) (Hvsg: vsg = read_proof_obligation E k P Q1 Q2).



  Class RequestG  := LstG {
    lst_relayG :> gen_heapG socket_address (list string) Σ;
  }.

  Class RequestPreG := LstPreG {
    lst_relayPreG :> gen_heapPreG socket_address (list string) Σ;
  }.

  Definition lstΣ : gFunctors := #[gen_heapΣ socket_address (list string)].


  Definition server_si : socket_interp Σ :=
    (λ m, let (from, to) := (m_sender m, m_destination m) in
          let mb := m_body m in
          ∃ Ψ i s l,
            ⌜mb = idstr i s⌝ ∗
             from ⤇ Ψ ∗
             from ↦cpt{1/2} i ∗
             to ↦cpt{1/2} i ∗
             to ↦lst{1/2} l ∗
             (∀ m', ⌜mb = m_body m'⌝ ∗
                    ⌜to = m_sender m'⌝ ∗
                     from ↦cpt{1/2} i ∗
                     to ↦cpt{1/2} (i+1) ∗
                     to ↦lst{1/2} (s :: l) -∗
                     Ψ m'))%I.
*)
