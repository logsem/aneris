From iris.algebra Require Import agree gmap auth.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     network tactics proofmode lifting lang.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec resources.

(* Resources and socket protocols for session guarantees *)

Section res.
  Context `{!DB_params, !DB_time, !DB_events}.

  Definition rep_id := nat.
  Definition seq_id := nat.

  Inductive log_req :=
  | LInit (db : rep_id)
  | LRead (db : rep_id) (k : Key) (s : lhst) (h : gmem)
  | LWrite (db : rep_id) (k : Key) (v : SerializableVal) (s : lhst) (h : gmem).

  Definition req_db (lrq : log_req) : rep_id :=
    match lrq with
    | LInit db => db
    | LRead db _ _ _ => db
    | LWrite db _ _ _ _ => db
    end.

  Definition req_map := gmapUR nat (agreeR (leibnizO log_req)).
  Context `{!inG Σ (authUR req_map)}.

  Definition is_req γ (n : seq_id) (rq : log_req) :=
    own γ (◯ {[ n := to_agree rq]}).

  Instance is_req_persistent γ n req : Persistent (is_req γ n req).
  Proof. apply _. Qed.

  Lemma is_req_agree γ n rq rq' :
    is_req γ n rq ⊢ is_req γ n rq' -∗ ⌜rq = rq'⌝.
  Proof.
    iIntros "H1 H2".
    rewrite /is_req.
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    iPureIntro.
    rewrite -auth_frag_op in Hvalid.
    revert Hvalid.
    rewrite auth_frag_valid.
    intros Hvalid.
    specialize (Hvalid n).
    rewrite lookup_op !lookup_singleton in Hvalid.
    rewrite -Some_op in Hvalid.
    revert Hvalid.
    rewrite Some_valid.
    intros Hvalid.
    apply @to_agree_op_inv in Hvalid.
    apply leibniz_equiv in Hvalid.
    simplify_eq.
    done.
  Qed.

  Lemma is_req_alloc γ (M : req_map) n rq :
    n ∉ dom M →
    own γ (● M) ⊢
    |==> own γ (● <[n := to_agree rq]> M) ∗ is_req γ n rq.
  Proof.
    iIntros (Hi) "HM".
    iMod (own_update _ _ (● <[n := to_agree rq]> M ⋅
                         ◯ {[n := to_agree rq]}) with "HM") as "[$ $]";
      last done.
    apply auth_update_alloc.
    apply @alloc_singleton_local_update; last done.
    apply (not_elem_of_dom (D := gset nat)); done.
  Qed.

  Lemma request_init : True ⊢ |==> ∃ γ, own γ (● ∅).
  Proof.
    iIntros "_".
    iApply own_alloc.
    apply auth_auth_valid; done.
  Qed.

  Lemma is_req_auth_disagree γ M (n : nat) rq :
    own γ (● M) ⊢ is_req γ n rq -∗ ⌜n ∈ dom M⌝.
  Proof.
    iIntros "Hown Hisreq".
    rewrite /is_req.
    iDestruct (own_valid_2 with "Hown Hisreq") as "Hown".
    iDestruct "Hown" as %[Hvalid _]%auth_both_valid_discrete.
    iPureIntro.
    apply dom_included in Hvalid.
    rewrite dom_singleton_L in Hvalid.
    set_solver.
  Qed.

End res.

Section serialization.
  Context `{!DB_params}.

  Definition seq_id_serialization := int_serialization.

  Definition req_init_serialization := string_serialization.

  Definition req_read_serialization := string_serialization.

  Definition req_write_serialization :=
    prod_serialization string_serialization DB_serialization.

  Definition req_serialization :=
    prod_serialization
      seq_id_serialization
      (sum_serialization
         req_init_serialization
         (sum_serialization
            req_read_serialization
            req_write_serialization)).

  Definition resp_init_serialization := string_serialization.

  Definition resp_read_serialization :=
    sum_serialization
      unit_serialization
      DB_serialization.

  Definition resp_write_serialization := string_serialization.

  Definition resp_serialization :=
    prod_serialization
      seq_id_serialization
      (sum_serialization
         resp_init_serialization
         (sum_serialization
            resp_read_serialization
            resp_write_serialization)).

  Global Instance: ∀ sid : Z, Serializable req_serialization (#sid, InjLV #"I").
  Proof. apply _. Qed.

  Global Instance:
    ∀ (sid : Z) (k : Key),
      Serializable req_serialization (#sid, InjRV (InjLV #k)).
  Proof. apply _. Qed.

  Global Instance:
    ∀ (sid : Z) (k : Key) (v : val),
      DB_Serializable v →
      Serializable req_serialization (#sid, InjRV (InjRV (#k, v))).
  Proof. apply _. Qed.

  Global Instance:
    ∀ sid : Z, Serializable resp_serialization (#sid, InjLV #"Ok").
  Proof. apply _. Qed.

  Global Instance:
    ∀ sid : Z, Serializable resp_serialization (#sid, InjRV (InjLV (InjLV #()))).
  Proof. apply _. Qed.

  Global Instance:
    ∀ (sid : Z) (v : val),
      DB_Serializable v →
      Serializable resp_serialization (#sid, InjRV (InjLV (InjRV v))).
  Proof. apply _. Qed.

  Global Instance:
    ∀ sid : Z, Serializable resp_serialization (#sid, InjRV (InjRV #"Ok")).
  Proof. apply _. Qed.

  Typeclasses Opaque req_serialization resp_serialization.
  Global Opaque req_serialization resp_serialization.

End serialization.

Section protocols.

  Definition SM_N : namespace := nroot.@"SM".

  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context `{!DB_params}.
  Context `{!DB_time, !DB_events}.
  Context `{!DB_resources Mdl Σ}.
  Context `{!Maximals_Computing}.
  Context `{!inG Σ (authUR req_map)}.

  (* Deserialized request *)
  Inductive des_req :=
  | DInit
  | DRead (k : Key)
  | DWrite (k : Key) (v : val).

  Definition des_req_to_val (r : des_req) : val :=
    match r with
    | DInit => (InjLV #"I")
    | DRead k => (InjRV (InjLV #k))
    | DWrite k v => (InjRV (InjRV (#k, v)))
    end.

  (* Deserialized response *)
  Inductive des_resp :=
  | RInit
  | RRead (v : val)
  | RWrite.

  Definition des_resp_to_val (r : des_resp) : val :=
    match r with
    | RInit => (InjLV #"Ok")
    | RRead v => (InjRV (InjLV v))
    | RWrite => (InjRV (InjRV #"Ok"))
    end.

  (* Variable msg_to_resp : message_body -> option (seq_id * des_resp). *)

  (* Consistency between physical and logical requests *)
  Inductive cons_req : des_req -> log_req -> Prop :=
  | ConsReqInit db : cons_req DInit (LInit db)
  | ConsReqRead db k s h : cons_req (DRead k) (LRead db k s h)
  | ConsReqWrite db k (v : SerializableVal) s h :
      cons_req (DWrite k v) (LWrite db k v s h).

  (* Consistency between a physical response and its logical request *)
  Inductive cons_res : des_resp -> log_req -> Prop :=
  | ConsResInit db : cons_res RInit (LInit db)
  | ConsResRead db k s h v : cons_res (RRead v) (LRead db k s h)
  | ConsResWrite db k v s h : cons_res (RWrite) (LWrite db k v s h).

  (* Socket protocols *)
  Definition init_post (db : rep_id) : iProp Σ :=
    ∃ s,
     Seen db s
     ∗ ([∗ set] k ∈ DB_keys, ∃ h, OwnMemSnapshot k h)
     ∗ GlobalInv.

  Definition read_post (db : rep_id) (k : Key) (s : lhst) (h : gmem)
             (vo : val) : iProp Σ :=
    ∃ s' h',
      ⌜s ⊆ s'⌝
      ∗ ⌜h ⊆ h'⌝
      ∗ Seen db s'
      ∗ OwnMemSnapshot k h'
      ∗ ((⌜vo = NONEV⌝ ∗ ⌜restrict_key k s' = ∅⌝)
         ∨
         (∃ e v, ⌜vo = SOMEV v⌝
                ∗ ⌜AE_val e = v⌝
                ∗ ⌜AE_key e = k⌝
                ∗ ⌜e ∈ Maximals (restrict_key k s')⌝
                ∗ ⌜(erasure e) ∈ h'⌝)).

  Definition write_post (db : rep_id) (k : Key) (v : val) (s : lhst)
             (h : gmem) : iProp Σ :=
    ∃ e s' h',
      ⌜AE_key e = k⌝
      ∗ ⌜AE_val e = v⌝
      ∗ ⌜s ⊆ s'⌝
      ∗ ⌜h ⊆ h'⌝
      ∗ Seen db s'
      ∗ OwnMemSnapshot k h'
      ∗ ⌜e ∉ s⌝
      ∗ ⌜e ∈ s'⌝
      ∗ ⌜(erasure e) ∉ h⌝
      ∗ ⌜(erasure e) ∈ h' ⌝
      ∗ ⌜(erasure e) ∈ Maximals h'⌝
      ∗ ⌜Maximum s' = Some e⌝.

  Definition db_si (db : rep_id) : socket_interp Σ :=
    (λ msg, ∃ ϕ (sid : nat) drq γ lrq,
        (m_sender msg) ⤇ ϕ ∗
        ⌜s_is_ser req_serialization
          (#sid, des_req_to_val drq)%V (m_body msg)⌝ ∗
        is_req γ sid lrq ∗
        ⌜req_db lrq = db⌝ ∗
        ⌜cons_req drq lrq⌝ ∗
        let (pre, post) :=
          match lrq with
          | LInit db => (True, fun _ => init_post db)
          | LRead db k s h =>
            (⌜k ∈ DB_keys⌝ ∗ Seen db s ∗ OwnMemSnapshot k h,
             fun res => ∃ vo, ⌜res = RRead vo⌝ ∗
                           read_post db k s h vo)
          | LWrite db k v s h =>
            (⌜k ∈ DB_keys⌝ ∗ Seen db s ∗ OwnMemSnapshot k h,
             fun _ => write_post db k v s h)
          end
        in
        pre ∗ □ (∀ res, (∃ dres, ⌜s_is_ser resp_serialization
                                (#sid, des_resp_to_val dres) (m_body res)⌝ ∗
                               is_req γ sid lrq
                               ∗ ⌜cons_res dres lrq⌝
                               ∗ post dres)
                        -∗ ϕ res))%I.

  Global Instance db_si_persistent db m : Persistent (db_si db m).
  Proof.
    rewrite /Persistent.
    iDestruct 1 as (Φ i drq γ lrq) "(#?&#?&#?&#?&#?&Hm)".
    destruct lrq eqn:Heq.
    - iDestruct "Hm" as "[_ #?]".
      iModIntro.
      iExists _, _, _, _, lrq; rewrite Heq.
      iFrame "#".
    - iDestruct "Hm" as "[#? #?]".
      iModIntro.
      iExists _, _, _, _, lrq; rewrite Heq.
      iFrame "#".
    - iDestruct "Hm" as "[#? #?]".
      iModIntro.
      iExists _, _, _, _, lrq; rewrite Heq.
      iFrame "#".
  Qed.

  Definition resp_body_post dres lrq vo : iProp Σ :=
    ⌜cons_res dres lrq⌝
    ∗ match lrq with
      | LInit db => init_post db
      | LRead db k s h => ⌜dres = RRead vo⌝ ∗
        read_post db k s h vo
      | LWrite db k v s h => write_post db k v s h
      end.

  Definition client_si (γ : gname) : socket_interp Σ :=
    (λ msg, ∃ (sid : nat) dres lrq vo,
        ⌜s_is_ser resp_serialization
         (#sid, des_resp_to_val dres) (m_body msg)⌝
         ∗ is_req γ sid lrq
         ∗  resp_body_post dres lrq vo)%I.
End protocols.

Global Hint Constructors cons_req : core.
Global Hint Constructors cons_res : core.
