From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.reliable_communication.lib.repdb Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras resources_def resources_global_inv resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import log_proof repdb_serialization.


Import gen_heap_light.
Import lock_proof.

Section MT_spec_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM mγ : gname).
  Context (mv : val).
  Context (kvsL logL : loc).

  Definition ReqData : Type :=
    (coPset * (string * val) * (iProp Σ * (we → wrlog → wrlog → iProp Σ))) +
    string * (Qp * option write_event).

  Definition RepData : Type := we * ghst * ghst + option we.

  Definition ReqPre (reqv : val) (reqd : ReqData) : iProp Σ :=
    Global_Inv γL γM ∗
    ((∃ E k v P Q,
     ⌜reqd = inl (E, (k, v), (P, Q))⌝ ∗
     ⌜reqv = InjLV (#(LitString k), v)%V⌝ ∗
     ⌜↑DB_InvName ⊆ E⌝ ∗
     ⌜k ∈ DB_keys⌝ ∗
     P ∗
     □ (P
         ={⊤, E}=∗
         ∃ (h : wrlog) (a_old: option we),
           ⌜at_key k h = a_old⌝ ∗
            own_mem_user γM k 1 a_old ∗
            own_obs γL DB_addr h ∗
            ▷ (∀ (hf : ghst) (a_new : we),
                  ⌜at_key k hf = None⌝ ∗
                  ⌜we_key a_new = k⌝ ∗ ⌜we_val a_new = v⌝ ∗
                  ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
                  own_mem_user γM k 1 (Some a_new) ∗
                  own_obs γL DB_addr (h ++ hf ++ [a_new]) ={E,⊤}=∗ Q a_new h hf))) ∨
    (∃ k wo q, ⌜k ∈ DB_keys⌝ ∗
               ⌜reqd = inr (k, (q, wo))⌝ ∗
               ⌜reqv = InjRV #(LitString k)⌝ ∗
               own_mem_user γM k q wo)).

  Definition ReqPost
    (repv : val) (reqd : ReqData) (repd : RepData) : iProp Σ :=
    (∀ E k v P Q, ⌜reqd = inl (E, (k, v), (P, Q))⌝ -∗
       ∃ a_new h hf, ⌜repd = inl (a_new, h, hf)⌝ ∗ ⌜repv = #()⌝ ∗ Q a_new h hf) ∨
    (∀ k wo q, ⌜reqd = inr (k, (q, wo))⌝ -∗
       ∃ vo, ⌜repd = inr wo⌝ ∗ ⌜repv = InjRV vo⌝ ∗  own_mem_user γM k q wo ∗
       ((⌜vo = NONEV⌝ ∗ ⌜wo = None⌝) ∨
        (∃ a, ⌜vo = SOMEV (we_val a)⌝ ∗ ⌜wo = Some a⌝))).


  Definition handler_cloj : val :=
    λ: "mv" "reqv", client_request_handler_at_leader #kvsL #logL "mv" "reqv".

  Lemma client_request_handler_at_leader_spec  :
    ∀ reqv reqd,
    {{{ is_monitor (DB_InvName .@ "leader_main") (ip_of_address DB_addr) mγ mv
               (leader_local_main_inv_def γL kvsL logL) ∗
           lock_proof.locked mγ ∗ (leader_local_main_inv_def γL kvsL logL) ∗
           ReqPre reqv reqd }}}
       handler_cloj mv reqv @[ip_of_address DB_addr]
    {{{ repv repd, RET repv;
           ⌜Serializable (rep_l2c_serialization) repv⌝ ∗
           lock_proof.locked mγ ∗ (leader_local_main_inv_def γL kvsL logL) ∗
           ReqPost repv reqd repd }}}.
  Proof.
  Admitted.
   (* iIntros (Φ) "(#Hmon & Hkey & HR & Hpre) HΦ".
    rewrite /client_request_handler_at_leader.
    wp_pures.
    rewrite /ReqPre.
    iDestruct "Hpre" as "(#HGinv & [HpreW | HpreR])".
    - admit.
    - iDestruct "HpreR" as (k we q Hkeys Hreqd ->) "Hk".
      wp_pures.
      rewrite{2} /leader_local_main_inv_def.
      iDestruct "HR" as (lV mV mM lM Hmap Hlog HvalidL) "(Hm & Hl & HlogL)".
      wp_load.
      wp_apply (wp_map_lookup $! Hmap).
      iIntros (v Hv).
      wp_pures.
      destruct (mM !! k) eqn:Hmk; rewrite Hmk in Hv.
      + admit.
      + iApply ("HΦ" $! _ (inr None)).
        iSplit.
        * rewrite Hv. rewrite /rep_l2c_serialization.
          iPureIntro.
          rewrite /Serializable /= /sum_valid_val /=; eauto.
          exists (InjLV #()). right. split; first done. by right.
        * iFrame "Hkey".
          iSplitR "Hk".
          ** admit.
          ** iRight. iIntros (k0 wo0 q0 Hreqd0).
             iExists v.
             iSplit.
             admit.
             iSplit; first done.
             rewrite Hreqd0 in Hreqd. inversion Hreqd. subst.
             iFrame. iLeft. admit.

          rewrite /option_valid_val.
          exists (InjLV #()).
          Eapply option_is_ser_valid. rewrite option_valid_val. /=; eauto..
          eauto. done. apply (sum_is_ser_valid _ _ _ ""). simplify_eq.
          simpl. iPureIntro. simplify_eq /=.
          eapply sum_is_ser_valid. rewrite /sum_is_ser. simplify_eq /=.
          eexists _, _. right. split; eauto. done.
       + admit.
      + iFrame "Hkey". *)


(* is_monitor (DB_InvName .@ "leader_main") (ip_of_address DB_addr) MTS_mγ  MTS_mv *)
(*                (leader_local_main_inv_def γL kvsL logL) ∗ *)
(*            lock_proof.locked MTS_mγ ∗ (leader_local_main_inv_def γL kvsL logL) ∗ *)
(*            ReqPre reqv reqd }}} *)

Global Program Instance client_handler_at_leader_spec_params : MTS_spec_params :=
  {| (* Requests. *)
    MTS_req_ser  := req_c2l_serialization;
    MTS_req_ser_inj := req_c2l_ser_is_injective;
    MTS_req_ser_inj_alt := req_c2l_ser_is_injective_alt;
    MTS_req_data := ReqData;
    MTS_rep_ser  := rep_l2c_serialization;
    MTS_rep_ser_inj := rep_l2c_ser_is_injective;
    MTS_rep_ser_inj_alt := rep_l2c_ser_is_injective_alt;
    MTS_rep_data := RepData;
    MTS_saddr := DB_addr;
    MTS_mN := (DB_InvName .@ "leader_main");
    MTS_mR := (leader_local_main_inv_def γL kvsL logL);
    MTS_mγ := mγ;
    MTS_mv := mv;
    MTS_handler := handler_cloj;
    MTS_handler_pre  := ReqPre;
    MTS_handler_post := ReqPost;
    MTS_handler_spec := client_request_handler_at_leader_spec;
|}.

End MT_spec_params.
