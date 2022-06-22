From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras log_resources.

Import gen_heap_light.
Import lock_proof.


Section Known_followers.
  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Resources about free/known replicated logs. *)

  (** ** Ownership for a replicated log known by the system. *)
  Definition known_replog_token (sa : socket_address) (γ : gnameO) : iProp Σ :=
    own IDBG_known_replog_name (◯ {[ sa := to_agree γ ]}).

  Global Instance  known_replog_token_Persistent sa γ :
    Persistent (known_replog_token sa γ).
  Proof. apply _. Qed.

  (** ** Ownership of all replicated logs known by the system. *)
  Definition known_replog_tokens (N : gmap socket_address gnameO)  : iProp Σ :=
    (* own IDBG_free_replog_set_name (GSet (dom N)) ∗ *)
    own IDBG_known_replog_name (● (to_agree <$> N : gmap _ _ )).

 Lemma known_replog_token_agree sa γ1 γ2 :
   known_replog_token sa γ1 -∗ known_replog_token sa γ2 -∗ ⌜γ1 = γ2⌝.
  Proof.
    iIntros "Hγ1 Hγ2".
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
    iPureIntro.
    rewrite -auth_frag_op singleton_op  in Hval.
    apply auth_frag_valid_1 in Hval.
    specialize (Hval sa).
    rewrite lookup_singleton in Hval.
    rewrite Some_op in Hval.
    revert Hval.
    rewrite Some_valid.
    intros Hval.
    by apply (to_agree_op_inv_L (A:=leibnizO _ )) in Hval.
  Qed.

  Lemma known_replog_in_N N sa γsa:
    known_replog_tokens N ∗ known_replog_token sa γsa -∗
    ⌜N !! sa = Some γsa⌝.
  Proof.
    iIntros "[Htoks Htok]".
    rewrite /known_replog_tokens /known_replog_token.
    iDestruct (own_valid_2 with "Htoks Htok") as %Hvalid.
    rewrite auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hincluded _].
    iPureIntro.
    revert Hincluded.
    rewrite singleton_included_l; intros (w & Hw1 & Hw2).
    revert Hw2; rewrite -Hw1; clear Hw1.
    rewrite lookup_fmap. clear w.
    intros [|(w & w' & Hw1 & Hw2 & Hw3)]%option_included; [done|].
    destruct (N !! sa); last by inversion Hw2.
    simplify_eq /=.
    destruct Hw3 as [->%(@to_agree_inj)%leibniz_equiv|Hw3]; [done|].
    by apply to_agree_included in Hw3 as ->%leibniz_equiv.
  Qed.

End Known_followers.

Section Resources_definition.
  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname).

  (* ------------------------------------------------------------------------ *)
  (** Abstract global memory definition and properties. *)

  Definition own_mem_user (k : Key) (q: Qp) (a : option write_event) :=
    lmapsto γM k q a.

  Definition own_mem_sys M := gen_heap_light_ctx γM M.

  (** Properties of points-to connective *)
  Lemma OwnMemKey_timeless_holds k q v : Timeless (own_mem_user k q v).
  Proof. apply _. Qed.

  From stdpp Require Import numbers.

  Lemma OwnMemKey_exclusive_holds k q v v' :
    own_mem_user k 1 v ⊢ own_mem_user k q v' -∗ False.
  Proof.
    rewrite /own_mem_user.
    iIntros "Hown1 Hown2".
    iDestruct (lmapsto_valid_2 with "Hown1 Hown2") as %Hvalid.
    rewrite frac_valid in Hvalid.
    by apply Qp_not_add_le_l in Hvalid.
  Qed.

  (* Maybe remove ? *)
  Lemma OwnMemKey_fractioal_holds k v : Fractional (λ q, own_mem_user k q v).
  Proof. apply _. Qed.

  Lemma OwnMemKey_as_fractioal_holds k q v :
    AsFractional (own_mem_user k q v) (λ q, own_mem_user k q v) q.
  Proof. apply _. Qed.

  Lemma OwnMemKey_combine_holds k q q' v v' :
    own_mem_user k q v ∗ own_mem_user k q' v' ⊢
    own_mem_user k (q + q') v ∗ ⌜v = v'⌝.
  Proof.
    iIntros "[Hown1 Hown2]".
    iApply (lmapsto_combine with "Hown1 Hown2").
  Qed.

  Lemma OwnMemKey_split_holds k q1 q2 v :
    own_mem_user k (q1 + q2) v ⊢ own_mem_user k q1 v ∗ own_mem_user k q2 v.
  Proof. iIntros "[Hown1 Hown2]". by iFrame. Qed.

  Lemma own_mem_update k M (we : option write_event) (we' : write_event) :
    own_mem_user k 1%Qp we ⊢
    own_mem_sys M ==∗ own_mem_user k 1%Qp (Some we') ∗ own_mem_sys (<[k := Some we']>M).
  Proof.
    iIntros "Hown1 Hown2".
    iMod (gen_heap_light_update with "Hown2 Hown1") as "[Hown2 Hown1]".
    iModIntro. iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** Principal & replicated log ownership predicates *)

  (** ** Principal log. *)
  Definition own_logL_global L : iProp Σ := own_log_auth γL (1/2) L.

  Definition own_logL_obs L : iProp Σ := own γL (◯ML L).

  (** ** Replicated logs. *)

  Definition own_replog_global γ sa l : iProp Σ :=
    known_replog_token sa γ ∗ own_logL_obs l ∗ own_log_auth γ (1/2) l.

  Definition own_replog_obs sa l : iProp Σ :=
    ∃ γ, known_replog_token sa γ ∗ own_logL_obs l ∗ own γ (◯ML l).

  (** ** General Obs predicate : socket_address → wrlog → iProp Σ. *)
  Definition own_obs sa l : iProp Σ :=
    (⌜sa = DB_addr⌝ ∗ own_logL_obs l) ∨ own_replog_obs sa l.

  Lemma Obs_timeless_holds a h : Timeless (own_obs a h).
  Proof. apply _. Qed.

  Lemma Obs_persistent_holds a h : Persistent (own_obs a h).
  Proof. apply _. Qed.

  Lemma Obs_own_log_obs DB_addr L:
    own_obs DB_addr L ⊢ own_log_obs γL L.
  Proof.
    iIntros "[(%_ & #Hobs)|#Hobs]"; [iFrame "#"|].
    by iDestruct "Hobs" as (γ) "(_ & Hobs &  _)".
  Qed.

End Resources_definition.
