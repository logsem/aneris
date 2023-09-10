From iris.algebra Require Import agree auth excl gmap updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.snapshot_isolation.specs Require Import user_params.
From aneris.examples.snapshot_isolation.proof Require Import time events model.
From aneris.examples.snapshot_isolation.proof.resources Require Import resource_algebras.



(** Meta tokens tracking connection between physical data and ghost names. *)
Section ConnectedClients.
  Context `{!anerisG Mdl Σ, !IDBG Σ}.

  Context (γKnownClients : gname).

  Definition connected_clients (M : gmap socket_address gname) : iProp Σ :=
    own γKnownClients (● (to_agree <$> M : gmap _ _)).

  Definition connected_client_token (sa : socket_address) (γCst : gname) : iProp Σ :=
    own γKnownClients (◯ {[ sa := to_agree γCst ]}).

  Global Instance session_tokenPersistent sa γ :
    Persistent (connected_client_token sa γ).
  Proof. apply _. Qed.

  Lemma session_token_agree sa γ1 γ2 :
    connected_client_token sa γ1 -∗ connected_client_token sa γ2 -∗ ⌜γ1 = γ2⌝.
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

End ConnectedClients.

Section Resources.
  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.

  Context (γGauth γGsnap γT γTss : gname).

  (** ---------------- Global memory ---------------- *)

  Definition ownMemSeen (k : Key) (h : list write_event) : iProp Σ :=
    own γGsnap (◯ {[ k := to_max_prefix_list h]}).

  Definition ownMemUser (k : Key) (h : (list write_event)) : iProp Σ :=
    ghost_map_elem γGauth k (DfracOwn 1%Qp) h ∗
      ownMemSeen k h.

  Definition ownMemAuthGlobal
             (M : gmap Key (list write_event)) :=
    ghost_map_auth γGauth (1/2)%Qp M.

  Definition ownMemAuthLocal (M : gmap Key (list write_event)) :=
    ghost_map_auth γGauth (1/2)%Qp M.

  Definition ownMemMono (M : gmap Key (list write_event)) : iProp Σ :=
    own γGsnap
        (● (to_max_prefix_list <$> M : gmapUR Key (max_prefix_listR write_eventO))).

  Definition ownMemGlobal (M : gmap Key (list write_event)) : iProp Σ :=
    ownMemAuthGlobal M ∗ ownMemMono M.

  (** ---------------- Time Snaps ---------------- *)
  Definition ownTimeStartsAuth (tss : gset nat) : iProp Σ :=
    own γTss (● tss).

  Definition ownTimeStartsSnap (t : nat) : iProp Σ :=
    own γTss (◯ {[ t ]}).

  (** ---------------- Time ---------------- *)
  Definition ownTimeGlobal T : iProp Σ :=
    mono_nat_auth_own γT (1/2) T.

  Definition ownTimeLocal T : iProp Σ :=
    mono_nat_auth_own γT (1/2) T.

  Definition ownTimeCptSnap T : iProp Σ :=
    mono_nat_lb_own γT T.

  Definition ownTimeSnap ts : iProp Σ :=
     ownTimeCptSnap ts ∗ ownTimeStartsSnap ts.

  Instance ownTimeSnap_Persistent :
      ∀ i, Persistent (ownTimeSnap i).
    Proof. apply _. Qed.

  (** ---------------- Propreties of global memory. ---------------- *)

  Lemma ownMemSeen_lookup M k h :
    ownMemMono M ⊢
    ownMemSeen k h -∗
    ∃ h', ⌜h `prefix_of` h' ∧ M !! k = Some h'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2")
      as %[Hv1 Hv2]%auth_both_valid_discrete.
    rewrite singleton_included_l in Hv1.
    destruct Hv1 as (y & Hvy & Hv1).
    rewrite Some_included_total in Hv1.
    rewrite lookup_fmap in Hvy.
    destruct (M !! k) eqn:Heq; rewrite Heq in Hvy;
      simplify_eq /=; [| by inversion Hvy].
    apply Some_equiv_inj in Hvy.
    rewrite -Hvy to_max_prefix_list_included in Hv1.
    destruct Hv1 as (l0 & Hl0).
    fold_leibniz.
    iPureIntro; exists l. split; last done.
    by rewrite Hl0; apply prefix_app_r.
  Qed.

  Lemma  ownMemSeen_Persistent k h :
    Persistent (ownMemSeen k h).
  Proof. apply _. Qed.

(*  Seen_timeless k h :> Timeless (Seen k h); *)

(* OwnMemKey_exclusive k h h' : *)
(*         k ↦ₖ h ⊢ k ↦ₖ h' -∗ False; *)

(*     OwnLocalKey_exclusive k c v v' : *)
(*         k ↦{c} v ⊢ k ↦{c} v' -∗ False; *)


  Lemma ownMemSeen_prefix k h h':
    ownMemSeen k h ⊢ ownMemSeen k h' -∗
    ⌜h `prefix_of` h' ∨ h' `prefix_of` h⌝.
  Proof.
    iIntros "Hobs1 Hobs2".
    iDestruct (own_valid_2 with "Hobs1 Hobs2") as %Hvalid.
    rewrite auth_frag_op_valid singleton_op singleton_valid
      in Hvalid.
    by rewrite to_max_prefix_list_op_valid_L in Hvalid.
  Qed.

  (** TODO: other needed lemmas. *)

End Resources.
