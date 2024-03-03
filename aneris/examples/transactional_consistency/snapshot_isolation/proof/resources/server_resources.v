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
     list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events resource_algebras.
From aneris.examples.transactional_consistency.snapshot_isolation.proof Require Import model.
From aneris.examples.transactional_consistency Require Import user_params.


(*----------------------------------------------------------------------------*)
(** Meta tokens tracking connection between physical data and ghost names.    *)
(*----------------------------------------------------------------------------*)

Section ConnectedClients.
  Context `{!anerisG Mdl Σ, !IDBG Σ}.
  Context (γKnownClients : gname).

  Definition connected_clients
    (M : gmap socket_address gname) : iProp Σ :=
    own γKnownClients (● (to_agree <$> M : gmap _ _)).

  Definition connected_client_token
    (sa : socket_address) (γCst : gname) : iProp Σ :=
    own γKnownClients (◯ {[ sa := to_agree γCst ]}).

  Global Instance session_tokenPersistent sa γ :
    Persistent (connected_client_token sa γ).
  Proof. apply _. Qed.

  Lemma session_token_agree sa γ1 γ2 :
    connected_client_token sa γ1 -∗
    connected_client_token sa γ2 -∗
    ⌜γ1 = γ2⌝.
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

(*---------------------------------------------------------------------------*)
(** ----------------------- Resources for Snapshots ------------------------ *)
(*---------------------------------------------------------------------------*)
Section Snapshot_Resources.
  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (γTrns : gname).
  
  Definition global_memUR M : gmapUR Key (max_prefix_listR write_eventO) :=
    (to_max_prefix_list <$> M :
      gmapUR Key (max_prefix_listR write_eventO)).

  Definition ownSnapFrag (t : nat) (M : gmap Key (list write_eventO)) : iProp Σ :=
    own γTrns (◯ {[ t := to_agree (global_memUR M) ]}).

  Lemma ownSnapFragPersistent t M:
    Persistent (ownSnapFrag t M).
  Proof. apply _. Qed.
  
  Definition ownSnapAuth (S : gmap nat global_mem) : iProp Σ :=
    own γTrns (● (((λ M, to_agree (global_memUR M)) <$> S) : gmap _ _)).

  Lemma ownSnapAgree t M S :
    ownSnapFrag t M -∗
    ownSnapAuth S -∗
      ⌜S !! t = Some M⌝. 
  Proof.
    iIntros "Hf Ha".
    iDestruct (own_valid_2 with "Ha Hf")
      as %[Hv1 Hv2]%auth_both_valid_discrete.
    rewrite singleton_included_l in Hv1.
    destruct Hv1 as (y & Hvy & Hv1).
    rewrite Some_included_total in Hv1.
    rewrite lookup_fmap in Hvy.
    destruct (S !! t) eqn:HSt; last first. rewrite HSt in Hvy.  inversion Hvy.
    rewrite HSt in Hvy. 
    simplify_eq/=. iPureIntro. inversion Hvy. rewrite -H2 in Hv1.
    apply to_agree_included in Hv1. apply leibniz_equiv. symmetry.
    simplify_eq /=. f_equal. f_equal. rewrite /global_memUR in Hv1. 
    apply Some_equiv_eq. exists M. split; first done.
    apply (map_fmap_equiv_inj to_max_prefix_list) in Hv1; first done.
    apply _. 
  Qed.
  
  Lemma ownSnapFragAgree t M1 M2 :
    ownSnapFrag t M1 -∗
    ownSnapFrag t M2 -∗
      ⌜M1 = M2⌝. 
  Proof.
    iIntros "Hf1 Hf2".
    rewrite /ownSnapFrag.
    iDestruct (own_valid_2 with "Hf1 Hf2") as %Hval.
    rewrite -auth_frag_op singleton_op  in Hval.
    apply auth_frag_valid_1 in Hval.
    specialize (Hval t).
    rewrite lookup_singleton in Hval.
    rewrite Some_op in Hval.
    iPureIntro.
    revert Hval.
    rewrite Some_valid.
    intros Hval.
    eapply (to_agree_op_inv (A:= _ )) in Hval.
    apply leibniz_equiv.
    rewrite /global_memUR in Hval.
    eapply (map_fmap_equiv_inj to_max_prefix_list) in Hval; first done.
    apply _.
  Qed.
    
End Snapshot_Resources.
   

(*---------------------------------------------------------------------------*)
(** ------------------- Resources for Global State ------------------------- *)
(*---------------------------------------------------------------------------*)
Section Global_Memory_Resources.
  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.

  (*---------------------------------------------------------------------------*)
  (** ------------------- Monotone tracking of the memory -------------------- *)
  (*---------------------------------------------------------------------------*)
  Section MonotoneMemory.
    Context (γGsnap : gname).

    Definition ownMemSeen (k : Key) (h : list write_event) : iProp Σ :=
      own γGsnap (◯ {[ k := to_max_prefix_list h]}).
    
    Definition ownMemMono (M : gmap Key (list write_event)) : iProp Σ :=
      own γGsnap (● global_memUR M).

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
    Lemma ownMemSeen_Persistent k h :
      Persistent (ownMemSeen k h).
    Proof. apply _. Qed.
    
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

    Lemma get_OwnMemSeen_prefix M k h hl:
      M !! k = Some h →
      hl `prefix_of` h →
      ownMemMono M ⊢ |==> ownMemMono M ∗ ownMemSeen k hl.
    Proof.
      iIntros (HMk h_hl) "?".
      iApply own_op.
      iApply own_update; last done.
      apply auth_update_dfrac_alloc.
      {
        apply gmap_core_id=>i x/lookup_singleton_Some[_<-].
        apply max_prefix_list.mono_list_lb_core_id.
      }
      apply (@singleton_included_l _ _ _ (max_prefix_listR write_eventO)).
      exists (to_max_prefix_list h).
      split; first by rewrite lookup_fmap HMk.
      apply Some_included_2.
      apply (@to_max_prefix_list_included_L write_eventO); last done.
      apply _.
    Qed.

    Lemma get_OwnMemSeen M k h :
      M !! k = Some h →
      ownMemMono M ⊢ |==> ownMemMono M ∗ ownMemSeen k h.
    Proof.
      intro HMk.
      by iApply get_OwnMemSeen_prefix.
    Qed.

  End MonotoneMemory.

  (*---------------------------------------------------------------------------*)
  (** ------------------- Monotone tracking of the memory -------------------- *)
  (*---------------------------------------------------------------------------*)
  Section GlobalMemory.
    Context (γGauth γGsnap : gname).

    Definition ownMemUser (k : Key) (h : (whist)) : iProp Σ :=
      ghost_map_elem γGauth k (DfracOwn 1%Qp) h ∗ ownMemSeen γGsnap k h.

    Definition ownMemAuthGlobal (M : global_mem) :=
      ghost_map_auth γGauth (1/2)%Qp M.

    Definition ownMemAuthLocal (M : global_mem) :=
      ghost_map_auth γGauth (1/2)%Qp M.
    
    Definition ownMemGlobal (M : global_mem) : iProp Σ :=
      ownMemAuthGlobal M ∗ ownMemMono γGsnap M.

    (*  Seen_timeless k h :> Timeless (Seen k h); *)
    (* OwnMemKey_exclusive k h h' : *)
    (*         k ↦ₖ h ⊢ k ↦ₖ h' -∗ False; *)

    (*     OwnLocalKey_exclusive k c v v' : *)
    (*         k ↦{c} v ⊢ k ↦{c} v' -∗ False; *)
    
  End GlobalMemory.

  (** ---------------- Time ---------------- *)
  Section GlobalTime.
    Context (γT : gname).
    
    Definition ownTimeGlobal T : iProp Σ :=
      mono_nat_auth_own γT (1/2) T.

    Definition ownTimeLocal T : iProp Σ :=
      mono_nat_auth_own γT (1/2) T.

    Definition ownTimeSnap T : iProp Σ :=
      mono_nat_lb_own γT T.

    Instance ownTimeSnap_Persistent :
      ∀ i, Persistent (ownTimeSnap i).
    Proof. apply _. Qed.

   End GlobalTime.
  
End Global_Memory_Resources.
