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
From aneris.examples.snapshot_isolation.proof Require Import model.
From aneris.examples.snapshot_isolation.proof.resources Require Import
  resource_algebras.


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

(*----------------------------------------------------------------------------*)
(** Resources embedding the model of the global memory and snapshots.         *)
(*----------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(** ----------------------- Resources for Snapshots ------------------------ *)
(*---------------------------------------------------------------------------*)
Section Snapshot_Resources.
  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (γTrns : gname).

  (** Snapshots related to a transaction identified by a ghost name γt. *)
  Section Snapshot_at_given_gname.
    Context (γt : gname).
    
    Definition ownSnapFragGname (k : Key) (h : whist) : iProp Σ :=
      own γt (◯ {[ k := to_max_prefix_list h]}).

    Lemma ownSnapFragGnamePersistent k h:
      Persistent (ownSnapFragGname k h).
    Proof. apply _. Qed.
  
    Definition global_memUR M : gmapUR Key (max_prefix_listR write_eventO) :=
      (to_max_prefix_list <$> M :
        gmapUR Key (max_prefix_listR write_eventO)).

    Definition ownSnapFragMemGname M : iProp Σ :=
      own γt (◯ global_memUR M).

    Lemma ownSnapFragMemGnamePersistent M:
      Persistent (ownSnapFragMemGname M).
    Proof. apply _. Qed.
    
    Definition ownSnapAuthGname (M : global_mem) : iProp Σ :=
      own γt (● global_memUR M).

    Lemma ownSnapFragGname_lookup M k h :
      ownSnapAuthGname M ⊢
      ownSnapFragGname k h -∗
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

    (* We do not need this lemma actually *)
    (* Lemma ownSnapFragGname_prefix k h h':
      ownSnapFragGname k h ⊢ ownSnapFragGname k h' -∗
        ⌜h `prefix_of` h' ∨ h' `prefix_of` h⌝.
    Proof.
      iIntros "Hobs1 Hobs2".
      iDestruct (own_valid_2 with "Hobs1 Hobs2") as %Hvalid.
      rewrite auth_frag_op_valid singleton_op singleton_valid
        in Hvalid.
      by rewrite to_max_prefix_list_op_valid_L in Hvalid.
    Qed. *)

    Lemma get_ownSnapFragGname_prefix M k h hl:
      M !! k = Some h →
      hl `prefix_of` h →
      ownSnapAuthGname M ⊢
        |==> ownSnapAuthGname M ∗ ownSnapFragGname k hl.
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
  
  Lemma get_ownSnapFragGname M k h :
      M !! k = Some h →
      ownSnapAuthGname M ⊢ |==> ownSnapAuthGname M ∗ ownSnapFragGname k h.
  Proof.
    intro HMk.
    by iApply get_ownSnapFragGname_prefix.
  Qed.
  
  End Snapshot_at_given_gname.

  Section Snapshots.
    
    (** A transaction identified by the start time ts and a ghost name γTr. *)
    Definition ownTrnFrag (t : nat) (γt : gname) : iProp Σ :=
      own γTrns (◯ {[ t := to_agree γt ]}).

    Definition ownSnapshotsNamesAuth (S : gmap nat gname) : iProp Σ :=
      own γTrns (● (to_agree <$> S : gmap _ _)).

    Definition ownSnapFrag γt (t : nat) (k : Key) (h : whist) : iProp Σ :=
      ownTrnFrag t γt ∗ ownSnapFragGname γt k h .

    Lemma ownSnapFragPersistent γt t k h :
      Persistent (ownSnapFrag γt t k h).
    Proof. apply _. Qed.

    (** Importantly, note that there is currently no relation between snapshots
        for two given transactions. We only relate snapshots to the state of 
        the global memory. *)
    Definition ownSnapshotsAuth (Sγ : gmap nat gname) (S : snapshots) : iProp Σ :=
      ownSnapshotsNamesAuth Sγ ∗
      ([∗ map] t ↦ γt ; Mt ∈ Sγ ; S, ownTrnFrag t γt ∗ ownSnapAuthGname γt Mt).

    Lemma ownSnapFrag_lookup Sγ S M γ t k h :
      ownSnapshotsAuth Sγ S ⊢
      ⌜Sγ !! t = Some γ⌝ -∗
      ⌜S !! t = Some M⌝ -∗
      ownSnapFrag γ t k h -∗
      ∃ h', ⌜h `prefix_of` h' ∧ M !! k = Some h'⌝.
    Proof.
      iIntros "(HAuthNames & HAuth) %Hγ %HM #(Hf1 & Hf2)".
      iDestruct (big_sepM2_lookup with "[$HAuth]") as "(_ & HauthM)"; try eauto.
      iApply (ownSnapFragGname_lookup with "[$HauthM][$Hf2]").
    Qed.

    Lemma get_ownSnapFrag_prefix Sγ S M k h hl t γ:
      Sγ !! t = Some γ →
      S !! t = Some M →
      M !! k = Some h →
      hl `prefix_of` h →
      ownSnapshotsAuth Sγ S ⊢
      |==> ownSnapshotsAuth Sγ S ∗ ownSnapFrag γ t k hl.
    Proof.
      iIntros (Hsg HS HM Hpre) "(Htrs & Hauth)".
      iDestruct (big_sepM2_lookup_acc with "[$Hauth]")
        as "((#Ht & Ha) & Hacc)"; try eauto.
      iMod (get_ownSnapFragGname_prefix γ M k h hl HM Hpre with "[Ha]")
        as "(Ha & Hf)"; try eauto.
      iFrame "#∗".
      iApply "Hacc".
      by iFrame "#∗".
    Qed.
    
    Lemma get_ownSnapFrag Sγ S M t k h γ :
      Sγ !! t = Some γ →
      S !! t = Some M →
      M !! k = Some h →
      ownSnapshotsAuth Sγ S ⊢ |==>  ownSnapshotsAuth Sγ S ∗ ownSnapFrag γ t k h.
    Proof.
      iIntros (???) "Ha".
      by iApply (get_ownSnapFrag_prefix with "[$Ha]").
    Qed.

  End Snapshots.

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
