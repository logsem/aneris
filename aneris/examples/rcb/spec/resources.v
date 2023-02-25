From aneris.aneris_lang Require Import resources proofmode.
From aneris.prelude Require Import time.
From aneris.examples.rcb.spec Require Import base events.

(** Embedding of the model in the Iris logic. *)

Section Predicates.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCB_events}.

  Class RCB_resources := {

    (** Global Invariant *)
    GlobalInv : iProp Σ;

    GlobalInvPersistent :> Persistent GlobalInv;

    (** Global state *)

    OwnGlobal : gstate → iProp Σ;
    OwnGlobalSnapshot : gstate → iProp Σ;

    (** Global state properties *)

    OwnGlobal_timeless h :> Timeless (OwnGlobal h);
    OwnGlobalSnapshot_timeless h :> Timeless (OwnGlobalSnapshot h);

    OwnGlobal_Exclusive h h' : OwnGlobal h ⊢ OwnGlobal h' -∗ False;
    OwnGlobalSnapshotPersistent :> ∀ h, Persistent (OwnGlobalSnapshot h);
    OwnGlobalSnapshot_union h h' :
      OwnGlobalSnapshot h ⊢ OwnGlobalSnapshot h' -∗ OwnGlobalSnapshot (h ∪ h');
    User_Snapshot h : OwnGlobal h ⊢ OwnGlobal h ∗ OwnGlobalSnapshot h;
    OwnGlobalSnapshot_included h h' E :
      ↑RCB_InvName ⊆ E →
      GlobalInv ⊢
      OwnGlobal h -∗ OwnGlobalSnapshot h' ={E}=∗ OwnGlobal h ∗ ⌜h' ⊆ h⌝;

    Snapshot_ext h h' E :
      ↑RCB_InvName ⊆ E →
      GlobalInv ⊢ OwnGlobalSnapshot h -∗
        OwnGlobalSnapshot h' ={E}=∗
          ⌜∀ a a', a ∈ h → a' ∈ h' → (GE_vc a) = (GE_vc a') → a = a'⌝;

    (** Local state *)

    OwnLocal : nat → lstate → iProp Σ;

    (** Local state properties *)

    OwnLocal_timeless i s :> Timeless (OwnLocal i s);

    OwnLocal_Exclusive i s s' : OwnLocal i s ⊢ OwnLocal i s' -∗ False;

    OwnLocal_ext n n' s s' E :
      ↑RCB_InvName ⊆ E →
      GlobalInv ⊢ OwnLocal n s -∗ OwnLocal n' s' ={E}=∗
        ⌜∀ e e', e ∈ s → e' ∈ s' → (LE_vc e) = (LE_vc e')
                 → (LE_payload e) = (LE_payload e') ∧ (LE_origin e) = (LE_origin e')⌝;

    OwnLocal_local_ext n s E :
      ↑RCB_InvName ⊆ E →
      GlobalInv ⊢ OwnLocal n s ={E}=∗
                   ⌜∀ e e', e ∈ s → e' ∈ s → (LE_vc e) = (LE_vc e') → e = e'⌝;

    OwnLocal_provenance n s E :
      ↑RCB_InvName ⊆ E ->
      GlobalInv ⊢ OwnLocal n s ={E}=∗
       OwnLocal n s ∗ (∃ h, OwnGlobalSnapshot h ∗ ⌜∀ e, e ∈ s -> erasure e ∈ h⌝);

    OwnGlobalSnapshot_provenance n s h E :
      ↑RCB_InvName ⊆ E ->
      GlobalInv ⊢ OwnGlobalSnapshot h
                -∗ OwnLocal n s
                ={E}=∗ ⌜∀ a, a ∈ h -> (GE_origin a) = n -> ∃ e, e ∈ s ∧ erasure e = a⌝;

    OwnGlobalSnapshot_origin h :
      OwnGlobalSnapshot h -∗ ⌜∀ a, a ∈ h -> (GE_origin a) < length RCB_addresses⌝;  

    (** Causality property *)

    Causality n s h E :
      ↑RCB_InvName ⊆ E →
      GlobalInv ⊢ OwnLocal n s -∗ OwnGlobalSnapshot h ={E}=∗
        ⌜∀ a e, a ∈ h → e ∈ s → vector_clock_lt (GE_vc a) (LE_vc e) →
                ∃ e', e' ∈ s ∧ erasure e' = a⌝;

    init_token : nat → iProp Σ;

    (** Socket protocol *)

    RCB_socket_proto : nat -> socket_interp Σ;
 }.

End Predicates.

Section DerivedLemmas.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCB_events, !RCB_resources}.

  Lemma OwnLocal_erasure_injectivity E (i : nat) (s : lstate) :
    ↑RCB_InvName ⊆ E →
    GlobalInv ⊢ OwnLocal i s ={E}=∗
      ⌜ ∀ a b, a ∈ s → b ∈ s → erasure a = erasure b → a = b⌝.
  Proof.
    iIntros (Hnames) "HGlobinv HLoc".
    iMod (OwnLocal_local_ext with "HGlobinv HLoc") as "%ext"; first done.
    iModIntro. iPureIntro.
    intros a b a_in b_in erasure_eq.
    apply ext; try assumption.
    rewrite<- !erasure_vc.
    congruence.
  Qed.

  Lemma Local_included_Global (e : le) E (i : nat) (s : lstate) (h : gstate) :
    ↑RCB_InvName ⊆ E → e ∈ s →
    GlobalInv ⊢ OwnGlobal h -∗ OwnLocal i s ={E}=∗ ⌜erasure e ∈ h⌝.
  Proof.
    iIntros (Hnames e_in_s) "#HGlobinv HGlob HLoc".
    iMod (OwnLocal_provenance with "HGlobinv HLoc") as "[_ HSnap]"; try eassumption.
    iDestruct "HSnap" as (h') "[#HSnap %e_in_h']".
    iMod (OwnGlobalSnapshot_included with "HGlobinv HGlob HSnap") as "[_ %]"; auto.
  Qed.

  Lemma NoCreation i j si sj e E :
    ↑RCB_InvName ⊆ E ->
    GlobalInv ⊢ OwnLocal i si
              -∗ OwnLocal j sj
              -∗ ⌜e ∈ si⌝
              -∗ ⌜(LE_origin e) = j⌝
              ={E}=∗ ⌜∃ e', e' ∈ sj ∧ erasure e' = erasure e⌝.
  Proof.
    iIntros (?) "#HInv Hloci Hlocj %Hini %Horig".
    iMod (OwnLocal_provenance with "HInv Hloci") as "[Hloci Hh]"; [done|].
    iDestruct "Hh" as (h) "[#Hsnap %Herase]".
    iMod (OwnGlobalSnapshot_provenance with "HInv Hsnap Hlocj") as "%Hin"; try done.
    iPureIntro.
    apply Hin; [ | rewrite erasure_origin]; auto.
  Qed.

  (* TODO: merge the "prime" lemmas below with the original versions above.
     i.e. make sure the original lemmas all preserve non-duplicable resources. *)

  (** The following lemmas are all duplicates of the laws OwnLocal_local_ext,
      OwnLocal_erasure_injectivity, etc.
      These duplicates are here to preserve the exclusive resources `OwnGlobal h` or
      `OwnLocal n s` in the hypotheses. This is possible because the conclusion of lemmas such as
      OwnLocal_local_ext, etc., are pure goals.
  *)
  Lemma OwnLocal_local_ext' n s E :
    ↑RCB_InvName ⊆ E →
    GlobalInv ⊢ OwnLocal n s ={E}=∗
                OwnLocal n s ∗ ⌜∀ e e', e ∈ s → e' ∈ s → (LE_vc e) = (LE_vc e') → e = e'⌝.
  Proof.
    iIntros (HE) "#? ?".
    iApply fupd_plain_keep_r.
    iFrame.
    iIntros "?".
    iApply OwnLocal_local_ext; eauto.
  Qed.

  (* TODO: clean this up *)
  Lemma OwnLocal_ext' n n' s s' E :
      ↑RCB_InvName ⊆ E →
      GlobalInv ⊢ OwnLocal n s -∗ OwnLocal n' s' ={E}=∗
        OwnLocal n s ∗
        OwnLocal n' s' ∗
        ⌜∀ e e', e ∈ s → e' ∈ s' → (LE_vc e) = (LE_vc e')
                 → (LE_payload e) = (LE_payload e') ∧ (LE_origin e) = (LE_origin e')⌝.
  Proof.
    iIntros (HE) "#Hinv Hl1 Hl2".
    iPoseProof (fupd_plain_keep_r E ⌜∀ e e' : le, e ∈ s → e' ∈ s' →
                            LE_vc e = LE_vc e' →
                              LE_payload e = LE_payload e' ∧
                                LE_origin e = LE_origin e'⌝%I (OwnLocal n s ∗ OwnLocal n' s')) as "Himpl".
    remember ⌜∀ e e' : le, e ∈ s → e' ∈ s' →
                            LE_vc e = LE_vc e' →
                              LE_payload e = LE_payload e' ∧
                              LE_origin e = LE_origin e'⌝%I as post.
    iAssert (OwnLocal n s ∗ OwnLocal n' s' ={E}=∗ post)%I as "Himpl2".
    { iIntros "[Hl1 Hl2]".
      subst.
      iApply (OwnLocal_ext with "[//] Hl1 Hl2"); done. }
    iPoseProof ("Himpl" with "[$Hl1 $Hl2 $Himpl2]") as "> ([? ?]&?)".
    iModIntro. iFrame.
  Qed.

  Lemma OwnLocal_erasure_injectivity' E (i : nat) (s : lstate) :
    ↑RCB_InvName ⊆ E →
    GlobalInv ⊢ OwnLocal i s ={E}=∗
    OwnLocal i s ∗ ⌜ ∀ a b, a ∈ s → b ∈ s → erasure a = erasure b → a = b ⌝.
  Proof.
    iIntros (HE) "? ?".
    iApply fupd_trans.
    iApply fupd_plain_keep_r.
    iModIntro; iFrame.
    by iApply OwnLocal_erasure_injectivity.
  Qed.

  Lemma Local_included_Global' (e : le) E (i : nat) (s : lstate) (h : gstate) :
    ↑RCB_InvName ⊆ E → e ∈ s →
    GlobalInv ⊢ OwnGlobal h -∗ OwnLocal i s ={E}=∗
      ⌜ erasure e ∈ h ⌝ ∗ OwnGlobal h ∗ OwnLocal i s.
  Proof.
    iIntros (Hnames e_in_s) "? ? ?".
    iApply fupd_trans.
    iApply fupd_plain_keep_l.
    iFrame.
    iIntros "!> [? ?]".
    iApply (Local_included_Global with "[$] [$] [$]"); done.
  Qed.

  Lemma OwnGlobalSnapshot_provenance' n s h E :
    ↑RCB_InvName ⊆ E ->
    GlobalInv ⊢
    OwnGlobalSnapshot h
    -∗ OwnLocal n s
    ={E}=∗
        OwnLocal n s ∗
        ⌜∀ a, a ∈ h -> (GE_origin a) = n -> ∃ e, e ∈ s ∧ erasure e = a⌝.
  Proof.
    iIntros (Hname) "#Hinv #Hsnap Hloc".
    iApply fupd_plain_keep_r.
    iFrame.
    iIntros "Hloc".
    iMod (OwnGlobalSnapshot_provenance with "Hinv Hsnap Hloc") as %?;
      [done | by iPureIntro].
  Qed.

  Lemma Causality' n s h E :
      ↑RCB_InvName ⊆ E →
      GlobalInv ⊢ OwnLocal n s -∗ OwnGlobalSnapshot h ={E}=∗
        OwnLocal n s ∗
        ⌜∀ a e, a ∈ h → e ∈ s → vector_clock_lt (GE_vc a) (LE_vc e) →
                ∃ e', e' ∈ s ∧ erasure e' = a⌝.
  Proof.
    iIntros (?) "? ? ?".
    iApply fupd_trans.
    iApply fupd_plain_keep_r.
    iFrame.
    iIntros "!> ?".
    iApply (Causality with "[$] [$]"); done.
  Qed.
End DerivedLemmas.

Arguments RCB_resources _ _ {_ _ _}.

