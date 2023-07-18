From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.

Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.

Import derived_laws_later.bi.

Set Default Proof Using "Type".

Definition yes_go : val :=
  rec: "yes_go" "n" "b" :=
    (if: CAS "b" #true #false
      then "n" <- !"n" - #1
       else #());;
    if: #0 < !"n"
      then "yes_go" "n" "b"
      else #().

Definition yes : val :=
  λ: "N" "b",
    let: "n" := Alloc "N" in
    yes_go "n" "b".

Definition no_go : val :=
  rec: "no_go" "n" "b" :=
    (if: CAS "b" #false #true
      then "n" <- !"n" - #1
       else #());;
    if: #0 < !"n"
      then "no_go" "n" "b"
      else #().

Definition no : val :=
  λ: "N" "b",
    let: "n" := Alloc "N" in
    no_go "n" "b".

Definition start : val :=
  λ: "N",
    let: "b" := Alloc #true in
    (Fork (yes "N" "b") ;;
    Fork (no "N" "b")).

(** * Definition of the model! *)

Inductive YN := Y | No.

#[global] Instance YN_eqdec: EqDecision YN.
Proof. solve_decision. Qed.

#[global] Instance YN_countable: Countable YN.
Proof.
  refine ({|
             encode yn := match yn with Y => 1 | No => 2 end;
             decode p := match p with 1 => Some Y | 2 => Some No | _ => None end;
         |})%positive.
  intros yn. by destruct yn.
Qed.

#[global] Instance YN_inhabited: Inhabited YN.
Proof. exact (populate Y). Qed.

Inductive yntrans: nat*bool -> option YN -> nat*bool -> Prop :=
| yes_trans n: (n > 0)%nat -> yntrans (n, true) (Some Y) (n, false) (* < *)
| yes_fail n: (n > 1)%nat -> yntrans (n, false) (Some Y) (n, false) (* ≤ *)
| no_trans n: yntrans (S n, false) (Some No) (n, true) (* < *)
| no_fail n: (n > 0)%nat → yntrans (n, true) (Some No) (n, true) (* ≤ *)
.

Definition yn_live_roles nb : gset YN :=
  match nb with
  | (0, _) => ∅
  | (1, false) => {[ No ]}
  | _ => {[ No; Y ]}
  end.

Lemma live_spec_holds:
     forall s ρ s', yntrans s (Some ρ) s' -> ρ ∈ yn_live_roles s.
Proof.
  intros [n b] yn [n' ?] Htrans. rewrite /yn_live_roles.
  inversion Htrans; simplify_eq; destruct n'; try set_solver; try lia; destruct n'; try set_solver; lia.
Qed.

Definition the_fair_model: FairModel.
Proof.
  refine({|
            fmstate := nat * bool;
            fmrole := YN;
            fmtrans := yntrans;
            live_roles nb := yn_live_roles nb;
            fm_live_spec := live_spec_holds;
          |}).
Defined.

Definition the_model: LiveModel heap_lang the_fair_model :=
  {|
    lm_fl (x: fmstate the_fair_model) := 61%nat;
  |}.

(** The CMRAs we need. *)
Class yesnoG Σ := YesnoG {
  yes_name: gname;
  no_name: gname;
  yesno_n_G :> inG Σ (excl_authR natO);
  yesno_f_G :> inG Σ (excl_authR boolO);
 }.
Class yesnoPreG Σ := {
  yesno_PreG :> inG Σ (excl_authR natO);
  yesno_f_PreG :> inG Σ (excl_authR boolO);
 }.
Definition yesnoΣ : gFunctors :=
  #[ heapΣ (@LM_EM _ the_model);
     GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{@heapGS Σ _ (@LM_EM _ the_model), !yesnoG Σ}.
  Let Ns := nroot .@ "yes_no".

  Definition yes_at (n: nat) := own yes_name (◯E n).
  Definition no_at (n: nat) := own no_name (◯E n).

  Definition auth_yes_at (n: nat) := own yes_name (●E n).
  Definition auth_no_at (n: nat) := own no_name (●E n).

  Lemma they_agree γ (N M: nat):
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_agree N M:
    yes_at N -∗ auth_yes_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.
  Lemma no_agree N M:
    no_at N -∗ auth_no_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_update γ (N M P: nat):
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma yes_update P N M:
     auth_yes_at M ∗ yes_at N ==∗ auth_yes_at P ∗ yes_at P.
  Proof. apply they_update. Qed.
  Lemma no_update P N M:
     auth_no_at M ∗ no_at N ==∗ auth_no_at P ∗ no_at P.
  Proof. apply they_update. Qed.

  Lemma they_finished_update γ (N M P: bool):
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

  Definition yesno_inv_inner b :=
    (∃ N B,
          frag_free_roles_are ∅ ∗
          frag_model_is (N, B) ∗ b ↦ #B ∗
          (if B
           then auth_yes_at N ∗ auth_no_at N
           else auth_yes_at (N-1) ∗ auth_no_at N) ∗
          ⌜(N, B) ≠ (0, false)⌝
    )%I.
  Definition yesno_inv b := inv Ns (yesno_inv_inner b).

  Lemma yes_go_spec tid n b (N: nat) f (Hf: f > 40):
    {{{ yesno_inv b ∗ has_fuel tid Y f ∗ n ↦ #N ∗ ⌜N > 0⌝%nat ∗ yes_at N }}}
      yes_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).

    iIntros (Φ) "(#Hinv & Hf & HnN & %HN & Hyes) Hk". unfold yes_go.

    wp_pures.
    wp_bind (CmpXchg _ _ _).

    assert (∀ s, Atomic s (CmpXchg #b #true #false)) by apply _.

    iApply wp_atomic.

    iInv Ns as (M B) "(>HFR & >Hmod & >Bb & Hauths & >%Hnever)" "Hclose".
    destruct B; iDestruct "Hauths" as "[>Hay >Han]".
    - iDestruct (yes_agree with "Hyes Hay") as "%Heq".

      (* TODO *)
      rewrite -has_fuel_fuels.

      destruct (decide (M = 0)) as [->|Nneq]; first lia.
      destruct (decide (M = 1)) as [->|Nneq1].
      + iApply (wp_cmpxchg_suc_step_singlerole_keep_dead _ tid (Y: fmrole the_fair_model) _ 30%nat _
                                             (1, true) (1, false)
             with "[$]") =>//.
        { set_solver. }
        { lia. }
        { econstructor. lia. }
        { set_solver. }
        iModIntro.
        iIntros "!> (Hb & Hmod & HFR & Hf)".
        iMod (yes_update 0 with "[$]") as "[Hay Hyes]".
        iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
        { iNext. iExists _, _. iFrame. simpl. iFrame. by iPureIntro. }

        iModIntro.

        rewrite has_fuel_fuels.
        wp_pures.
        wp_load.
        wp_pures.
        wp_store.
        wp_pures.
        wp_load.

        wp_pure _.
        simplify_eq. simpl.

        iApply wp_atomic.

        iInv Ns as (M B) "(>HFR & >Hmod & >Hb & Hauths & >%Hbever')" "Hclose".

        destruct B.
        * iApply (wp_lift_pure_step_no_fork_remove_role {[ Y ]} ((0, true): fmstate the_fair_model) _ _ _ _ _ _ {[ Y := _ ]}) =>//.
          { apply map_non_empty_singleton. }
          { rewrite dom_singleton. set_solver. }
          { simpl. set_solver. }

          repeat iModIntro.

          iDestruct "Hauths" as "[Hay Han]". iDestruct (yes_agree with "Hyes Hay") as %Heq.
          assert (M = 0) by lia. simplify_eq. iFrame "Hmod". iSplitL "Hf".
          { rewrite /has_fuels_S fmap_insert fmap_empty //. }
          iIntros "Hmod Hf".

          wp_pures. repeat iModIntro.
          iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
          { iNext. iExists _, _. iFrame. done. }
          iModIntro. iApply "Hk".
          rewrite map_filter_singleton_False; last set_solver. rewrite /has_fuels dom_empty_L.
          iDestruct "Hf" as "[??]". iFrame.
        * iDestruct "Hauths" as "[>Hay >Han]". iDestruct (yes_agree with "Hyes Hay") as %Heq.
          assert (M = 1) by (destruct M; [done|lia]). simplify_eq.

          iApply (wp_lift_pure_step_no_fork_remove_role {[ Y ]} ((1, false): fmstate the_fair_model) _ _ _ _ _ _ {[ Y := _ ]}) =>//.
          { apply map_non_empty_singleton. }
          { rewrite dom_singleton. set_solver. }
          { simpl. set_solver. }

          repeat iModIntro.

          iFrame "Hmod". iSplitL "Hf".
          { rewrite /has_fuels_S fmap_insert fmap_empty //. }
          iIntros "Hmod Hf".

          wp_pures. repeat iModIntro.
          iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
          { iNext. iExists _, _. iFrame. done. }
          iModIntro. iApply "Hk".
          rewrite map_filter_singleton_False; last set_solver. rewrite /has_fuels dom_empty_L.
          iDestruct "Hf" as "[??]". iFrame.
      +  assert (N = N) by lia. simplify_eq. iApply (wp_cmpxchg_suc_step_singlerole _ tid (Y: fmrole the_fair_model) _ 55%nat _
                                             (M, true) (M, false)
             with "[$]"); eauto.
      { simpl. lia. }
      { econstructor. lia. }
      { simpl. destruct M; [set_solver | destruct M; set_solver]. }
      iModIntro.
      iIntros "!> (Hb & Hmod & HFR & Hf)".
      iMod (yes_update (M-1) with "[$]") as "[Hay Hyes]".
      iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
      { iNext. iExists _, _. iFrame. iPureIntro. intro contra. simplify_eq. }
      iModIntro. rewrite decide_True; last first.
      { do 2 (destruct M; try done). set_solver. }

      rewrite has_fuel_fuels.
      wp_pures.
      wp_load.
      wp_pures.
      wp_store.
      wp_pures.
      wp_load.
      wp_pures.

      destruct (decide (0 < S M - 1)) as [Heq|Heq].
      * rewrite bool_decide_eq_true_2 //; last lia.
        wp_pure _.

        rewrite -has_fuel_fuels.
        iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
        { iFrame "∗#". iSplit; last by iPureIntro; lia.
          iClear "Hg Hinv".

          assert (∀ l v v', v = v' → l ↦ v ⊣⊢ l ↦ v') as pointsto_proper.
          { intros ??? ->. done. }

          iApply (pointsto_proper with "HnN"). do 2 f_equiv. destruct M; [done|]. lia. }
        iPureIntro; lia.
      * rewrite bool_decide_eq_false_2 //; last lia.
        have ->: M = 0 by lia. simpl. lia.
    - iDestruct (yes_agree with "Hyes Hay") as "%Heq". rewrite -> Heq in *.
      have HM: M > 0 by lia.

      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (Y: fmrole the_fair_model) _ 50%nat _
                                             (M, false) (M, false)
             with "[$]"); eauto.
      { simpl. lia. }
      { econstructor. lia. }
      iIntros "!>!> (Hb & Hmod & HFR & Hf)".
      (* iMod (yes_update (N-1) with "[$]") as "[Hay Hyes]". *)
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _, _. iFrame. iSplit; [iFrame|done]. }

      rewrite decide_True; last first.
      { destruct M; [done|destruct M; [lia|set_solver]]. }

      iModIntro.
      wp_pures.
      wp_load.
      wp_pure _. rewrite bool_decide_eq_true_2; last lia.
      wp_pure _.

      rewrite -has_fuel_fuels.
      iApply ("Hg" with "[] [Hyes HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.

  Lemma yes_spec tid b (N: nat) f (Hf: f > 50):
    {{{ yesno_inv b ∗ has_fuel tid Y f ∗ ⌜N > 0⌝ ∗ yes_at N }}}
      yes #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & %HN & Hyes) Hk". unfold yes.

    wp_pures.
    wp_bind (Alloc _).

    rewrite has_fuels_gt_1; last by solve_fuel_positive.

    iApply (wp_alloc_nostep _ _ _ _ {[Y := _]}%nat with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite fmap_insert fmap_empty. done. }
    iNext. iIntros (n) "(HnN & _ & Hf)".
    rewrite -has_fuel_fuels.

    wp_pures.

    rewrite -has_fuel_fuels.

    iApply (yes_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    { iFrame "Hinv". iPureIntro; lia. }
  Qed.

  Lemma no_go_spec tid n b (N: nat) f (Hf: f > 40):
    {{{ yesno_inv b ∗ has_fuel tid No f ∗ n ↦ #N ∗ ⌜N > 0⌝ ∗ no_at N }}}
      no_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).

    iIntros (Φ) "(#Hinv & Hf & HnN & %HN & Hno) Hk". unfold no_go.

    wp_pures.
    wp_bind (CmpXchg _ _ _).

    assert (∀ s, Atomic s (CmpXchg #b #true #false)) by apply _.

    iApply wp_atomic.

    iInv Ns as (M B) "(>HFR & >Hmod & >Bb & Hauths & >%Hnever)" "Hclose".
    destruct B; iDestruct "Hauths" as "[>Hay >Han]"; last first.
    - iDestruct (no_agree with "Hno Han") as "%Heq".

      (* TODO *)
      rewrite -has_fuel_fuels.

      destruct (decide (M = 0)) as [->|Nneq]; first lia.
      destruct (decide (M = 1)) as [->|Nneq1].
      + iApply (wp_cmpxchg_suc_step_singlerole_keep_dead _ tid (No: fmrole the_fair_model) _ 30%nat _
                                             (1, false) (0, true)
             with "[$]") =>//.
        { lia. }
        { econstructor. }
        iModIntro.
        iIntros "!> (Hb & Hmod & HFR & Hf)".
        iMod (no_update 0 with "[$]") as "[Han Hno]".
        iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
        { iNext. iExists _, _. iFrame. simpl. iFrame. by iPureIntro. }

        iModIntro.

        rewrite has_fuel_fuels.
        wp_pures.
        wp_load.
        wp_pures.
        wp_store.
        wp_pures.
        wp_load.

        wp_pure _.
        simplify_eq. simpl.

        iApply wp_atomic.

        iInv Ns as (M B) "(>HFR & >Hmod & >Hb & Hauths & >%Hbever')" "Hclose".

        destruct B.
        * iApply (wp_lift_pure_step_no_fork_remove_role {[ No ]} ((0, true): fmstate the_fair_model) _ _ _ _ _ _ {[ No := _ ]}) =>//.
          { apply map_non_empty_singleton. }
          { rewrite dom_singleton. set_solver. }
          { simpl. set_solver. }

          repeat iModIntro.

          iDestruct "Hauths" as "[Hay Han]". iDestruct (no_agree with "Hno Han") as %Heq.
          assert (M = 0) by lia. simplify_eq. iFrame "Hmod". iSplitL "Hf".
          { rewrite /has_fuels_S fmap_insert fmap_empty //. }
          iIntros "Hmod Hf".

          wp_pures. repeat iModIntro.
          iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
          { iNext. iExists _, _. iFrame. done. }
          iModIntro. iApply "Hk".
          rewrite map_filter_singleton_False; last set_solver. rewrite /has_fuels dom_empty_L.
          iDestruct "Hf" as "[??]". iFrame.
        * iDestruct "Hauths" as "[>Hay >Han]". iDestruct (no_agree with "Hno Han") as %Heq.
          assert (M = 0) by lia. simplify_eq.
      +  assert (N = N) by lia. simplify_eq.
         destruct M; first done.

         iApply (wp_cmpxchg_suc_step_singlerole _ tid (No: fmrole the_fair_model) _ 55%nat _
                                             (S M, false) (M, true)
             with "[$]"); eauto.
         { simpl. lia. }
         { econstructor. }
         { simpl. destruct M; [set_solver | destruct M; set_solver]. }
         iModIntro.
         iIntros "!> (Hb & Hmod & HFR & Hf)".
         iMod (no_update (M) with "[$]") as "[Han Hno]".
         iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
         { iNext. iExists _, _. iFrame. iSplit; last by iPureIntro.
           iApply (own_proper with "Hay"). f_equiv. apply leibniz_equiv_iff. lia. }

         iModIntro. rewrite decide_True; last first.
         { do 2 (destruct M; try done); set_solver. }

         rewrite has_fuel_fuels.
         wp_pures.
         wp_load.
         wp_pures.
         wp_store.
         wp_pures.
         wp_load.
         wp_pures.

         destruct (decide (0 < S M - 1)) as [Heq|Heq].
         * rewrite bool_decide_eq_true_2 //; last lia.
           wp_pure _.

           rewrite -has_fuel_fuels.
           iApply ("Hg" with "[] [Hno HnN Hf] [$]"); last first.
           { iFrame "∗#". assert ((S M - 1)%Z = M)%nat as -> by lia. iFrame. iPureIntro; lia. }
           iPureIntro; lia.
         * rewrite bool_decide_eq_false_2 //; last lia.
           have ->: M = 0 by lia. simpl. lia.
    - iDestruct (no_agree with "Hno Han") as "%Heq". rewrite -> Heq in *.
      have HM: M > 0 by lia.

      rewrite -has_fuel_fuels. assert (M = N) by lia. simplify_eq.
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (No: fmrole the_fair_model) _ 50%nat _
                                             (N, true) (N, true)
             with "[$]"); eauto.
      { simpl. lia. }
      { econstructor. lia. }
      iIntros "!>!> (Hb & Hmod & HFR & Hf)".
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _, _. iFrame. iSplit; [iFrame|done]. }

      rewrite decide_True; last first.
      { destruct N; [lia|destruct N; set_solver]. }

      iModIntro.
      wp_pures.
      wp_load.
      wp_pure _. rewrite bool_decide_eq_true_2; last lia.
      wp_pure _.

      rewrite -has_fuel_fuels.
      iApply ("Hg" with "[] [Hno HnN Hf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.

  Lemma no_spec tid b (N: nat) f (Hf: f > 50):
    {{{ yesno_inv b ∗ has_fuel tid No f ∗ ⌜N > 0⌝ ∗ no_at N }}}
      no #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & %HN & Hyes) Hk". unfold no.

    wp_pures.
    wp_bind (Alloc _).

    rewrite has_fuels_gt_1; last by solve_fuel_positive.

    iApply (wp_alloc_nostep _ _ _ _ {[No := _]}%nat with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite fmap_insert fmap_empty. done. }
    iNext. iIntros (n) "(HnN & _ & Hf)".
    rewrite -has_fuel_fuels.

    wp_pures.

    rewrite -has_fuel_fuels.

    iApply (no_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    { iFrame "Hinv". done. }
  Qed.
End proof.


Section proof_start.
  Context `{@heapGS Σ _ (@LM_EM _ the_model), !yesnoPreG Σ}.
  Let Ns := nroot .@ "yes_no".

  Lemma start_spec tid (N: nat) f (Hf: f > 60):
    {{{ frag_model_is (N, true) ∗ 
        has_fuels tid {[ Y := f; No := f ]} ∗ ⌜N > 0⌝ }}}
      start #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "[Hst [Hf %HN]] Hkont". unfold start.

    wp_pures.

    wp_bind (Alloc _).
    iApply (wp_alloc_nostep _ _ _ _ {[Y := _; No := _]} with "[Hf]").
    { apply insert_non_empty. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //. }

    iIntros "!>" (l) "(Hl & _ & Hf)".

    wp_pures.

    (* Allocate the invariant. *)
    iMod (own_alloc (●E N  ⋅ ◯E N))%nat as (γ_yes_at) "[Hyes_at_auth Hyes_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E N  ⋅ ◯E N))%nat as (γ_no_at) "[Hno_at_auth Hno_at]".
    { apply auth_both_valid_2; eauto. by compute. }

    pose (the_names := {|
     yes_name := γ_yes_at;
     no_name := γ_no_at;
    |}).

    iApply fupd_wp.
    iAssert (|==> frag_free_roles_are ∅)%I as "-#FR".
    { rewrite /frag_free_roles_are. iApply own_unit. }
    iMod "FR" as "FR". 
    iMod (inv_alloc Ns _ (yesno_inv_inner l) with "[-Hkont Hf Hyes_at Hno_at]") as "#Hinv".
    { iNext. unfold yesno_inv_inner. iExists N, true. iFrame. done. }
    iModIntro.

    wp_bind (Fork _).
    rewrite has_fuels_gt_1; last solve_fuel_positive.
    iApply (wp_fork_nostep _ tid _ _ _ {[ No ]} {[ Y ]} {[Y := _; No := _]}
             with "[Hyes_at] [- Hf] [Hf]");
      [ set_solver | by apply insert_non_empty |  | | | rewrite !fmap_insert fmap_empty // ];
      [set_solver | |].
    { iIntros (tid') "!> Hf". iApply (yes_spec with "[-]"); last first.
      + by eauto.
      + rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite has_fuel_fuels. by iFrame "#∗".
      + lia. }

    iIntros "!> Hf".
    rewrite map_filter_insert_not; last set_solver.
    rewrite map_filter_insert_True; last set_solver.
    rewrite map_filter_empty insert_empty.

    iModIntro.
    wp_pures.

    rewrite has_fuels_gt_1; last solve_fuel_positive.
    iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ No ]} {[No := _]} with "[Hno_at] [Hkont] [Hf]");
      [ set_solver | by apply insert_non_empty |  | | | rewrite !fmap_insert fmap_empty // ];
      [set_solver | |].
    { iIntros (tid') "!> Hf". iApply (no_spec with "[-]"); last first.
      + by eauto.
      + rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite has_fuel_fuels. by iFrame "#∗".
      + lia. }

    iNext. iIntros "[Hf _]".
    iApply "Hkont". iModIntro. iApply (equiv_wand with "Hf"). do 2 f_equiv.
    rewrite dom_empty_iff_L map_filter_empty_iff.
    intros ???. set_solver.
  Qed.
End proof_start.
