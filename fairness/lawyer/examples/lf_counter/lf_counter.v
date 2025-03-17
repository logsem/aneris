From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Class LFCPreG Σ := {
    lfc_wm :> inG Σ (authUR (gmapUR nat natUR));
}.


Class LFCG Σ := {
    lfc_pre :> LFCPreG Σ;
    γ__wm: gname;
}.


Section WaitMap.
  Context `{LFCG Σ}.

  Definition wm_auth (wm: gmap nat nat) :=
    own γ__wm ((● wm): authUR (gmapUR nat natUR)). 

  Definition val_toks (i k: nat) :=
    own γ__wm ((◯ {[ i := k ]}): authUR (gmapUR nat natUR)).

  Definition val_tok (i: nat) := val_toks i 1. 

  Lemma wm_auth_toks_ge wm i k:
    wm_auth wm -∗ val_toks i k -∗ ⌜ exists n, wm !! i = Some n /\ k <= n ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite -own_op. 
    iIntros "X". iDestruct (own_valid with "X") as %V. iPureIntro.
    apply auth_both_valid_discrete in V as [SUB V].
    apply singleton_included_l in SUB as (? & ITH & LE).
    apply leibniz_equiv_iff in ITH. eexists. split; eauto.
    rewrite Some_included_total in LE.
    by apply nat_included.
  Qed.

  Lemma wm_alloc wm i:
    wm_auth wm ==∗ wm_auth (<[ i := default 0 (wm !! i) + 1 ]> wm) ∗ val_tok i.
  Proof using.
    iIntros "WM". rewrite -own_op. rewrite /wm_auth.
    iApply (own_update with "[$]"). apply auth_update_alloc.
    destruct (wm !! i) eqn:ITH; simpl.
    - eapply insert_alloc_local_update; eauto.
      apply nat_local_update.
      set_solver.
    - apply alloc_local_update; eauto. done.
  Qed.  

  Lemma wm_get0 wm i
    (DOM: i ∈ dom wm):
    wm_auth wm ==∗ wm_auth wm ∗ val_toks i 0.
  Proof using.
    iIntros "WM". rewrite -own_op. rewrite /wm_auth.
    iApply (own_update with "[$]"). apply auth_update_alloc.
    apply elem_of_dom in DOM as [? ITH]. 
    etrans. 
    - eapply insert_alloc_local_update; eauto. reflexivity.
    - rewrite insert_id; [| done]. reflexivity. 
  Qed.

End WaitMap.


Section LFCounter.
  Context `{ODd: OfeDiscrete DegO} `{ODl: OfeDiscrete LevelO}.
  Context `{LEl: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Let OAM := ObligationsAM.
  Let ASEM := ObligationsASEM.

  Context `{EM: ExecutionModel heap_lang M}.

  Context {Σ: gFunctors}.
  (* Keeping the more general interface for future developments *)
  Context `{oGS': @asem_GS _ _ ASEM Σ}.
  Let oGS: ObligationsGS (OP := OP) Σ := oGS'.
  Existing Instance oGS.

  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

  Context (d0 d1: Degree).
  Hypotheses (DEG01: deg_lt d0 d1). 

  (* Context (K: nat). *)
  (* Hypothesis (K_LB: K <= LIM_STEPS). *)

  Definition INCR_ITER_LEN := 10.
  Hypothesis (INCR_LS_LB: 2 + INCR_ITER_LEN <= LIM_STEPS).

  Local Instance filter_key_dec c:
    ∀ x : nat * nat, Decision ((gt c ∘ fst) x).
  Proof using.
    intros [??]. simpl. rewrite /gt. solve_decision.
  Qed.

  Definition wm_waits `{LFCG Σ} π__cnt c (wm: gmap nat nat): iProp Σ :=
    [∗ map] i ↦ n ∈ filter (gt c ∘ fst) wm, 
      (∃ r, cp_mul π__cnt d0 (r * INCR_ITER_LEN) ∗ val_toks i (n - r) ∗ ⌜ r <= n ⌝).

  Definition wm_eb (wm: gmap nat nat): iProp Σ :=
    exc_lb (set_max (map_img wm: gset nat) * INCR_ITER_LEN). 

  Definition wm_interp `{LFCG Σ} π__cnt c: iProp Σ :=
    ∃ wm, wm_auth wm ∗ wm_waits π__cnt c wm ∗ wm_eb wm ∗ ⌜ dom wm = set_seq 0 (S c) ⌝.

  Definition cnt_inv_inner `{LFCG Σ} (cnt: loc) (π__cnt: Phase): iProp Σ :=
    ∃ (c: nat), cnt ↦ #c ∗ wm_interp π__cnt c. 

  Definition cnt_ns := nroot.@"cnt".
  Definition cnt_inv `{LFCG Σ} cnt π__cnt := inv cnt_ns (cnt_inv_inner cnt π__cnt).

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS' _ EM _ (↑ nroot)}.
  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS' _ EM _ ⊤}.
  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}.

  Definition incr_impl: val :=
    rec: "incr_impl" "c" :=
      let: "n" := !"c" in
      if: CAS "c" "n" ("n" + #1) then #()
      else "incr_impl" "c"
  . 

  Definition incr: val :=
    λ: "c", incr_impl "c".

  Lemma eb_wm_incr wm c:
    wm_eb wm -∗ BOU ∅ INCR_ITER_LEN
      (wm_eb (<[c:=(default 0 (wm !! c) + 1)]> wm)).
  Proof using.
    clear INCR_LS_LB. 
    iIntros "EB".
    iApply OU_BOU_rep. iApply (OU_rep_wand with "[]").
    2: { iApply increase_eb_upd_rep. iFrame. }

    iApply exc_lb_le.
    rewrite -Nat.mul_succ_l. apply PeanoNat.Nat.mul_le_mono_r. 
    apply set_max_spec. rewrite /set_Forall. intros i.
    rewrite elem_of_map_img. setoid_rewrite lookup_insert_Some.
    rewrite -(Nat.add_1_r (set_max _)).
    intros [n [[<- <-] | [? ITH]]].
    - destruct (wm !! c) eqn:CTH; simpl; [| lia].
      apply Plus.plus_le_compat_r_stt.
      apply set_max_elems. eapply elem_of_map_img; eauto.
    - etrans; [apply set_max_elems| ].
      { eapply @elem_of_map_img.
        3: eexists; eauto.
        all: apply _. }
      lia.
  Qed.
    
  Lemma wm_alloc_tok `{LFCG Σ} π__cnt c:
    wm_interp π__cnt c -∗ BOU ∅ INCR_ITER_LEN (wm_interp π__cnt c ∗ val_tok c).
  Proof using.
    clear INCR_LS_LB.
    iIntros "(%wm & AUTH & WAITS & #EB & %DOM)".
    iMod (wm_alloc _ c with "[$]") as "[AUTH TOK]".
    iFrame "TOK". 
    rewrite /wm_interp.
    iExists _. iFrame "AUTH".

    iApply (BOU_frame_l with "[WAITS]").
    { rewrite /wm_waits.
      rewrite map_filter_insert_not; [done| ].
      simpl. lia. }

    iApply BOU_frame_r.
    { iPureIntro. rewrite dom_insert_L. rewrite <- DOM.
      apply subseteq_union_1_L. apply singleton_subseteq_l.
      rewrite DOM. apply elem_of_set_seq. lia. }

    by iApply eb_wm_incr. 
  Qed.

  Lemma wm_incr `{LFCG Σ} π__cnt c:
    wm_interp π__cnt c -∗ cp π__cnt d1 -∗ BOU ∅ (INCR_ITER_LEN + 1) (wm_interp π__cnt (S c)).
  Proof using DEG01. 
    clear ODl ODd OBLS_AMU__f OBLS_AMU NO_OBS_POST LEl INCR_LS_LB. 
    iIntros "(%wm & AUTH & WAITS & #EB & %DOM) CP1".
    iMod (wm_alloc _ (S c) with "[$]") as "[AUTH TOK]".
    iMod (wm_get0 _ c with "[$]") as "[AUTH TOKS0]".
    { rewrite dom_insert_L. rewrite DOM.
      apply elem_of_union. right. apply elem_of_set_seq. lia. }    
    rewrite /wm_interp. iExists _. iFrame "AUTH".

    rewrite bi.sep_assoc. iApply BOU_frame_r.
    { iPureIntro. rewrite dom_insert_L. rewrite DOM.
      rewrite (set_seq_S_end_union_L _ (S c)). done. }

    iMod (eb_wm_incr with "[$]") as "#EB'"; [lia| ]. 
    iApply BOU_frame_r; [iApply "EB'"| ]. 
    
    rewrite not_elem_of_dom_1.
    2: { rewrite DOM. intros ?%elem_of_set_seq. lia. }
    simpl.

    assert (c ∈ dom wm) as [k CTH]%elem_of_dom.
    { rewrite DOM. apply elem_of_set_seq. lia. }

    rewrite /wm_waits.
    rewrite map_filter_insert_not.
    2: { intros. simpl. lia. }

    rewrite {3 4}(map_split wm c). rewrite CTH. simpl.  
    rewrite !map_filter_union.
    2, 3: apply map_disjoint_dom; set_solver. 
    rewrite !big_sepM_union.
    2, 3: apply map_disjoint_dom; eapply disjoint_subseteq;
          [apply _| apply dom_filter_subseteq | apply dom_filter_subseteq| ];
          set_solver. 
    iDestruct "WAITS" as "[_ WAITS']". iApply (BOU_frame_r with "[WAITS']").
    { iApply (big_opM_proper_2 with "[$]").
      2: { intros ????? EQ.
           erewrite leibniz_equiv_iff in EQ. by subst. }
      apply map_equiv_iff. intros i.
      rewrite !map_filter_lookup.
      destruct (delete c wm !! i) eqn:ITH.
      2: { done. }
      simpl. apply lookup_delete_Some in ITH as [? ITH].
      rewrite !option_guard_decide.
      apply mk_is_Some, elem_of_dom in ITH. rewrite DOM in ITH.
      apply elem_of_set_seq in ITH. 
      apply leibniz_equiv_iff. destruct decide, decide; try lia. done. }

    rewrite map_filter_singleton. simpl. destruct decide; [| lia].
    rewrite big_sepM_singleton.
    iExists k. rewrite Nat.sub_diag. iFrame "TOKS0".
    iMod (exchange_cp_upd with "[$] []").
    4: { iModIntro. iFrame. iPureIntro. lia. }
    { reflexivity. }
    { apply DEG01. }
    iApply (exc_lb_le with "EB").
    apply Nat.mul_le_mono_r. 
    apply set_max_elems. eapply elem_of_map_img; eauto.
  Qed. 

  Lemma wmi_swap `{LFCG Σ} c c' π__cnt
    (NEQ: c ≠ c'):
    wm_interp π__cnt c' -∗ val_tok c -∗ wm_interp π__cnt c' ∗ cp_mul π__cnt d0 INCR_ITER_LEN.
  Proof using.
    clear DEG01 ODl ODd OBLS_AMU__f OBLS_AMU NO_OBS_POST LEl INCR_LS_LB. 
    iIntros "(%wm & AUTH & WAITS & #EB & %DOM) TOK".
    rewrite /wm_interp.
    iApply bi.sep_exist_r. iExists _. iFrame "EB". iClear "EB".
    rewrite bi.sep_comm !bi.sep_assoc. iSplitL; [| done].  
    rewrite /wm_waits.
    iDestruct (wm_auth_toks_ge with "[$] [$]") as %LT.
    destruct LT as (K & CTH & _).
    assert (c < c') as LT. 
    { apply mk_is_Some, elem_of_dom in CTH. rewrite DOM in CTH.
      apply elem_of_set_seq in CTH. lia. }
    rewrite (map_split wm c). rewrite CTH. simpl.
    rewrite !map_filter_union.
    2: apply map_disjoint_dom; set_solver. 
    rewrite !big_sepM_union.
    2: apply map_disjoint_dom; eapply disjoint_subseteq;
          [apply _| apply dom_filter_subseteq | apply dom_filter_subseteq| ];
          set_solver.
    iDestruct "WAITS" as "[C WAITS']". iFrame "WAITS'".
    rewrite map_filter_singleton. simpl. destruct decide; [| lia].
    rewrite big_opM_singleton. iDestruct "C" as "(%r & CPS & TOKS & %LErk)".
    iCombine "TOK TOKS" as "TOKS".
    iDestruct (wm_auth_toks_ge with "[$] [$]") as %BOUNDc. iFrame "AUTH".
    destruct BOUNDc as (?&CTH_&BOUNDc).
    erewrite lookup_union_Some_l in CTH_; [| apply lookup_singleton].
    inversion CTH_. subst x.
    destruct r. 
    { lia. }
    rewrite Nat.mul_succ_l. iDestruct (cp_mul_split with "CPS") as "[? CPS]".
    iFrame "CPS".
    iExists _. iFrame.
    replace (1 + (K - S r)) with (K - r) by lia. iFrame.
    iPureIntro. lia.
  Qed.

  Lemma incr_impl_spec `{LFCG Σ} τ π cnt π__cnt
    (PH: phase_le π__cnt π):
    {{{ cnt_inv cnt π__cnt ∗ exc_lb (S INCR_ITER_LEN) ∗ 
        cp π__cnt d1 ∗ cp_mul π d0 INCR_ITER_LEN ∗ 
        th_phase_frag τ π 1 }}}
      incr_impl #cnt @τ
    {{{ v, RET v; ⌜ True ⌝ }}}.
  Proof using OBLS_AMU INCR_LS_LB DEG01.
    clear ODl ODd OBLS_AMU__f NO_OBS_POST LEl.     
    iIntros (Φ) "(#INV & #EB & CP1 & CPS & PH) POST".
    iLöb as "IH".
    rewrite /incr_impl.

    pure_steps.
    
    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/cnt_inv_inner. iDestruct "inv" as ">(%c & CNT & WMI)".
    iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> CNT".
    MU_by_BOU.
    iApply BOU_weaken; [reflexivity| apply empty_subseteq| iIntros "X"; iApply "X"| ].
    iMod (wm_alloc_tok with "[$]") as "[WMI TOK]".
    { lia. }
    BOU_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[CNT WMI]") as "_".
    { iExists _. iFrame. }
    iModIntro.

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ + _)%E. pure_steps.

    wp_bind (CmpXchg _ _ _)%E.  
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". iModIntro.
    rewrite {1}/cnt_inv_inner. iDestruct "inv" as ">(%c' & CNT & WMI)".
    iApply sswp_MU_wp; [done| ].

    destruct (decide (c' = c)) as [-> | NEQ].
    - iApply (wp_cmpxchg_suc with "[$]").
      { done. }
      { by constructor. }
      iIntros "!> CNT".
      MU_by_BOU.
      iApply BOU_weaken; [reflexivity| apply empty_subseteq| iIntros "X"; iApply "X"| ].
      iMod (wm_incr with "[$] [$]") as "WMI".
      { lia. }
      BOU_burn_cp. iApply wp_value.
      iMod ("CLOS" with "[CNT WMI]") as "_".
      { iExists _. replace (Z.of_nat (S c)) with (Z.of_nat c + 1)%Z by lia.
        iFrame. }
      iModIntro.

      wp_bind (Snd _)%E. pure_steps. by iApply "POST".
    - iApply (wp_cmpxchg_fail with "[$]").
      { set_solver. }
      { by constructor. }
      iIntros "!> CNT".
      iDestruct (wmi_swap with "WMI [$]") as "[WMI CPS']"; [done| ].
      MU_by_burn_cp. iApply wp_value.  
      iMod ("CLOS" with "[CNT WMI]") as "_".
      { iExists _. iFrame. }
      iModIntro.

      wp_bind (Snd _)%E. do 3 pure_step_cases.
      iDestruct (cp_mul_weaken with "CPS'") as "CPS'"; [apply PH | reflexivity| ].
      iApply ("IH" with "[$] [$] [$] [$]"). 
  Qed.

  
  Lemma incr_spec `{LFCG Σ} τ π cnt π__cnt
    (PH: phase_le π__cnt π):
    {{{ th_phase_eq τ π ∗ cp_mul π__cnt d1 2 ∗
        cnt_inv cnt π__cnt }}}
      incr #cnt @ τ
    {{{ v, RET v; ⌜ True ⌝ }}}.
  Proof using OBLS_AMU INCR_LS_LB DEG01.
    iIntros (Φ) "(PH & CPS1 & #INV) POST".
    rewrite /incr.

    split_cps "CPS1" 1. rewrite -cp_mul_1.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
    rewrite cp_mul_weaken; [| apply PH| reflexivity].
    BOU_burn_cp.

    iApply (incr_impl_spec with "[-POST]").
    { apply PH. }
    { iFrame "#∗". }
    done.
  Qed.

  Lemma wmi_init `{LFCPreG Σ} π__cnt:
    ⊢ BOU ∅ 0 (∃ (L: LFCG Σ), wm_interp π__cnt 0).
  Proof using.
    clear -H. 
    rewrite /wm_interp. iStartProof.
    iMod (own_alloc (● {[ 0 := 0 ]} ⋅ ◯ _: (authUR (gmapUR nat natUR)))) as (γ) "[AUTH FRAG]".
    { apply auth_both_valid_2; [| reflexivity].
      by apply singleton_valid. }
    set (L := {| γ__wm := γ; |}).
    iApply OU_BOU_rep.
    iApply (OU_rep_wand with "[-]").
    2: { iApply increase_eb_upd_rep0. }
    iIntros "#EB". 
    iExists L, _. iFrame. iSplitL.
    { rewrite /wm_waits. rewrite map_filter_singleton. simpl.
      destruct decide; [lia| ]. set_solver. }
    iSplit.
    - rewrite /wm_eb. simpl. rewrite map_img_singleton_L.
      by rewrite set_max_singleton.
    - iPureIntro. rewrite dom_singleton_L. set_solver.
  Qed.

  Lemma alloc_cnt_inv `{LFCPreG Σ} cnt π__cnt:
    cnt ↦ #0 -∗ BOU ∅ 0 (∃ (L: LFCG Σ), cnt_inv cnt π__cnt).
  Proof using.
    iIntros "CNT".
    iMod wmi_init as "(%L & WMI)".
    iMod (inv_alloc cnt_ns _ (cnt_inv_inner cnt π__cnt) with "[-]") as "#?".
    { iExists _. iNext. iFrame. }
    iModIntro. iExists _. iFrame "#∗".
  Qed.

  Definition counter_client: val :=
    λ: <>,
       let: "cnt" := ref #0%nat in
       Fork (incr "cnt") ;;
       incr "cnt".

  Theorem counter_client_spec `{LFCPreG Σ} τ π:
    {{{ th_phase_eq τ π ∗ cp_mul π d1 5 ∗ obls τ ∅ }}}
      counter_client #() @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof.
    iIntros (Φ) "(PH & CPS1 & OB) POST". rewrite /counter_client.

    split_cps "CPS1" 1. rewrite -cp_mul_1.
    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply DEG01. }
    BOU_burn_cp.

    wp_bind (ref _)%E.
    iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %cnt CNT _".
    MU_by_BOU.
    iApply (BOU_weaken ∅); [reflexivity| set_solver| ..].
    { eauto. }
    iMod (alloc_cnt_inv _ π with "[$]") as "(%ND & #INV)".
    { lia. }
    BOU_burn_cp. iApply wp_value.

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (Fork _)%E.
    iApply sswp_MUf_wp. iIntros (τ') "!>".
    split_cps "CPS" 1.
    MU__f_by_BOU (∅: gset SignalId). 
    iModIntro. iSplitR "CPS' PH OB". 
    2: { iExists _. rewrite cp_mul_1. by iFrame. }
    iIntros "(%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2])".
    rewrite difference_diag_L intersection_idemp_L.

    split_cps "CPS1" 2.
    iSplitL "CPS1' PH2 OB2".
    - iApply (incr_spec with "[$]").
      { apply PH_LT2. }
      iIntros "!> % _". simpl. by iApply NO_OBS_POST.
      Unshelve. by eauto. 
    - iRename "PH1" into "PH". rewrite cp_mul_weaken; [| apply PH_LT1| reflexivity].
      wp_bind (Rec _ _ _)%E. pure_steps.

      iApply (incr_spec with "[$]").
      { apply PH_LT1. }
      iIntros "!> % _". by iApply "POST".

  Qed.    

End LFCounter.
  
