From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From aneris.prelude Require Import quantifiers iris_extraction.
From aneris.program_logic Require Export weakestpre.

Set Default Proof Using "Type".
Import uPred.

Record execution_trace Λ := {
  extr_path : list (cfg Λ);
  extr_obs : list (list (observation Λ)); }.

Arguments extr_path {_} _.
Arguments extr_obs {_} _.

Record auxiliary_trace (AS : Type) := {
  auxtr_path : list AS; }.

Arguments auxtr_path {_} _.

Section execution_trace.
  Context {Λ : language}.

  Definition singleton_exec (c : cfg Λ) : execution_trace Λ :=
    {| extr_path := [c]; extr_obs := []; |}.

  Definition exec_starts_in (e : execution_trace Λ) (c : cfg Λ) : Prop :=
    hd_error (extr_path e) = Some c.

  Definition exec_ends_in (e : execution_trace Λ) (c : cfg Λ) : Prop :=
    last (extr_path e) = Some c.

  Lemma singleton_exec_starts_in c : exec_starts_in (singleton_exec c) c.
  Proof. done. Qed.

  Lemma singleton_exec_ends_in c : exec_ends_in (singleton_exec c) c.
  Proof. done. Qed.

  Lemma exec_ends_in_inj e c c' :
    exec_ends_in e c → exec_ends_in e c' → c = c'.
  Proof. rewrite /exec_ends_in; intros ->; congruence. Qed.

  Fixpoint valid_extr_path
           (ep : list (cfg Λ)) (obs : list (list (observation Λ))) : Prop :=
    match ep with
    | [] => obs = []
    | c :: ep' =>
      match ep' with
      | [] => obs = []
      | c' :: ep'' =>
        ∃ κ obs', obs = κ :: obs' ∧ step c κ c' ∧ valid_extr_path ep' obs'
      end
    end.

  Definition valid_exec (e : execution_trace Λ) : Prop :=
    valid_extr_path (extr_path e) (extr_obs e).

  Lemma valid_singleton_exec c : valid_exec (singleton_exec c).
  Proof. done. Qed.

  Definition exec_extend (e : execution_trace Λ) (c : cfg Λ)
             (κ : list (observation Λ)) :=
    {| extr_path := extr_path e ++ [c];
       extr_obs := extr_obs e ++ [κ]; |}.

  Lemma exec_extend_starts_in e c' c κ :
    exec_starts_in e c' → exec_starts_in (exec_extend e c κ) c'.
  Proof.
    rewrite /exec_starts_in /exec_extend /=; intros Hec'.
    assert (extr_path e = c' :: tail (extr_path e)) as ->
        by by apply hd_error_tl_repr.
    done.
  Qed.

  Lemma exec_extend_ends_in e c κ : exec_ends_in (exec_extend e c κ) c.
  Proof. apply last_snoc. Qed.

  Definition exec_get_obs (e : execution_trace Λ) :=
    fold_right (λ κ κs, κ ++ κs) [] (extr_obs e).

  Lemma exec_extend_get_obs e c κ :
    exec_get_obs (exec_extend e c κ) = exec_get_obs e ++ κ.
  Proof.
    rewrite /exec_get_obs /=.
    revert κ.
    induction (extr_obs e) as [|κ' obs IHobs]; intros κ; simpl.
    { rewrite app_nil_r //. }
    rewrite IHobs -!assoc_L //=.
  Qed.

  Lemma extend_valid_exec e c κ c':
    valid_exec e →
    exec_ends_in e c →
    step c κ c' →
    valid_exec (exec_extend e c' κ).
  Proof.
    destruct e as [ep eo]; rewrite /valid_exec /exec_ends_in /=.
    revert eo.
    induction ep as [|d ep IHep];
      intros eo Hvl Hend Hstp; first done.
    assert (ep = nil → d = c) as Hep1 by by intros ->; simplify_eq/=.
    assert (ep ≠ nil → last ep = Some c) as Hep2 by by destruct ep.
    destruct ep; simpl.
    { simplify_eq/=; eexists κ, _; done. }
    destruct Hvl as (κ' & eo' & -> & Hdstp & Hvl).
    eexists κ', _; split_and!; [done|done|].
    eapply IHep; eauto.
  Qed.

End execution_trace.

Section auxiliary_trace.
  Context {AS : Type}.

  Definition singleton_sim (st : AS) : auxiliary_trace AS :=
    {| auxtr_path := [st]; |}.

  Definition sim_starts_in (sm : auxiliary_trace AS) (st : AS) : Prop :=
    hd_error (auxtr_path sm) = Some st.

  Definition sim_ends_in (sm : auxiliary_trace AS) (st : AS) : Prop :=
    last (auxtr_path sm) = Some st.

  Lemma singleton_sim_starts_in st : sim_starts_in (singleton_sim st) st.
  Proof. done. Qed.

  Lemma singleton_sim_ends_in st : sim_ends_in (singleton_sim st) st.
  Proof. done. Qed.

  Lemma sim_ends_in_inj sm st st' :
    sim_ends_in sm st → sim_ends_in sm st' → st = st'.
  Proof. rewrite /sim_ends_in; intros ->; congruence. Qed.

  Fixpoint valid_auxtr_path (sm : list AS) : Prop :=
    match sm with
    | [] => True
    | st :: sm' =>
      match sm' with
      | [] => True
      | st' :: sm'' => M st st' ∧ valid_auxtr_path sm'
      end
    end.

  Definition valid_sim (sm : auxiliary_trace M) : Prop :=
    valid_auxtr_path (auxtr_path sm).

  Lemma valid_singleton_sim st : valid_sim (singleton_sim st).
  Proof. done. Qed.

  Definition sim_extend (sm : auxiliary_trace M) (st : M) :=
    {| auxtr_path := auxtr_path sm ++ [st]; |}.

  Lemma sim_extend_starts_in sm st' st :
    sim_starts_in sm st' → sim_starts_in (sim_extend sm st) st'.
  Proof.
    rewrite /sim_starts_in /sim_extend /=; intros Hec'.
    assert (auxtr_path sm = st' :: tail (auxtr_path sm)) as ->
        by by apply hd_error_tl_repr.
    done.
  Qed.

  Lemma sim_extend_ends_in sm st : sim_ends_in (sim_extend sm st) st.
  Proof. apply last_snoc. Qed.

  Lemma sim_valid_exec sm st st':
    valid_sim sm →
    sim_ends_in sm st →
    M st st' →
    valid_sim (sim_extend sm st').
  Proof.
    destruct sm as [smp]; rewrite /valid_sim /sim_ends_in /=.
    induction smp as [|st'' smp IHsmp];
      intros Hvl Hend Hstp; first done.
    assert (smp = nil → st'' = st) as Hep1 by by intros ->; simplify_eq/=.
    assert (smp ≠ nil → last smp = Some st) as Hep2 by by destruct smp.
    destruct smp; simpl.
    { simplify_eq/=; done. }
    destruct Hvl as [? ?]; split; first done.
    eapply IHsmp; eauto.
  Qed.

End auxiliary_trace.

Definition wptp_pre Σ M {Λ} (s : stuckness)
           (φ : execution_trace Λ → auxiliary_trace M → Prop)
           (wptp : execution_trace Λ -d> auxiliary_trace M -d> iPropO Σ) :
  execution_trace Λ -d> auxiliary_trace M -d> iPropO Σ :=
  (λ ex sm,
  ⌜valid_exec ex⌝ →
  ⌜φ ex sm⌝ →
  ∀ c c' κ st,
    ⌜exec_ends_in ex c⌝ →
    ⌜sim_ends_in sm st⌝ →
    ⌜step c κ c'⌝ →
    ▷ ▷ (∃ st', ⌜st' = st ∨ M st st'⌝ ∧
                ⌜φ (exec_extend ex c' κ) (sim_extend sm st')⌝ ∧
                wptp (exec_extend ex c' κ) (sim_extend sm st')))%I.

Local Instance wp_pre_contractive Σ M Λ s φ :
  Contractive (@wptp_pre Σ M Λ s φ).
Proof.
  rewrite /wptp_pre=> n wp wp' Hwp ex sm.
  repeat (f_contractive || f_equiv); apply dist_S; apply Hwp.
Qed.

Definition wptp Σ M {Λ} (s : stuckness) (φ : execution_trace Λ → auxiliary_trace M → Prop) :
  execution_trace Λ → auxiliary_trace M → iProp Σ := fixpoint (wptp_pre Σ M s φ).

Instance is_except_0_wptp {Σ} M Λ s φ exp sm:
  IsExcept0 (@wptp Σ Λ M s φ exp sm).
Proof.
  rewrite /IsExcept0; iIntros "H".
  rewrite /wptp (fixpoint_unfold (wptp_pre _ _ _ _) _ _).
  iIntros (? ? ? ? ? ? ? ? ?).
  iMod "H".
  iApply "H"; done.
Qed.

Global Instance wptp_plain Σ M {Λ} s φ ex sm : Plain (@wptp Σ M Λ s φ ex sm).
Proof.
  rewrite /Plain.
  iIntros "H".
  iLöb as "IH" forall (ex sm).
  rewrite /wptp (fixpoint_unfold (wptp_pre _ _ _ _) _ _).
  rewrite {3 5}/wptp_pre.
  iIntros (? ? c ? ? ? ? ? ?).
  iDestruct ("H" with "[] [] [] [] []") as "H"; [done|done|done|done|done|].
  do 2 (iApply later_plainly_1; iNext).
  iDestruct "H" as (st') "(#Hst' & #Hφ & H)".
  iExists _.
  iSplitR; first by iClear "IH"; iModIntro.
  iSplitR; first by iClear "IH"; iModIntro.
  iApply "IH"; done.
Qed.

Lemma wp_take_step `{!irisG Λ Σ M} s n st Φ e1 σ1 κ e2 σ2 efs κs :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 κs n st -∗
  WP e1 @ s; ⊤ {{ v, Φ v } } ={⊤}[∅]▷=∗
  ∃ st', ⌜st' = st ∨ M st st'⌝ ∗
  state_interp σ2 (κs ++ κ) (length efs + n) st' ∗
  WP e2 @ s; ⊤ {{ v, Φ v } } ∗
  ([∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }}).
Proof.
  iIntros (Hstp) "HSI Hwp".
  rewrite wp_unfold /wp_pre.
  destruct (to_val e1) eqn:He1.
  { erewrite val_stuck in He1; done. }
  iMod ("Hwp" with "HSI") as "[Hs Hwp]".
  iMod ("Hwp" with "[]") as "Hwp"; first done.
  iModIntro; iNext.
  iMod "Hwp" as (st') "(% & ? & ? & ?)".
  iModIntro; iExists _; iFrame; done.
Qed.

Lemma wp_not_stuck `{!irisG Λ Σ M} e σ κs s Φ n st :
  state_interp σ κs n st -∗
  WP e @ s; ⊤ {{ v, Φ v }} ={⊤}=∗
  state_interp σ κs n st ∗
  WP e @ s; ⊤ {{ v, Φ v }} ∗
  ⌜s = NotStuck → not_stuck e σ⌝.
Proof.
  iIntros "HSI Hwp".
  rewrite /not_stuck assoc.
  iApply fupd_plain_keep_r; iFrame.
  iIntros "[HSI Hwp]".
  rewrite wp_unfold /wp_pre.
  destruct (to_val e) eqn:He.
  - iModIntro; iPureIntro; eauto.
  - iApply fupd_plain_mask.
    iMod ("Hwp" $! _ [] with "HSI") as "[Hs Hwp]".
    iModIntro; destruct s; [iDestruct "Hs" as %?|]; eauto.
Qed.

Lemma wp_other_not_stuck `{!irisG Λ Σ M} efs σ κs s Φ n st :
  state_interp σ κs n st -∗
  ([∗ list] e ∈ efs, WP e @ s; ⊤ {{Φ}}) ={⊤}=∗
  state_interp σ κs n st ∗
  ([∗ list] e ∈ efs, WP e @ s; ⊤ {{Φ}}) ∗
  ⌜∀ e, e ∈ efs → s = NotStuck → not_stuck e σ⌝.
Proof.
  iIntros "HSI Hwp".
  rewrite assoc.
  iApply fupd_plain_keep_r; iFrame.
  iIntros "[HSI Hwp]".
  iIntros (e He).
  iDestruct (big_sepL_elem_of with "Hwp") as "Hwp"; [done|].
  iMod (wp_not_stuck with "HSI Hwp") as "(_ & _ & ?)"; done.
Qed.

Lemma wp_of_val_post `{!irisG Λ Σ M} e s Φ :
  WP e @ s; ⊤ {{ v, Φ v }} ={⊤}=∗
  from_option Φ True (to_val e) ∗
  (from_option Φ True (to_val e) -∗ WP e @ s; ⊤ {{ v, Φ v }}).
Proof.
  iIntros "Hwp".
  rewrite wp_unfold /wp_pre.
  destruct (to_val e) eqn:He.
  - iMod "Hwp"; simpl; iFrame; auto.
  - iModIntro.
    iSplit; first done.
    iIntros "_"; done.
Qed.

Lemma wp_of_val_post_other `{!irisG Λ Σ M} efs s Φ :
  ([∗ list] e ∈ efs, WP e @ s; ⊤ {{Φ}}) ={⊤}=∗
  ([∗ list] v ∈ omap to_val efs, Φ v) ∗
  (([∗ list] v ∈ omap to_val efs, Φ v) -∗ ([∗ list] e ∈ efs, WP e @ s; ⊤ {{Φ}})).
Proof.
  iIntros "Hefs".
  iInduction efs as [|e efs IHefs] "IH"; simpl; first done.
  iDestruct "Hefs" as "[Hwp Hefs]".
  iMod (wp_of_val_post with "Hwp") as "[Hpost Hback]".
  iMod ("IH" with "Hefs") as "[Hefspost Hefsback]".
  iModIntro.
  destruct (to_val e); simpl.
  - iFrame.
    iIntros "[Hpost Hefspost]".
    iSplitL "Hpost Hback"; [iApply "Hback"|iApply "Hefsback"]; iFrame.
  - iFrame.
    iIntros "Hefspost".
    iSplitL "Hback"; [iApply "Hback"|iApply "Hefsback"]; iFrame; done.
Qed.

Lemma take_step `{!irisG Λ Σ M} s Φ c κ c' κs es st :
  step c κ c' →
  hd_error c.1 = Some es →
  state_interp c.2 κs (length (tail c.1)) st -∗
  WP es @ s; ⊤ {{ v, Φ v }} -∗
  ([∗ list] ef ∈ tail c.1, WP ef @ s; ⊤ {{ v, fork_post v }}) ={⊤}[∅]▷=∗
  ⌜∀ e2, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2⌝ ∗
  ∃ st', ⌜st' = st ∨ M st st'⌝ ∗
  state_interp c'.2 (κs ++ κ) (length (tail c'.1)) st' ∗
  ∃ es', ⌜hd_error c'.1 = Some es'⌝ ∗
    from_option Φ True (to_val es') ∗
    ([∗ list] v ∈ omap to_val (tail c'.1), fork_post v) ∗
    (from_option Φ True (to_val es') -∗
      ([∗ list] v ∈ omap to_val (tail c'.1), fork_post v) -∗
      WP es' @ s; ⊤ {{ v, Φ v }} ∗
      ([∗ list] ef ∈ tail c'.1, WP ef @ s; ⊤ {{ v, fork_post v }})).
Proof.
  iIntros (Hstep Hes) "HSI Hes Hother".
  destruct c as [[|e1 t1] σ1']; simplify_eq/=.
  inversion Hstep as [? σ1 ? ? ? t21 t22 ? ? Hpstep]; simplify_eq/=.
  destruct t21; simplify_eq/=.
  - iMod (wp_take_step with "HSI Hes") as "Hwp"; [done|].
    iModIntro; iNext; iMod "Hwp" as (st') "(% & HSI & Hwp & Hefs)".
    iCombine "Hother" "Hefs" as "Hother".
    rewrite -big_sepL_app.
    iMod (wp_not_stuck with "HSI Hwp") as "(HSI & Hwp & %)".
    iMod (wp_other_not_stuck with "HSI Hother") as "(HSI & Hother & %)".
    iMod (wp_of_val_post with "Hwp") as "(Hpost & Hback)".
    iMod (wp_of_val_post_other with "Hother") as "(Hpostother & Hbackother)".
    iModIntro.
    rewrite Nat.add_comm app_length.
    iSplit.
    { iIntros (? -> [->|]%elem_of_cons); auto. }
    iExists _; iSplit; first done.
    iFrame "HSI Hpostother".
    iExists _; iSplit; first done.
    iFrame.
    iIntros "Hpost Hpostother".
    iSplitL "Hpost Hback"; [iApply "Hback"|iApply "Hbackother"]; done.
  - rewrite big_sepL_app /=.
    iDestruct "Hother" as "(Ho1 & Hwp & Ho2)".
    iMod (wp_take_step with "HSI Hwp") as "Hwp"; [done|].
    iModIntro; iNext; iMod "Hwp" as (st') "(% & HSI & Hwp & Hefs)".
    iAssert ([∗ list] ef ∈ (t21 ++ e2 :: t22 ++ efs),
             WP ef @ s; ⊤ {{ v, fork_post v }})%I with "[Ho1 Hwp Ho2 Hefs]"
      as "Hother".
    { rewrite big_sepL_app /=; iFrame. }
    iMod (wp_not_stuck with "HSI Hes") as "(HSI & Hes & %)".
    iMod (wp_other_not_stuck with "HSI Hother") as "(HSI & Hother & %)".
    iMod (wp_of_val_post with "Hes") as "(Hpostes & Hbackes)".
    iMod (wp_of_val_post_other with "Hother") as "(Hpostother & Hbackother)".
    iModIntro.
    rewrite Nat.add_comm -app_length -app_assoc /= !app_length /=.
    iSplit.
    { iIntros (? -> [->|]%elem_of_cons); auto. }
    iExists _; iSplit; first done.
    iFrame "HSI Hpostother".
    iExists _; iSplit; first done.
    iFrame.
    iIntros "Hpost Hpostother".
    iSplitL "Hpost Hbackes"; [iApply "Hbackes"|iApply "Hbackother"]; done.
Qed.

Theorem wp_strong_adequacy_helper Σ M Λ `{!invPreG Σ}
        (s: stuckness) (φ : execution_trace Λ → auxiliary_trace M → Prop) e1 σ1 κs st :
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → M → iProp Σ)
         (Φ fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ M := IrisG _ _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 st ∗
       WP e1 @ s; ⊤ {{ Φ }} ∗
       □ (∀ (ex : execution_trace Λ) (sm : auxiliary_trace M) st' st'' c κ κs' t2 e2 t2' σ2,
         ⌜exec_starts_in ex ([e1], σ1)⌝ -∗
         ⌜sim_starts_in sm st⌝ -∗
         ⌜exec_ends_in ex c⌝ -∗
         ⌜sim_ends_in sm st'⌝ -∗
         ⌜φ ex sm⌝ -∗
         ⌜step c κ (t2, σ2)⌝ -∗
         ⌜st'' = st' ∨ M st' st''⌝ -∗
         ⌜t2 = e2 :: t2'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2⌝ -∗
         stateI σ2 (κs' ++ κ) (length t2') st'' -∗
         from_option Φ True (to_val e2) -∗
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         |={⊤, ∅}=>
          ⌜ φ (exec_extend ex (t2, σ2) κ) (sim_extend sm st'') ⌝)) →
  ⊢ wptp Σ M s φ (singleton_exec ([e1], σ1)) (singleton_sim st).
Proof.
  intros Hwp.
  iMod wsat_alloc as (Hinv) "[Hw HE]".
  iPoseProof Hwp as "Hwp".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("Hwp" with "[$Hw $HE]") as ">[Hw [HE Hwp']]".
  iClear "Hwp".
  iDestruct "Hwp'" as (stateI Φ fork_post) "(HSI & Hwp & #Hstep)".
  clear Hwp.
  set (IrisG Λ Σ M Hinv stateI fork_post).
  pose proof (singleton_exec_starts_in ([e1], σ1)) as Hexpst.
  pose proof (singleton_exec_ends_in ([e1], σ1)) as Hexpen.
  pose proof (singleton_sim_starts_in st) as Hsmst.
  pose proof (singleton_sim_ends_in st) as Hsmen.
  set (es := e1) at 2.
  set (est := st) at 2.
  assert (hd_error ([e1], σ1).1 = Some es) as Hes by done.
  change st with est in Hsmen at 2.
  clearbody es est.
  set (other := tail ([e1], σ1).1).
  (* The following is annoying but if I don't include something blatantly
     ephemeral the proofmode puts the result automatically in the persistent
     context! *)
  iAssert (stateI σ1 κs 0 est ∗
           [∗ list] ef ∈ other, WP ef @ s; ⊤ {{ fork_post }})%I
    with "[HSI]" as "[HSI Hother]"; [by iFrame|].
  change 0 with (length other).
  set (exp := singleton_exec ([e1], σ1)) in *.
  set (smp := singleton_sim st) in *.
  clearbody exp smp.
  set ([e1], σ1) as c2 in Hexpen, Hes, other.
  change σ1 with (c2.2) at 2.
  clearbody c2.
  unfold other; clear other.
  iLöb as "IH" forall (exp smp c2 es est Hes κs Hsmen Hexpen Hexpst Hsmst)
                      "Hwp Hother".
  rewrite {2}/wptp (fixpoint_unfold (wptp_pre _ _ _ _) _ _).
  iIntros (Hvl Hφ c c' κ st' Hends Hsmends Hstep).
  pose proof (exec_ends_in_inj exp c c2 Hends Hexpen); simplify_eq.
  pose proof (sim_ends_in_inj smp est st' Hsmen Hsmends); simplify_eq.
  destruct c2 as [[|e2 t2] σ2]; simplify_eq/=.
  iPoseProof (take_step _ _ ((_ :: _), _) with "[$HSI] Hwp Hother") as "Hstp";
    [done|done|].
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("Hstp" with "[$Hw $HE]") as ">(Hw & HE & Hstp)".
  iNext.
  iMod ("Hstp" with "[$Hw $HE]") as ">(Hw & HE & % & H)".
  iDestruct "H" as (st'') "(% & HSI & H)".
  iDestruct "H" as (es' Hes') "(Hpost & Hfpost & Hback)".
  destruct c' as [[|e2' t2'] σ2']; simplify_eq/=.
  iAssert (▷ ⌜φ (exec_extend exp (es' :: t2', σ2') κ) (sim_extend smp st'')⌝)%I
    as "#Hextend".
  { iMod ("Hstep"
           with "[] [] [] [] [] [] [] [] [] HSI Hpost Hfpost [$Hw $HE]")
      as ">(Hw & HE & %)"; done. }
  iDestruct ("Hback" with "Hpost Hfpost") as "[Hes' Hother]".
  iNext.
  iExists _; iSplit; first done.
  iSplit; first done.
  iSpecialize ("IH" $! (exec_extend exp (es' :: t2', σ2') κ)
                    (sim_extend smp st'') (es' :: t2', σ2') es' st'' with "[]");
    [done|].
  iApply ("IH" with "[] [] [] [] Hw HE HSI Hes' Hother");
    eauto using exec_extend_ends_in, exec_extend_starts_in,
    sim_extend_ends_in, sim_extend_starts_in.
Qed.

Definition monotone {A} (Ψ : (A → Prop) → (A → Prop)) :=
  ∀ (P Q : A → Prop), (∀ x, P x → Q x) → ∀ x, Ψ P x → Ψ Q x.

Definition GFX {A} (Ψ : (A → Prop) → (A → Prop)) : A → Prop :=
  λ x, ∃ P, P x ∧ (∀ x, P x → Ψ P x).

Lemma GFX_post_fixpoint {A} (Ψ : (A → Prop) → (A → Prop)) :
  monotone Ψ → ∀ x, GFX Ψ x → Ψ (GFX Ψ) x.
Proof.
  intros Hmono x (P & HP & HΨP).
  eapply Hmono; [|by apply HΨP].
  intros; exists P; split; auto.
Qed.

Lemma GFX_fixpoint {A} (Ψ : (A → Prop) → (A → Prop)) :
  monotone Ψ → ∀ x, Ψ (GFX Ψ) x ↔ GFX Ψ x.
Proof.
  intros Hmono x; split.
  - intros HΨ.
    exists (Ψ (GFX Ψ)); split; first done.
    intros ? ?; eapply Hmono; last done.
    apply GFX_post_fixpoint; done.
  - apply GFX_post_fixpoint; done.
Qed.

Definition pure_wptp_pre {Λ M} (φ : execution_trace Λ → auxiliary_trace M → Prop)
           (pure_wptp : execution_trace Λ → auxiliary_trace M → Prop) :
  execution_trace Λ → auxiliary_trace M → Prop :=
  λ ex sm,
  valid_exec ex →
  φ ex sm →
  ∀ c c' κ st,
    exec_ends_in ex c →
    sim_ends_in sm st →
    step c κ c' →
    ∃ st', (st' = st ∨ M st st') ∧
           φ (exec_extend ex c' κ) (sim_extend sm st') ∧
           pure_wptp (exec_extend ex c' κ) (sim_extend sm st').

Lemma pure_wptp_pre_mono {Λ M} (φ : execution_trace Λ → auxiliary_trace M → Prop) :
  monotone
    (λ ψ (exsm : execution_trace Λ * auxiliary_trace M),
     (pure_wptp_pre φ (λ ex sm, ψ (ex, sm)) exsm.1 exsm.2)).
Proof.
  intros P Q HPQ [ex sm] HP ? ? ? ? ? ? ? ? ?.
  edestruct HP as (?&?&?&?); eauto.
Qed.

Definition pure_wptp {Λ M} (φ : execution_trace Λ → auxiliary_trace M → Prop) :=
  λ ex sm,
  GFX (λ ψ (exsm : execution_trace Λ * auxiliary_trace M),
       (pure_wptp_pre φ (λ ex sm, ψ (ex, sm)) exsm.1 exsm.2)) (ex, sm).

Theorem wp_strong_adequacy Σ M Λ `{!invPreG Σ}
        (s: stuckness) (φ : execution_trace Λ → auxiliary_trace M → Prop) e1 σ1 κs st :
  (∀ st, smaller_card (sig (λ st', st' = st ∨ M st st')) nat) →
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → M → iProp Σ)
         (Φ fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ M := IrisG _ _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 st ∗
       WP e1 @ s; ⊤ {{ Φ }} ∗
       □ (∀ (ex : execution_trace Λ) (sm : auxiliary_trace M) st' st'' c κ κs' t2 e2 t2' σ2,
         ⌜exec_starts_in ex ([e1], σ1)⌝ -∗
         ⌜sim_starts_in sm st⌝ -∗
         ⌜exec_ends_in ex c⌝ -∗
         ⌜sim_ends_in sm st'⌝ -∗
         ⌜φ ex sm⌝ -∗
         ⌜step c κ (t2, σ2)⌝ -∗
         ⌜st'' = st' ∨ M st' st''⌝ -∗
         ⌜t2 = e2 :: t2'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2⌝ -∗
         stateI σ2 (κs' ++ κ) (length t2') st'' -∗
         from_option Φ True (to_val e2) -∗
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         |={⊤, ∅}=>
          ⌜ φ (exec_extend ex (t2, σ2) κ) (sim_extend sm st'') ⌝)) →
  pure_wptp φ (singleton_exec ([e1], σ1)) (singleton_sim st).
Proof.
  intros Hsc Hwptp%wp_strong_adequacy_helper; last done.
  exists (λ exsm, ⊢ wptp Σ M s φ exsm.1 exsm.2); split; first done.
  clear Hwptp.
  intros [ex sm] Hwptp; simpl.
  intros Hvl Hφ c c' κ st' Hsmends Hsimends Hstep.
  revert Hwptp.
  rewrite {1}/wptp (fixpoint_unfold (wptp_pre _ _ _ _) _ _); intros Hwptp;
    simpl in *.
  apply (extract_impl ⌜_⌝) in Hwptp; last by apply extract_pure.
  apply (extract_impl ⌜_⌝) in Hwptp; last by apply extract_pure.
  revert Hwptp; rewrite extract_forall; intros Hwptp.
  specialize (Hwptp c).
  revert Hwptp; rewrite extract_forall; intros Hwptp.
  specialize (Hwptp c').
  revert Hwptp; rewrite extract_forall; intros Hwptp.
  specialize (Hwptp κ).
  revert Hwptp; rewrite extract_forall; intros Hwptp.
  specialize (Hwptp st').
  apply (extract_impl ⌜_⌝) in Hwptp; last by apply extract_pure.
  apply (extract_impl ⌜_⌝) in Hwptp; last by apply extract_pure.
  apply (extract_impl ⌜_⌝) in Hwptp; last by apply extract_pure.
  revert Hwptp; rewrite !extract_later; intros Hwptp.
  apply extract_exists_alt in Hwptp as [st'' Hwptp]; last done.
  exists st''.
  revert Hwptp.
  rewrite !extract_and.
  rewrite !extract_pure; done.
Qed.




















































From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import wsat.
From aneris.program_logic Require Export weakestpre.
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)
Section adequacy.
Context `{!irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.

Definition config_wp : iProp Σ :=
  (□ ∀ σ1 δ1 κ σ2 κs nt,
        ⌜config_step σ1 κ σ2⌝ →
        state_interp σ1 δ1 κs nt ={⊤}[∅]▷=∗
          ∃ δ2, ⌜state_variant σ1 δ1 σ2 δ2⌝ ∗ state_interp σ2 δ2 (κs ++ κ) nt).

Lemma wp_step s e1 σ1 δ1 κ κs e2 σ2 efs nt Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 δ1 κs nt -∗ WP e1 @ s; ⊤ {{ Φ }} ={⊤}[∅]▷=∗
    ∃ δ2, ⌜state_variant σ1 δ1 σ2 δ2⌝ ∗
    state_interp σ2 δ2 (κs ++ κ) (nt + length efs) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗
    wptp s efs (replicate (length efs) fork_post).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  rewrite Nat.add_comm; setoid_rewrite big_sepL2_replicate_r; done.
Qed.

Lemma wptp_step s es1 es2 κ κs σ1 δ1 σ2 Φs nt :
  step (es1,σ1) κ (es2, σ2) →
  config_wp -∗
  state_interp σ1 δ1 κs nt -∗ wptp s es1 Φs -∗
  ∃ nt', |={⊤}[∅]▷=>
        ∃ δ2, ⌜state_variant σ1 δ1 σ2 δ2⌝ ∗
          state_interp σ2 δ2 (κs ++ κ) (nt + nt') ∗
          wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  iIntros (Hstep) "Hcfgwp Hσ Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep|]; simplify_eq/=.
  - iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
    iExists _. iMod (wp_step with "Hσ Ht") as "H"; first done.
    iIntros "!> !>". iMod "H" as (δ2) "(Hsv & Hσ & He2 & Hefs)". iIntros "!>".
    iExists δ2; iSplit; first done.
    rewrite -(assoc_L app) -app_comm_cons. iFrame.
  - iExists 0.
    iMod ("Hcfgwp" with "[] Hσ") as "Hσ"; first done.
    iModIntro; iNext; iMod "Hσ"; iModIntro.
    rewrite right_id_L Nat.add_0_r; iFrame; eauto.
Qed.

Lemma wptp_steps s n es1 es2 κs κs' σ1 δ1 σ2 Φs nt :
  nsteps n (es1, σ1) κs (es2, σ2) →
  config_wp -∗ state_interp σ1 δ1 κs' nt -∗ wptp s es1 Φs
  ={⊤}[∅]▷=∗^n ∃ nt' δ2,
    state_interp σ2 δ2 (κs' ++ κs) (nt + nt') ∗ wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  revert nt es1 es2 κs κs' σ1 δ1 σ2 Φs.
  induction n as [|n IH]=> nt es1 es2 κs κs' σ1 δ1 σ2 Φs /=.
  { inversion_clear 1; iIntros "? ? ?"; iExists 0, δ1 => /=.
    rewrite Nat.add_0_r !right_id_L. by iFrame. }
  iIntros (Hsteps) "#Hcfgwp Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  iDestruct (wptp_step with "[] Hσ He") as (nt') ">H"; [done|done|]; simplify_eq.
  iIntros "!> !>". iMod "H" as (δ2) "(Hsv & Hσ & He)". iModIntro.
  iApply (step_fupdN_wand with "[Hσ He]").
  { by iApply (IH with "[] Hσ He"). }
  iDestruct 1 as (nt'' δ3) "[??]".
  rewrite -(assoc_L (++)).
  rewrite -Nat.add_assoc -(assoc_L app) -replicate_plus.
  by eauto with iFrame.
Qed.

Lemma wp_not_stuck κs nt e σ δ Φ :
  state_interp σ δ κs nt -∗ WP e {{ Φ }} ={⊤}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ δ [] κs with "Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_strong_adequacy Φs κs' s n es1 es2 κs σ1 δ1 σ2 nt:
  nsteps n (es1, σ1) κs (es2, σ2) →
  config_wp -∗ state_interp σ1 δ1 κs' nt -∗
  wptp s es1 Φs ={⊤}[∅]▷=∗^(S n) ∃ nt' δ2,
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 δ2 (κs' ++ κs) (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post,
      from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "#Hcfgwp Hσ He". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "[] Hσ He") as "Hwp"; [done|done|].
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (nt' δ2) "(Hσ & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝%I
    (state_interp σ2 δ2 (κs' ++ κs) (nt + nt') ∗
    wptp s es2 (Φs ++ replicate nt' fork_post))%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (e' -> He').
    move: He' => /(elem_of_list_split _ _)[?[?->]].
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto. }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iExists _, _. iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. iApply (wp_value_inv' with "Hwp").
Qed.
End adequacy.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ Λ `{!invPreG Σ} es σ1 n κs t2 σ2 φ :
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI σ1 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
         (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_intro_mask'] or [fupd_mask_weaken] to introduce the
         fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
  iMod Hwp as (s stateI Φ fork_post) "(#Hcfgwp & Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iApply step_fupd_intro; [done|]; iModIntro.
  iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "[-Hφ]").
  { iApply (@wptp_strong_adequacy _ _ (IrisG _ _ Hinv stateI fork_post) _ []
    with "[] [Hσ] Hwp"); eauto; by rewrite right_id_L. }
  iDestruct 1 as (nt' ?) "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite replicate_length in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  iApply fupd_plain_mask_empty.
  iApply ("Hφ" with "[//] [%] [//] Hσ Hes'"); [congruence|].
  by rewrite big_sepL2_replicate_r // big_sepL_omap.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

Corollary wp_adequacy Σ Λ `{!invPreG Σ} s e σ φ :
  (∀ `{Hinv : !invG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv (λ σ κs _, stateI σ κs) fork_post in
       config_wp ∗ stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "(Hcfgwp & Hσ & Hwp)".
  iExists s, (λ σ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post => /=.
  iIntros "{$Hcfgwp $Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_weaken; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Corollary wp_invariance Σ Λ `{!invPreG Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       config_wp ∗ stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hcfgwp & Hσ & Hwp & Hφ)".
  iExists s, stateI, [(λ _, True)%I], fork_post => /=.
  iIntros "{$Hcfgwp $Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_weaken; first set_solver.
Qed.
