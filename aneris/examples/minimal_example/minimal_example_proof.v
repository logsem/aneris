From stdpp Require Import finite.
From trillium.prelude Require Import quantifiers finitary.
From iris.algebra Require Import auth excl csum agree.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import gset_map misc.
From aneris.aneris_lang.state_interp Require Import state_interp.
From aneris.aneris_lang Require Import
     lang resources network events proofmode adequacy.
From aneris.examples Require Export minimal_example_code.


Definition incr_exampleM : Model := model nat (λ m n, n = (m + 1)%nat) 0%nat.

Definition incr_res : cmra := authR (optionUR (csumR (exclR unitO) (agreeR (leibnizO loc)))).

Section resources.
  Context `{!inG Σ incr_res}.

  Definition oloc_to_res (ol : option loc) : option (csum (excl unit) (agree loc)) :=
    match ol with
    | Some l => Some (Cinr (to_agree l))
    | None => Some (Cinl (Excl ()))
    end.

  Definition incrloc_full (γ : gname) (ol : option loc) : iProp Σ :=
    own γ (● oloc_to_res ol).

  Definition incrloc_frag (γ : gname) (ol : option loc) : iProp Σ :=
    own γ (◯ oloc_to_res ol).

  Lemma incloc_create : ⊢ |==> ∃ γ, incrloc_full γ None ∗ incrloc_frag γ None.
  Proof. setoid_rewrite <- own_op; apply own_alloc. apply auth_both_valid; done. Qed.

  Lemma incrloc_agree γ ol ol' : incrloc_full γ ol -∗ incrloc_frag γ ol' -∗ ⌜ol = ol'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvl.
    apply auth_both_valid_discrete in Hvl as [Hvl1 Hvl2].
    destruct ol; destruct ol'; [| | |done].
    - apply Some_csum_included in Hvl1 as [|[(?&?&?&?)|(?&?&?&?&Hvl1)]]; simplify_eq.
      revert Hvl1; rewrite Some_included_total; intros ->%to_agree_included%leibniz_equiv; done.
    - apply Some_csum_included in Hvl1 as [|[(?&?&?&?&?)|(?&?&?&?&?)]]; simplify_eq.
    - apply Some_csum_included in Hvl1 as [|[(?&?&?&?&?)|(?&?&?&?&?)]]; simplify_eq.
  Qed.

  Lemma incrloc_update γ l :
    incrloc_full γ None -∗ incrloc_frag γ None ==∗ incrloc_full γ (Some l) ∗ incrloc_frag γ (Some l).
  Proof.
    iIntros "H1 H2".
    setoid_rewrite <- own_op.
    iApply (own_update_2 with "H1 H2").
    apply auth_update.
    apply option_local_update.
    apply exclusive_local_update; done.
  Qed.

End resources.

Section proof.
  Context `{!anerisG incr_exampleM Σ, !inG Σ incr_res}.

  Context (ip : ip_address).

  Definition ICIname : namespace := nroot .@ "incr".

  Definition incr_inv γ : iProp Σ :=
    inv ICIname ((incrloc_full γ None ∗ alloc_evs "s" [] ∗ frag_st 0%nat) ∨
                 (∃ l (n : nat), incrloc_full γ (Some l) ∗
                    l ↦[ip] #n ∗
                    (∃ σ h, alloc_evs "s" [allocObs ip "s" l #0 σ h] ∗
                        ⌜valid_allocObs ip l σ h⌝) ∗
                    frag_st n)).

  Lemma incr_inv_init γ E :
    incrloc_full γ None -∗ alloc_evs "s" [] -∗ frag_st 0%nat ={E}=∗ incr_inv γ.
  Proof.
    iIntros "? ? ?".
    iApply inv_alloc; iNext; iLeft; iFrame.
  Qed.

  Lemma WP_incr_loop γ l :
    {{{incr_inv γ ∗ incrloc_frag γ (Some l) }}} incr_loop #l @[ip] {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "#[Hinv Hl] _".
    iLöb as "IH".
    rewrite /incr_loop.
    wp_pures.
    wp_bind (!_)%E.
    iInv ICIname as "[[>H _]|H]" "Hcl".
    { iDestruct (incrloc_agree with "H Hl") as %?; done. }
    iDestruct "H" as (l' n) "(>Hfl & Hln & Hev & Hfg)".
    iDestruct (incrloc_agree with "Hfl Hl") as %?; simplify_eq.
    wp_load.
    iMod ("Hcl" with "[Hfl Hln Hev Hfg]") as "_".
    { iRight; iExists _, _; iFrame. }
    iModIntro.
    wp_pures.
    wp_bind (CAS _ _ _).
    iInv ICIname as "[[>H _]|H]" "Hcl".
    { iDestruct (incrloc_agree with "H Hl") as %?; done. }
    iDestruct "H" as (l' m) "(>Hfl & Hln & Hev & >Hfg)".
    iDestruct (incrloc_agree with "Hfl Hl") as %?; simplify_eq.
    destruct (decide (n = m)) as [->|].
    - iApply aneris_wp_atomic_take_step_model.
      iModIntro.
      iExists _, (m + 1)%nat; iFrame; iSplit.
      { iPureIntro; right; done. }
      wp_cas_suc.
      iIntros "Hfg".
      iApply fupd_mask_intro; first done.
      iIntros "_".
      iMod ("Hcl" with "[Hfl Hln Hev Hfg]") as "_".
      { replace #(m + 1) with #(m + 1)%nat by by repeat f_equal; lia.
        iRight; iExists _, _; iFrame. }
      iModIntro.
      do 2 wp_pure _; done.
    - wp_cas_fail.
      { intros ?; simplify_eq. }
      iMod ("Hcl" with "[Hfl Hln Hev Hfg]") as "_".
      { iRight; iExists _, _; iFrame. }
      iModIntro.
      do 2 wp_pure _; done.
  Qed.

  Lemma WP_incr_example γ :
    {{{incr_inv γ ∗ incrloc_frag γ None }}} incr_example @[ip] {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hl] _".
    rewrite /incr_example.
    wp_bind (ref<<_>> _)%E.
    iInv ICIname as "[H|H]" "Hcl"; last first.
    { iDestruct "H" as (? ?) "[>H _]".
      iDestruct (incrloc_agree with "H Hl") as %?; done. }
    iDestruct "H" as "(Hfl & Hev & Hfg)".
    wp_apply (aneris_wp_alloc_tracked with "Hev").
    iIntros (l h σ) "(Hl0 & Hev1 & Hev2)".
    iMod (incrloc_update with "Hfl Hl") as "[Hfl #Hl]".
    iMod ("Hcl" with "[Hfl Hl0 Hev1 Hev2 Hfg]") as "_".
    { iNext; iRight. iExists _, _; iFrame; eauto. }
    iModIntro.
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL.
    - iNext.
      wp_pures.
      iApply WP_incr_loop; [by iFrame "#"|].
      iNext; iIntros "?"; done.
    - iNext.
      iApply WP_incr_loop; [by iFrame "#"|].
      iNext; iIntros "?"; done.
  Qed.

End proof.

Definition heap_grows (c c' : cfg aneris_lang) : Prop :=
  dom c.2.(state_heaps) ⊆ dom c'.2.(state_heaps) ∧
  ∀ ip h h',
    c.2.(state_heaps) !! ip = Some h →
    c'.2.(state_heaps) !! ip = Some h' →
    dom h ⊆ dom h'.

Global Instance heap_grows_PreOder : PreOrder heap_grows.
Proof.
  rewrite /heap_grows; split; first by intros ?; set_solver.
  intros c1 c2 c3 [Hc121 Hc122] [Hc231 Hc232].
  split; first set_solver.
  intros ip h h' Hh Hh'.
  assert (is_Some (c2.2.(state_heaps) !! ip)) as [h'' Hh''].
  { apply elem_of_dom. apply elem_of_dom_2 in Hh. set_solver. }
  set_solver.
Qed.

Lemma valid_exec_heap_grows (ex : execution_trace aneris_lang) :
  valid_exec ex → trace_steps (λ x _ y, heap_grows x y) ex.
Proof.
  induction ex as [c|ex IHex c']; first by constructor.
  intros Hexvl.
  eapply valid_exec_exec_extend_inv in Hexvl as [Hecvl (c & <-%last_eq_trace_ends_in & Hstep)].
  econstructor; [done| |by apply IHex].
  rewrite /heap_grows.
  inversion Hstep as [????????? Htrl ? Hpstep|????? Htrl ? Hcfgstep]; simplify_eq/=; last first.
  { rewrite Htrl; simpl in *.
    inversion Hcfgstep; simpl in *; set_solver. }
  rewrite Htrl; simpl in *.
  inversion Hpstep as [????? Hhstep]; simplify_eq/=.
  inversion Hhstep as [??????? Hbstep|ip' ??????? Hbstep|ip' |]; simplify_eq/=.
  - inversion Hbstep; simplify_eq/=; set_solver.
  - rewrite dom_insert.
    split; first set_solver.
    intros ip.
    destruct (decide (ip = ip')) as [->|].
    + rewrite lookup_insert; intros ????; simplify_eq/=.
      inversion Hbstep; simplify_eq/=; set_solver.
    + rewrite lookup_insert_ne; last done; set_solver.
  - rewrite dom_insert.
    split; first set_solver.
    intros ip.
    destruct (decide (ip = ip')) as [->|].
    + rewrite lookup_insert; intros ????; simplify_eq/=.
    + rewrite lookup_insert_ne; last done; set_solver.
  - set_solver.
Qed.

Definition incr_sim ip (ex : execution_trace aneris_lang) (atr : finite_trace nat ()) : Prop :=
  trace_length ex = trace_length atr ∧
  ((events_of_trace (allocEV "s") ex = [] ∧ ∀ i n, atr !! i = Some n → n = 0)%nat ∨
  (∃ l (n : nat),
      (∃ σ h, events_of_trace (allocEV "s") ex = [allocObs ip "s" l #0 σ h] ∧
              valid_allocObs ip l σ h) ∧
      ∃ h,
        (trace_last ex).2.(state_heaps) !! ip = Some h ∧
        h !! l = Some #n ∧
        trace_last atr = n ∧
        (∀ i c h' v,
            ex !! i = Some c →
            state_heaps c.2 !! ip = Some h' →
            h' !! l = Some v →
            ∃ (m : nat), v = #m ∧ atr !! i = Some m ∧ m ≤ n) ∧
        (∀ m, m ≤ n → ∃ i c h',
              ex !! i = Some c ∧ state_heaps c.2 !! ip = Some h' ∧ h' !! l = Some #m ∧
              atr !! i = Some m)))%nat.

Definition init_state ip := {|
  state_heaps :=  {[ip := ∅ ]};
  state_sockets := {[ip := ∅ ]};
  state_ports_in_use := ∅;
  state_ms := ∅; |}.

Lemma incr_exampleM_finitary : aneris_model_rel_finitary incr_exampleM.
Proof.
  intros n.
  apply finite_smaller_card_nat.
  apply sig_finite_eq1.
Qed.

Lemma gcounter_adequacy ip :
  @continued_simulation aneris_lang (aneris_to_trace_model incr_exampleM)
    (incr_sim ip)
    {tr[ ([mkExpr ip incr_example], init_state ip) ]}
    {tr[ 0%nat ]}.
Proof.
  eapply (simulation_adequacy #[anerisΣ incr_exampleM; GFunctor incr_res] incr_exampleM
                              NotStuck ∅ {["s"]} ∅ ∅ ∅ (λ _, True) _ ip).
  { set_solver. }
  { set_solver. }
  { apply aneris_sim_rel_finitary, incr_exampleM_finitary. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
  iIntros (?) "!#".
  iExists (λ _, True)%I.
  iIntros "_ _ _ #? Hevs _ _ _ _ Hfg".
  rewrite big_sepS_singleton.
  assert (inG #[ anerisΣ incr_exampleM; GFunctor incr_res] incr_res).
  { assert (subG (GFunctor incr_res) #[ anerisΣ incr_exampleM; GFunctor incr_res]).
    apply _. solve_inG. }
  iMod incloc_create as (γ) "[Hf Hl]".
  iMod (incr_inv_init ip with "Hf Hevs Hfg") as "#Hinv".
  iModIntro.
  iSplit; [done|].
  iSplitL.
  { iPoseProof (WP_incr_example _ _ (λ _, True)%I with "[$Hl//] []") as "H".
    - iNext; iIntros "?"; done.
    - rewrite aneris_wp_unfold /aneris_wp_def.
      iApply (wp_wand with "[H]"); first by iApply "H".
      auto. }
  iIntros (ex atr c Hvs Hexs Hatrs Hexe Hcntr _) "(Hevs & HSI & Hmdl & %Hvalid & Hsteps) _".
  destruct (valid_system_trace_start_or_contract ex atr) as [[-> ->]|Hcontr]; first done.
  { erewrite !first_eq_trace_starts_in; [|eassumption|eassumption].
    iMod fupd_mask_subseteq as "_"; [|iModIntro]; first done.
    iPureIntro.
    split; [done|].
    left; split.
    - rewrite events_of_singleton_trace; done.
    - intros [] ? ?; simplify_eq/=; done. }
  destruct Hcontr as (ex' & atr' & oζ & ℓ & Hex' & Hatr').
  specialize (Hcntr ex' atr' oζ ℓ Hex' Hatr') as [Hlen Hmrel].
  rewrite /incr_sim.
  destruct atr as [|atr m]; first by apply not_trace_contract_singleton in Hatr'.
  apply trace_contract_of_extend in Hatr'; simplify_eq.
  destruct ex as [|ex oζ' c']; first by apply not_trace_contract_singleton in Hex'.
  apply trace_contract_of_extend in Hex'; simplify_eq.
  iInv ICIname as ">[H|H]" "_"; iApply fupd_mask_intro_discard; [set_solver| |set_solver|].
  - iDestruct "H" as "(Hfl & Haev & Hfg)".
    rewrite /incr_sim.
    simpl.
    destruct Hex' as [-> ->]. destruct Hatr' as [-> ->].
    iSplit; [rewrite /= Hlen //|].
    iLeft.
    iDestruct "Hevs" as (? ? lbls) "(_ & _ & _ & _ & _ & Hevs)".
    iDestruct (alloc_evs_lookup with "Hevs Haev") as %Haevlu.
    apply lookup_fn_to_gmap in Haevlu as [Haevs _].
    rewrite Haevs.
    iSplit; first done.
    iIntros (i n Hin).
    destruct (decide (i = trace_length atr)).
    + rewrite trace_lookup_last in Hin; last by simpl in *; lia.
      simplify_eq. simpl.
      iDestruct (auth_frag_st_agree with "Hmdl Hfg") as %->; done.
    + destruct (events_of_trace_extend_app (allocEV "s") ex c' oζ) as (evs & Hevslen & Hevs & _).
      { eapply valid_system_trace_valid_exec_trace; done. }
      rewrite Haevs in Hevs.
      symmetry in Hevs; apply app_eq_nil in Hevs as [Hevs _].
      pose proof (trace_lookup_lt_Some_1 _ _ _ Hin); simpl in *.
      rewrite trace_lookup_extend_lt in Hin; last lia.
      destruct Hmrel as [Hmrel|Hmrel]; last first.
      { rewrite Hevs in Hmrel. destruct Hmrel as (?&?&(?&?&?&?)&?); done. }
      iPureIntro.
      by eapply Hmrel.
  - iDestruct "H" as (l n) "(Hfl & Hln & Haev & Hfg)".
    iDestruct "Haev" as (σ h) "[Haev %Haevvl]".
    destruct Hex' as [-> ->]. destruct Hatr' as [-> ->].
    iSplit; [rewrite /= Hlen //|].
    iRight.
    iDestruct "Hevs" as (? ? lbls) "(_ & _ & _ & _ & _ & Hevs)".
    iDestruct (alloc_evs_lookup with "Hevs Haev") as %Haevlu.
    apply lookup_fn_to_gmap in Haevlu as [Haevs _].
    rewrite Haevs.
    iExists l, n.
    iSplit; first by eauto.
    iDestruct (aneris_state_interp_heap_valid with "HSI Hln") as %(h'&Hh'&Hh'ln).
    iExists _.
    iSplit; first done.
    iSplit; first done.
    iDestruct (auth_frag_st_agree with "Hmdl Hfg") as %Hst.
    destruct (events_of_trace_extend_app (allocEV "s") ex c' oζ) as (evs & Hevslen & Hevs & Hevs').
    { eapply valid_system_trace_valid_exec_trace; done. }
    iPureIntro.
    rewrite Haevs in Hevs.
    destruct (events_of_trace (allocEV "s") ex) as [|aev evs'] eqn:Haevseq.
    + destruct Hmrel as [Hmrel|Hmrel]; last first.
      { destruct Hmrel as (?&?&(?&?&?&?)&?); done. }
      assert (trace_last atr = 0) as Hatrlast.
      { apply Hmrel with (pred (trace_length atr)). apply trace_lookup_last.
        pose proof (trace_length_at_least atr); simpl in *; lia. }
      simplify_eq/=.
      split; first done.
      edestruct Hevs' as (K & tp1 & tp2 & efs & Hpres & Hpree & Hposts & Hposte);
        first by apply elem_of_list_singleton.
      simplify_eq/=.
      rewrite Hposts /= lookup_insert in Hh'; simplify_eq/=.
      rewrite lookup_insert in Hh'ln; simplify_eq/=.
      assert (n = 0) as -> by lia.
      split; last first.
      { intros m Hm.
        assert (m = 0) as -> by lia.
        eexists (trace_length ex), _, _.
        rewrite !trace_lookup_last //=; last rewrite Hlen //.
        split; first done.
        rewrite Hposts /= lookup_insert.
        split; first done.
        rewrite lookup_insert; done. }
      intros i c'' h' v Hi Hh' Hv.
      pose proof (trace_lookup_lt_Some_1 _ _ _ Hi); simpl in *.
      destruct (decide (i = trace_length ex)) as [->|].
      * rewrite trace_lookup_last in Hi; last done.
        simplify_eq/=.
        rewrite Hposts /= lookup_insert in Hh'.
        simplify_eq/=.
        rewrite lookup_insert in Hv; simplify_eq.
        eexists 0; split; first done.
        rewrite trace_lookup_last; simpl; eauto with lia.
      * assert (heap_grows c'' (trace_last ex)) as [_ Hheaps].
        { rewrite -rt_rtc_same.
          apply valid_system_trace_valid_exec_trace in Hvs.
          pose proof (trace_length_at_least ex).
          eapply (trace_steps_lookup
                    _ _ (valid_exec_heap_grows _ Hvs)
                    i (pred (trace_length ex)) c'' (trace_last ex)).
          - pose proof (trace_length_at_least ex).
            (* lia bug!? *)
            apply PeanoNat.Nat.lt_le_pred.
            apply Nat.le_neq; split; last done.
            apply lt_n_Sm_le; done.
          - done.
          - rewrite trace_lookup_extend_lt; last first.
            { apply lt_pred_n_n. eauto. }
            rewrite trace_lookup_last; [done|].
            rewrite -(S_pred _ 0) //. }
        destruct Haevvl as [Haevvl1 Haevvl2].
        specialize (Hheaps _ _ _ Hh' Haevvl1).
        assert (is_Some (h !! l)) as [? ?]; last by simplify_eq.
        apply (elem_of_dom (D := gset loc)).
        apply (elem_of_dom_2 (D := gset loc)) in Hv.
        set_solver.
    + simplify_eq Hevs; clear Hevs; intros <- Hevs.
      symmetry in Hevs; apply app_eq_nil in Hevs as [? ?]; simplify_eq/=.
      split; first done.
      destruct Hmrel as [Hmrel|Hmrel].
      { destruct Hmrel as [? ?]; done. }
      destruct Hmrel as (l' & k & Hl' & Hatrk & h'' & Hh'' & Hh''l'k & Hrel1 & Hrel2).
      destruct Hl' as (σ' & h3 & Haevs' & [Haevvl'1 Haevvl'2]).
      destruct Haevvl as [Haevvl1 Haevvl2].
      simplify_eq /=.
      assert (trace_last atr ≤ n ≤ trace_last atr + 1).
      { simpl in *. rewrite /user_model_evolution /= in Hvalid. lia. }
      split.
      * intros i c'' h4 v Hc'' Hh4 Hv.
        destruct (decide (i < trace_length ex)).
        -- rewrite trace_lookup_extend_lt in Hc''; last done.
           rewrite trace_lookup_extend_lt; last lia.
           destruct (Hrel1 i c'' h4 v) as (m' & ? & ? & ?); [done|done|done|]; simplify_eq.
           eauto with lia.
        -- pose proof (trace_lookup_lt_Some_1 _ _ _ Hc''); simpl in *.
           assert (i = trace_length ex) as ->. (* lia bug! *)
           { assert (i ≤ trace_length ex) by by apply lt_n_Sm_le. lia. }
           rewrite trace_lookup_extend; last by simpl in *; lia.
           rewrite trace_lookup_extend in Hc''; last done.
           simplify_eq; eauto.
      * intros m Hm.
        destruct (decide (m = n)) as [->|].
        { eexists (trace_length ex), _, _.
          repeat (rewrite trace_lookup_extend; last solve [lia|done]); done. }
        destruct (Hrel2 m) as (i & ? & ? & Hexi & ? & ? & ?); first lia.
        pose proof (trace_lookup_lt_Some_1 _ _ _ Hexi).
        eexists i, _, _.
        rewrite trace_lookup_extend_lt; last first.
        { assert (trace_length ex = trace_length atr) as <-. lia. done. }
        rewrite trace_lookup_extend_lt; done.
Qed.
