From iris.algebra Require Import auth gmap gset excl excl_auth gmultiset.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import locales_helpers comp_utils trace_lookup fairness fin_branch.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_em obligations_am obls_fairness_preservation obls_utils gset_prod.
From stdpp Require Import finite. 

Section FiniteBranching.
  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
    `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
  .

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  (* Context {Locale: Type}. *)
  Context {Λ: language}.
  Context `{Countable (locale Λ)}.
  Let Locale := locale Λ.

  Context {LIM_STEPS: nat}.
  Context (OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Let OM := ObligationsModel OP.

  Context `{Inhabited Locale}.

  Lemma burns_cp_next_states δ:
    list_approx (fun δ' => exists τ π d, burns_cp OP δ τ δ' π d). 
  Proof using.
    set (new_cps := map (fun cp => ps_cps _ δ ∖ {[+ cp +]}) (elements $ ps_cps _ δ)).
    exists (map (flip (update_cps OP) δ) new_cps). 
    intros ? (?&?&? & STEP).
    inversion STEP; subst; simpl in *. simpl.
    apply elem_of_list_In. apply in_map_iff. eexists. simpl. split; [reflexivity|].
    subst new_cps. apply in_map_iff. eexists. split; [reflexivity| ].
    apply elem_of_list_In. apply gmultiset_elem_of_elements. done.
  Qed.

  Lemma exchanges_cp_next_states δ d':
    list_approx (fun δ' => exists τ π d n, exchanges_cp OP δ τ δ' π d d' n). 
  Proof using.
    set (new_cps :=
           '(π, d) ← elements $ ps_cps _ δ;
           n ← seq 0 (ps_exc_bound _ δ + 1);
           mret (ps_cps _ δ ∖ {[+ (π, d) +]} ⊎ n *: {[+ (π, d') +]})).
    exists (map (flip (update_cps OP) δ) new_cps). 
    intros ? (?&?&?&?& STEP).
    inversion STEP; subst; simpl in *. simpl.
    apply elem_of_list_In. apply in_map_iff. eexists. simpl. split; [reflexivity|].
    subst new_cps. apply elem_of_list_In.
    apply elem_of_list_bind. eexists (_, _). split.
    2: { apply gmultiset_elem_of_elements. eauto. }
    apply elem_of_list_bind. eexists. rewrite elem_of_list_ret. split; [reflexivity| ].
    apply elem_of_seq. lia.
  Qed.

  Lemma creates_signal_next_states δ ℓ:
    list_approx (fun δ' => exists τ, creates_signal OP δ τ δ' ℓ).
  Proof using.
    set (s := next_sig_id _ δ). 
    set (new_sigs := <[ s := (ℓ, false) ]> (ps_sigs _ δ)).
    set (add_obl := 
           fun τ =>
             let cur_loc_obls := default ∅ (ps_obls _ δ !! τ) in
             <[ τ := cur_loc_obls ∪ {[ s ]} ]> (ps_obls _ δ)). 
    set (new_obls := map add_obl (elements $ dom $ ps_obls _ δ)).
    exists (map (flip (update_obls OP) (update_sigs OP new_sigs δ)) new_obls).
    intros ? (?& STEP).
    inversion STEP; subst; simpl in *. simpl.
    apply elem_of_list_In. apply in_map_iff. eexists. split; [reflexivity|].
    subst new_obls1. apply elem_of_list_In.
    subst new_obls. apply elem_of_list_In, in_map_iff. eexists. split; [reflexivity|].
    apply elem_of_list_In, elem_of_elements. done.
  Qed.

  Lemma sets_signal_next_states δ:
    list_approx (fun δ' => exists τ s, sets_signal OP δ τ δ' s). 
  Proof using.
    set (set_sig τs' :=
           let '(τ, s') := τs' in 
           let new_sigs := (map_imap (fun s '(ℓ, b) => Some (ℓ, (if (decide (s' = s)) then true else b))) (ps_sigs _ δ)) in
           let new_obls :=
             (let cur_loc_obls := default ∅ (ps_obls _ δ !! τ) in
              <[ τ := cur_loc_obls ∖ {[ s' ]} ]> (ps_obls _ δ)) in
           update_obls OP new_obls $ update_sigs OP new_sigs δ
           ). 
    exists (map set_sig (elements $ gset_prod (dom $ ps_obls _ δ) (dom $ ps_sigs _ δ))).
    intros ? (?&?& STEP). inversion STEP; subst; simpl in *. simpl.
    apply elem_of_list_In. apply in_map_iff.
    eexists (_, _). subst set_sig new_ps. split.
    { f_equal. f_equal. subst new_sigs0.
      apply map_eq. intros sid. rewrite map_lookup_imap. 
      destruct (decide (sid = x0)) as [->|?].
      { rewrite lookup_insert. rewrite SIG. simpl. rewrite decide_True; done. }
      rewrite lookup_insert_ne; [| done]. 
      destruct (ps_sigs OP δ !! sid) eqn:SID; rewrite SID; [| done].
      simpl. destruct s. rewrite decide_False; done. }
    apply elem_of_list_In, elem_of_elements.
    apply gset_prod_spec. simpl. split; eauto.
    by apply elem_of_dom.
  Qed.

  Lemma creates_ep_next_states δ d':
    list_approx (fun δ' => exists τ s π d, creates_ep OP δ τ δ' s π d d'). 
  Proof using.
    set (add_ep s_cp :=
           let '(s, (π, d)) := s_cp in
           let new_cps := ps_cps _ δ ∖ {[+ (π, d) +]} in
           let new_eps := ps_eps _ δ ∪ {[ (s, π, d') ]} in
           update_eps _ new_eps $ update_cps _ new_cps δ).
    exists (map add_ep (elements $ gset_prod (dom $ ps_sigs _ δ) (gmultiset_dom $ ps_cps _ δ))).
    intros ? (?&?&?&?& STEP). inversion STEP; subst; simpl in *. simpl.
    apply elem_of_list_In. apply in_map_iff.
    eexists (_, (_, _)). split; [reflexivity| ].
    apply elem_of_list_In, elem_of_elements.
    apply gset_prod_spec. simpl. split; eauto.
    by apply gmultiset_elem_of_dom.
  Qed.

  Lemma expects_ep_next_states δ:
    list_approx (fun δ' => exists τ s π d, expects_ep OP δ τ δ' s π d).
  Proof using.
    set (add_cp (ep: @ExpectPermission Degree) :=
           τ ← elements $ dom $ ps_phases _ δ;
           let πτ := default namespaces.nroot (ps_phases _ δ !! τ) in
           let cps' := let '(_, _, d) := ep in ps_cps _ δ ⊎ {[+ (πτ, d) +]} in
           let δ' := update_cps OP cps' δ in
           mret δ'
        ).
    exists (flat_map add_cp (elements $ ps_eps _ δ)).
    intros ? (?&?&?&?& STEP). inversion STEP; subst; simpl in *. simpl.
    apply elem_of_list_In. apply in_flat_map. eexists ((_, _), _).
    rewrite -!elem_of_list_In elem_of_elements. split; eauto.
    rewrite /add_cp. apply elem_of_list_bind. setoid_rewrite elem_of_list_ret.
    eexists. split.
    2: { apply elem_of_elements. eapply elem_of_dom; eauto. }
    rewrite LOC_PHASE. reflexivity. 
  Qed.

  Lemma forks_locale_next_states δ τ':
    list_approx (fun δ' => exists τ obls', forks_locale _ δ τ δ' τ' obls'). 
  Proof using.
    clear H1 H0 H. 
    exists (τπ0 ← map_to_list (ps_phases _ δ);
           let '(τ, π0) := τπ0 in
           let obls0 := default ∅ (ps_obls _ δ !! τ) in
           obls' ← elements $ powerset obls0;           
           let new_obls := <[ τ' := obls']> $ <[ τ := obls0 ∖ obls' ]> $ ps_obls _ δ in
           let new_phases := <[ τ' := fork_right π0 ]> $ <[ τ := fork_left π0 ]> $ ps_phases _ δ in
           mret (update_phases _ new_phases $ update_obls _ new_obls δ)).
    intros ? (?&?& STEP). inversion STEP; subst; simpl in *. simpl. 
    apply elem_of_list_bind. eexists (_, _).
    rewrite elem_of_list_bind. setoid_rewrite elem_of_list_ret.
    split.
    { eexists. split; [reflexivity| ].
      apply elem_of_elements. apply powerset_spec. set_solver. }
    by apply elem_of_map_to_list. 
  Qed.
    
  Lemma ex_and_comm' {T: Type} (A: Prop) (B: T -> Prop):
    (exists t, B t /\ A) <-> (exists t, B t) /\ A.
  Proof. 
    split.
    - intros (?&?&?); eauto.
    - intros ((?&?)&?); eauto.
  Qed.

  Section FinParams.
    Context (FINdeg: Finite Degree) (FINlvl: Finite Level).

    Lemma loc_step_approx δ:
      list_approx (fun δ' => exists τ, loc_step OP δ τ δ'). 
    Proof using FINlvl FINdeg.
      exists (
          proj1_sig (burns_cp_next_states δ) ++
            flat_map (fun d' => proj1_sig (exchanges_cp_next_states δ d')) (@enum _ _ FINdeg) ++
            flat_map (fun ℓ => proj1_sig (creates_signal_next_states δ ℓ)) (@enum _ _ FINlvl) ++
            proj1_sig (sets_signal_next_states δ) ++
            flat_map (fun d' => proj1_sig (creates_ep_next_states δ d')) (@enum _ _ FINdeg) ++
            proj1_sig (expects_ep_next_states δ)
        ).
      intros ? (?& STEP).
      rewrite !elem_of_app. 
      destruct STEP as [T|[T|[T|[T|[T|T]]]]]. 
      - destruct T as (?&?&T). left.
        destruct (burns_cp_next_states δ); eauto. 
      - destruct T as (?&?&?&?&T). do 1 right. left.
        apply elem_of_list_In, in_flat_map. setoid_rewrite <- elem_of_list_In.      
        eexists. split.
        { eapply elem_of_enum. Unshelve. eauto. }
        destruct exchanges_cp_next_states; eauto.
        eapply e; eauto. 
      - destruct T as (?&T). do 2 right. left.
        apply elem_of_list_In, in_flat_map. setoid_rewrite <- elem_of_list_In.      
        eexists. split.
        { eapply elem_of_enum. Unshelve. eauto. }
        destruct creates_signal_next_states; eauto.
      - destruct T as (?&T). do 3 right. left.
        destruct sets_signal_next_states; eauto.
      - destruct T as (?&?&?&?&T). do 4 right. left.
        apply elem_of_list_In, in_flat_map. setoid_rewrite <- elem_of_list_In.      
        eexists. split.
        { eapply elem_of_enum. Unshelve. eauto. }
        destruct creates_ep_next_states; eauto.
        eapply e; eauto. 
      - destruct T as (?&?&?&T). do 5 right.
        destruct expects_ep_next_states; eauto.
        eapply e; eauto. 
    Qed.

    (* TODO: move *)
    Instance nsteps_impl {A: Type}:
      Proper ((eq ==> eq ==> impl) ==> eq ==> (eq ==> eq ==> impl)) (@relations.nsteps A).
    Proof using.
      red. intros ?????????????. subst. red in H4.
      generalize dependent y2. induction y0.
      { intros ?. by rewrite !nsteps_0. }
      intros ?. rewrite -!rel_compose_nsteps_next.
      intros (?&STEPS&STEP). apply IHy0 in STEPS.
      eexists. split; eauto. eapply H4; eauto.
    Qed. 

    Lemma progress_step_approx δ:
      list_approx (fun δ' => exists τ, progress_step OP δ τ δ'). 
    Proof using FINlvl FINdeg.
      clear H1 H0 H. 
      red.
      exists (flat_map (fun i => list_approx_repeat (fun δ1 δ2 => exists τ, loc_step _ δ1 τ δ2)
                           loc_step_approx i δ) (seq 0 (LIM_STEPS + 2))).
      intros δ' [τ STEP]. apply elem_of_list_In, in_flat_map.
      setoid_rewrite <- elem_of_list_In.
      red in STEP. destruct STEP as (n & LE & REL). exists (n + 1). split. 
      { apply elem_of_seq. lia. }
      eapply list_approx_repeat_spec.
      destruct REL as (? & STEPS & STEP).
      rewrite Nat.add_1_r. apply rel_compose_nsteps_next.
      eexists. split.
      2: { destruct STEP as (?&?&?). eexists.
           red. left. eauto. }
      eapply nsteps_impl; eauto.
      red. intros ???????. subst. eauto.
    Qed.

    Lemma om_trans_approx δ (L: gset Locale):
      list_approx (fun δ' => dom (ps_obls _ δ') ⊆ L /\ exists τ, om_trans OP δ τ δ'). 
    Proof using FINlvl FINdeg.
      clear H1 H0 H.
      set (approx1 := proj1_sig $ progress_step_approx δ).
      set (approx2 :=
             τ' ← elements $ L;
             δ' ← approx1;
             proj1_sig (forks_locale_next_states δ' τ')).              
      exists (approx1 ++ approx2).
      intros δ' [LOCS [τ STEP]].
      red in STEP. destruct STEP as (δ_ & PSTEP & FSTEP).
      rewrite elem_of_app. inversion FSTEP; subst. 
      2: { left. subst approx1. destruct progress_step_approx. eauto. }
      right. subst approx2. apply elem_of_list_bind.
      setoid_rewrite elem_of_list_bind.
      destruct H as (τ' & ? & FORK). 
      eexists. split; [eexists; split| ].
      - destruct forks_locale_next_states. eauto.
      - subst approx1. destruct progress_step_approx. eauto.
      - apply elem_of_elements. inversion FORK. subst.
        apply LOCS. subst ps'. destruct δ_. simpl in *.
        subst new_obls0. rewrite dom_insert. set_solver.
    Qed.

    (* TODO: rename *)
    Theorem OM_fin_branch_impl
      `{EqDecision (expr Λ)}
      c δ
      (tp': list (language.expr Λ))
      (σ': language.state Λ)
      (oζ: olocale Λ)
      :
      list_approx (fun '(δ', ℓ) =>
           obls_ves_wrapper OP c oζ (tp', σ') δ ℓ δ' ∧
           om_live_tids OP id locale_enabled (tp', σ') δ'). 
    Proof using FINlvl FINdeg.
      destruct (om_trans_approx δ (locales_of_cfg (tp', σ'))) as [nexts NEXTS].
      exists (flat_map (fun τ => map (fun δ' => (δ', (obls_act, Some τ))) nexts) (elements $ locales_of_cfg c)).
      intros [δ' [? oτ]] [STEP TIDS]. apply elem_of_list_In, in_flat_map.
      setoid_rewrite <- elem_of_list_In.
      simpl in STEP. destruct oτ as [τ| ]; [| tauto].
      exists τ. simpl in STEP. destruct STEP as [STEP ->].
      red in STEP. destruct STEP as (STEP & TRANS & -> & CORR). 
      split.
      { apply elem_of_elements.
        destruct c. apply locales_of_cfg_Some.      
        replace l with (l, s).1 by done. by eapply locale_step_from_locale_src. }
      apply elem_of_list_In, in_map_iff. eexists. split; eauto.
      apply elem_of_list_In. apply NEXTS. split.
      { destruct CORR as [TH_OWN ?]. 
        red in TIDS.
        by rewrite TH_OWN. }
      simpl in TRANS. eauto.
    Qed. 
    
  End FinParams.

End FiniteBranching.
