From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic.
From trillium.fairness.lawyer Require Import obligations_model obls_utils.
From trillium.fairness Require Import locales_helpers. 


Close Scope Z. 

    From iris.proofmode Require Import coq_tactics.
    Lemma tac_wp_bind `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} 
      K Δ s E Φ e f :
      f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
      envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
      envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
    Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

    Ltac wp_bind_core K :=
      lazymatch eval hnf in K with
      | [] => idtac
      | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.
    
    Tactic Notation "wp_bind" open_constr(efoc) :=
      iStartProof;
      lazymatch goal with
      | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
          first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
                | fail 1 "wp_bind: cannot find" efoc "in" e ]
      | _ => fail "wp_bind: not a 'wp'"
      end.


Section ProgramLogic.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  
  Context `(OP: ObligationsParams Degree Level (locale heap_lang) LIM_STEPS).
  Let OM := ObligationsModel OP.
  
  (* TODO: figure out the proper way *)
  (* Context `{!ObligationsGS OP Σ}.  *)
  (* Context `{EM: ExecutionModel heap_lang OM}. *)
  Let EM := ObligationsEM OP. 

  Context `{hGS: @heapGS Σ _ EM}.

  Let oGS : ObligationsGS OP Σ := heap_fairnessGS (heapGS := hGS).

  Section MU.
    
    (* Definition extr_last_nofork (extr: execution_trace heap_lang) := *)
    (*   match extr with *)
    (*   | {tr[ _ ]} => False *)
    (*   | extr' :tr[oζ]: c' =>  *)
    (*       locales_of_cfg OP (trace_last extr') = locales_of_cfg OP c' *)
    (*   end. *)

    Definition gset_pick `{Countable K} (g: gset K) :=
      let l := elements g in
      match l with 
      | [] => None
      | e :: _ => Some e
      end. 

    Let extr_last_fork (extr: execution_trace heap_lang): option (locale heap_lang) :=
      match extr with
      | {tr[ _ ]} => None
      | extr' :tr[oζ]: c' =>
          let diff := locales_of_cfg OP c' ∖ locales_of_cfg OP (trace_last extr') in
          gset_pick diff
      end. 

    Definition HL_OM_trace_interp' (extr: execution_trace heap_lang)
      (omtr: auxiliary_trace OM) (τ: locale heap_lang) oτ': iProp Σ :=
      match extr with
      | {tr[ _ ]} => False
      | extr' :tr[oζ]: c' =>
          let c := trace_last extr' in
          let δ := trace_last omtr in
          gen_heap_interp c'.2.(heap) ∗
          (* TODO: next 3 lines are exactly obls_si; similar in next def *)
          obls_msi OP δ (H2 := oGS) ∗
          ⌜ threads_own_obls OP c δ ⌝ ∗
          ⌜ dom_phases_obls OP δ ⌝ ∗
          ⌜ oζ = Some τ ⌝ ∗
          ⌜ locale_step c (Some τ) c' ⌝ ∗
          (* ⌜ (if f then extr_last_fork else extr_last_nofork) (extr' :tr[oζ]: c') ⌝ *)
          (* ⌜ (if f then is_Some else eq None) (extr_last_fork $ extr' :tr[oζ]: c') ⌝ *)
          ⌜ extr_last_fork $ extr' :tr[oζ]: c' = oτ' ⌝
    end.

    Definition HL_OM_trace_interp'_step (extr: execution_trace heap_lang)
      (omtr: auxiliary_trace OM) (τ: locale heap_lang) (k: nat) (oτ': option (locale heap_lang)): iProp Σ :=
      match extr with
      | {tr[ _ ]} => False
      | extr' :tr[oζ]: c' =>
          let c := trace_last extr' in
          let δ := trace_last omtr in
          ∃ δ__k,
          gen_heap_interp c'.2.(heap) ∗
          obls_msi OP δ__k (H2 := oGS) ∗
          ⌜ nsteps (fun p1 p2 => loc_step OP p1 τ p2) k δ δ__k ⌝ ∗
          ⌜ threads_own_obls OP c δ ⌝ ∗
          ⌜ dom_phases_obls OP δ ⌝ ∗
          ⌜ obls_eq OP δ__k (dom $ ps_obls OP δ) ⌝ ∗
          ⌜ oζ = Some τ ⌝ ∗
          ⌜ locale_step c (Some τ) c' ⌝ ∗
          ⌜ extr_last_fork $ extr' :tr[oζ]: c' = oτ' ⌝
    end.

    Let iG := @heapG_irisG _ _ _ hGS. 
    
    Definition MU_impl (f: option (locale heap_lang)) E ζ (P : iProp Σ) : iProp Σ := ∀ extr atr, 
      HL_OM_trace_interp' extr atr ζ f ={E}=∗
      ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := iG) ∗ P.


    Definition MU := MU_impl None.
    (* Definition MU__f τ' := MU_impl (Some τ').  *)
    Definition MU__f E ζ ζ' P := MU_impl (Some ζ') E ζ P. 


    (* Definition MU E ζ (P : iProp Σ) := ∀ extr atr, *)
    (*   HL_OM_trace_interp' extr atr ζ false ={E}=∗ *)
    (*   ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := iG) ∗ P. *)

    (* Definition MU E ζ ζ' (P : iProp Σ) := ∀ extr atr, *)
    (*   (HL_OM_trace_interp' extr atr ζ false ={E}=∗ *)
    (*    ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := iG) ∗ P) ∗ *)
    (*   ⌜ locales_of_cfg (tra ⌝ *)


  (*   Lemma old_HL_OM_si e ζ b *)
  (* (extr : execution_trace heap_lang) *)
  (* (atr : auxiliary_trace (ObligationsModel OP)) *)
  (* (K : ectx heap_lang) *)
  (* (tp1 tp2 : list (language.expr heap_lang)) *)
  (* (σ1 : language.state heap_lang) *)
  (* (Hζ : language.locale_of tp1 (ectx_fill K e) = ζ) *)
  (* (Hextr : trace_last extr = (tp1 ++ ectx_fill K e :: tp2, σ1)) *)
  (* (e2 : language.expr heap_lang) *)
  (* (σ2 : language.state heap_lang) *)
  (* (Hstep : prim_step e σ1 e2 σ2 []) *)
  (* : *)
  (* obls_si OP (tp1 ++ fill K e :: tp2, σ1) (trace_last atr) (H2 := oGS) -∗ *)
  (* gen_heap_interp (heap σ2) -∗ *)
  (* HL_OM_trace_interp' (extr :tr[ Some ζ ]: (tp1 ++ ectx_fill K e2 :: tp2, σ2)) atr ζ b. *)
  (*   Proof using.  *)
  (*     iIntros "MSI Hσ". *)
  (*     rewrite /HL_OM_trace_interp'. simpl.  *)
  (*     rewrite /obls_si. iDestruct "MSI" as "(M & %TS & %DPO)".  *)
  (*     remember (trace_last extr) as xx. destruct xx as [tp h]. *)
  (*     inversion Hextr as [[TP HH]]. *)
  (*     rewrite -TP in TS. *)
  (*     iApply bi.sep_assoc. iSplitL. *)
  (*     { iFrame. } *)
  (*     iPureIntro. repeat rewrite and_assoc. split. *)
  (*     - repeat rewrite -and_assoc. repeat split; eauto.   *)
  (*       { replace tp with (tp, h).1 in TS by done. *)
  (*         rewrite Heqxx in TS. apply TS. } *)
  (*       simpl in Hζ.  *)
  (*       rewrite -Hζ. simpl. *)
  (*       eapply locale_step_atomic. *)
  (*       3: { eapply @fill_step. apply Hstep. }  *)
  (*       { rewrite -Heqxx Hextr. simpl. reflexivity. } *)
  (*       by rewrite app_nil_r.  *)
  (*     - simpl. rewrite -Heqxx TP HH. *)
  (*       rewrite /locales_of_cfg. simpl. f_equal. *)
  (*       apply locales_of_list_equiv. *)
  (*       apply locales_equiv_from_middle. done. *)
  (*   Qed.  *)

    (* TODO: move *)
    Lemma gset_pick_None `{Countable K} (g: gset K):
      gset_pick g = None <-> g = ∅.
    Proof.
      rewrite /gset_pick. destruct (elements g) eqn:E.
      - apply elements_empty_inv in E. apply leibniz_equiv_iff in E. done.
      - split; [done| ]. intros ->. simpl in E. set_solver.
    Qed. 
    
    (* TODO: move *)
    Lemma gset_pick_is_Some `{Countable K} (g: gset K):
      is_Some (gset_pick g) <-> g ≠ ∅.
    Proof.
      rewrite -not_eq_None_Some. apply not_iff_compat, gset_pick_None. 
    Qed. 

    (* TODO: move *)
    Lemma gset_pick_Some `{Countable K} (g: gset K) k:
      gset_pick g = Some k -> k ∈ g. 
    Proof.
      rewrite /gset_pick. destruct elements eqn:E; [done| ].
      intros [=->]. apply elem_of_elements. rewrite E. constructor. 
    Qed. 

    Lemma sswp_MU_wp_fupd s E E' ζ e Φ
      (NVAL: language.to_val e = None)
      :
      let sswp_post := λ e', (MU E' ζ (|={E',E}=> WP e' @ s; ζ; E {{ Φ }}))%I in
      (|={E,E'}=> sswp s E' e sswp_post)%I -∗
        WP e @ s; ζ; E {{ Φ }}.
    Proof.
      simpl. rewrite wp_unfold /wp_pre.
      iIntros "Hsswp". rewrite NVAL. 
      iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
      iMod "Hsswp" as "foo".
      rewrite /sswp. rewrite NVAL.
      iSimpl in "Hσ". iDestruct "Hσ" as "(%EV & HEAP & MSI)".
      iSpecialize ("foo" with "HEAP").
      iMod "foo" as (Hs) "Hsswp".
      red in Hextr. rewrite Hextr. 
      iModIntro. iSplit.
      { iPureIntro. by rewrite Hextr in Hs. }
      iIntros (e2 σ2 efs Hstep).
      iDestruct ("Hsswp" with "[//]") as "Hsswp".
      iApply (step_fupdN_le 1); [| done| ].
      { pose proof (trace_length_at_least extr). lia. }
      simpl.
      iApply (step_fupd_wand with "Hsswp").
      iIntros ">(Hσ & HMU & ->)".
      rewrite /MU. iSpecialize ("HMU" $! (extr :tr[Some ζ]: _) atr with "[MSI Hσ]").
      { clear NVAL Hvalid Hs EV.        
        
        rewrite /HL_OM_trace_interp'. simpl. 
        rewrite /obls_si. iDestruct "MSI" as "(M & %TS & %DPO)". 
        (* iPoseProof (MSI_tids_smaller with "MSI") as "%TS". *)
        remember (trace_last extr) as xx. destruct xx as [tp h].
        inversion Hextr as [[TP HH]].
        rewrite -TP in TS.
        iApply bi.sep_assoc. iSplitL.
        2: { iPureIntro. repeat rewrite and_assoc. split.
             - repeat rewrite -and_assoc. repeat split; eauto.  
               { replace tp with (tp, h).1 in TS by done.
                 rewrite Heqxx in TS. apply TS. }
               simpl in Hζ. 
               rewrite -Hζ. simpl.
               (* rewrite locale_fill'.  *)
               eapply locale_step_atomic.
               3: { eapply @fill_step. apply Hstep. } 
               { rewrite -Heqxx Hextr. simpl. reflexivity. }
               reflexivity.
             - simpl. rewrite (proj2 (gset_pick_None _)); [done| ].  
               apply subseteq_empty_difference_L.
               eapply subseteq_proper; [reflexivity| | by apply PreOrder_Reflexive]. 
               rewrite -Heqxx TP HH.
               rewrite app_nil_r.
               apply leibniz_equiv_iff. 
               rewrite /locales_of_cfg. simpl. f_equal.
               apply locales_of_list_equiv.
               apply locales_equiv_from_middle. done. } 
        simpl. iFrame. }
      iMod ("HMU") as (??) "[Hσ Hwp]". iMod "Hwp". iModIntro.
      iExists _, _. rewrite right_id_L. by iFrame.
    Qed.

    Lemma MU_wand E ζ (P Q : iProp Σ) :
      (P -∗ Q) -∗ MU E ζ P -∗ MU E ζ Q.
    Proof.
      rewrite /MU. iIntros "HPQ HMU".
      iIntros (extr atr) "Hσ".
      iMod ("HMU" with "Hσ") as (??) "[Hσ HP]". iModIntro.
      iExists _, _. iFrame. by iApply "HPQ".
    Qed.

    (* TODO: refactor *)
    Lemma MU__f_wand E ζ ζ' (P Q : iProp Σ) :
      (P -∗ Q) -∗ MU__f E ζ ζ' P -∗ MU__f E ζ ζ' Q.
    Proof.
      rewrite /MU__f /MU_impl. iIntros "HPQ HMU".
      iIntros (extr atr) "Hσ".
      iMod ("HMU" with "Hσ") as (??) "[Hσ HP]". iModIntro.
      iExists _, _. iFrame. by iApply "HPQ".
    Qed.
    
    Lemma sswp_MU_wp s E ζ e (Φ : val → iProp Σ)
      (NVAL: language.to_val e = None):
      sswp s E e (λ e', MU E ζ (WP e' @ s; ζ;  E {{ Φ }})) (hGS := hGS) -∗
        WP e @ s; ζ; E {{ Φ }}.
    Proof.
      iIntros "Hsswp". iApply sswp_MU_wp_fupd; auto. iModIntro.
      iApply (sswp_wand with "[] Hsswp").
      iIntros (?) "HMU". iApply (MU_wand with "[] HMU"). by iIntros "$ !>".
    Qed.
    
    Lemma locales_of_cfg_simpl l σ:
      locales_of_cfg OP (l, σ) = set_seq 0 (length l).
    Proof. 
      rewrite /locales_of_cfg. f_equal. simpl.
      rewrite !locales_of_list_from_indexes. simpl.
      rewrite !imap_seq_0. rewrite !list_fmap_id.
      apply list_to_set_seq.
    Qed. 

    Lemma length_upd_middle {A: Type} (x y: A) l1 l2:
      length (l1 ++ x :: l2) = length (l1 ++ y :: l2).
    Proof.  intros. rewrite !app_length. simpl. lia. Qed.

    Lemma gset_pick_singleton `{Countable K} (k: K):
      gset_pick {[ k ]} = Some k.
    Proof.
      rewrite /gset_pick. rewrite elements_singleton. done.
    Qed. 

    Lemma sswp_MUf_wp s E τ (Φ: val -> iProp Σ) e
      :
      (∀ τ', MU__f E τ τ' ((WP e @ s; τ'; ⊤ {{ fun r => fork_post (irisG := iG) τ' r }}) ∗ Φ #())) -∗
      WP (Fork e) @ s; τ; E {{ Φ }}.
    Proof using.
      iIntros "MU".
      iApply wp_lift_atomic_head_step; [done|].
      iIntros (extr mtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & HEAP & MSI)".
      rewrite /MU__f /MU_impl.

      iSplitR.
      { iPureIntro. red. do 3 eexists.
        simpl. apply ForkS. }

      iModIntro. iNext.
      iIntros (e2 σ2 efs STEP).
      have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.

      iSpecialize ("MU" $! _ (extr :tr[Some τ]: (_, _)) mtr with "[HEAP MSI]").
      { rewrite /HL_OM_trace_interp'. simpl.
        rewrite /obls_si. iDestruct "MSI" as "(M & %TS & %DPO)".
        remember (trace_last extr) as xx. destruct xx as [tp h].
        inversion Hexend as [[TP HH]].
        rewrite TP. simpl. 
        iApply bi.sep_assoc. iSplitL.
        { iFrame. }
        iPureIntro. repeat split; try done. 
        - by rewrite -TP.
        - erewrite <- language.locale_fill with (K := K) in Hloc.  
          rewrite -Hloc. simpl.
          eapply locale_step_atomic.
          { reflexivity. }
          2: { econstructor; eauto. }
          rewrite Hloc. f_equal.
          by inversion STEP.
        - rewrite !locales_of_cfg_simpl.
          rewrite (length_upd_middle (ectx_language.fill K e2) #()). 
          rewrite (length_upd_middle (fill K (Fork e)) #()). 
          rewrite app_comm_cons. rewrite app_assoc.
          rewrite app_length. rewrite set_seq_add_L. simpl.
          rewrite difference_union_distr_l_L. rewrite subseteq_empty_difference_L; [| done].
          rewrite union_empty_l_L.

          inversion STEP. subst. simpl. rewrite union_empty_r_L.
          rewrite difference_disjoint_L.
          2: { apply disjoint_singleton_l.
               intros ?%elem_of_set_seq. lia. }
          rewrite gset_pick_singleton. reflexivity. }
      
      iMod ("MU") as (??) "(Hσ & WP' & POST)".
      iFrame.
      inversion STEP. subst. iModIntro. iExists _, _. iFrame.
      simpl. rewrite !app_nil_r. iSplitL; [| done].
      rewrite /locale_of. rewrite (length_upd_middle (fill K (Fork e)) #()). 
      iApply "WP'". 
    Qed. 
     
  End MU.

  Section BMU.

    Definition BMU E ζ b (P : iProp Σ) : iProp Σ :=
    ∀ extr atr n f,
      (* ⌜ n <= LIM_STEPS - b ⌝ ∗ *)
      HL_OM_trace_interp'_step extr atr ζ n f ={E}=∗
      ∃ n', HL_OM_trace_interp'_step extr atr ζ n' f ∗ 
            (* ⌜ n <= n' <= LIM_STEPS ⌝ ∗  *)
            ⌜ n' - n <= b ⌝ ∗
            P.

    (* (* TODO: clarify how to derive this fact *) *)
    (* Lemma WIP_th_own_ex_phase c τ c' δ *)
    (*   (STEP: locale_step c (Some τ) c') *)
    (*   (OBLS: threads_own_obls OP c δ): *)
    (*   exists π, ps_phases OP δ !! τ = Some π. *)
    (* Proof. *)
      
    (* Admitted. *)

    (* (* TODO: ghost steps should preserve it *) *)
    (* Lemma WIP_th_own_gsteps_ex_phase c τ c' δ δ' n *)
    (*   (STEP: locale_step c (Some τ) c') *)
    (*   (OBLS: threads_own_obls OP c δ) *)
    (*   (GSTEPS: relations.nsteps (fun p1 p2 => ghost_step OP p1 τ p2) n δ δ'): *)
    (*   exists π, ps_phases OP δ' !! τ = Some π. *)
    (* Proof. Admitted. *)

    (* Lemma WIP_all_phases_le π1 π2: *)
    (*   phase_le π1 π2. *)
    (* Proof. done. Qed. *)

    (* TODO: move *)
    Lemma locale_step_sub c1 c2 τ
      (STEP: locale_step c1 (Some τ) c2):
      locales_of_cfg OP c1 ⊆ locales_of_cfg OP c2. 
    Proof.
      inversion STEP. subst.
      
      rewrite !locales_of_cfg_simpl. 
      rewrite app_comm_cons. rewrite app_assoc. rewrite (app_length _ efs). 
      rewrite -!list_to_set_seq. rewrite seq_app.
      rewrite list_to_set_app.
      rewrite (length_upd_middle e1 e2). set_solver.
    Qed. 

    (* TODO: move *)
    Lemma locale_step_fresh_exact c1 c2 τ τ'
      (STEP: locale_step c1 (Some τ) c2)
      (FRESH: τ' ∈ locales_of_cfg OP c2 ∖ locales_of_cfg OP c1):
      locales_of_cfg OP c2 = locales_of_cfg OP c1 ∪ {[ τ' ]} /\ τ' ∉ locales_of_cfg OP c1.
    Proof.
      inversion STEP. subst.
      revert FRESH.
      
      rewrite !locales_of_cfg_simpl. 
      rewrite app_comm_cons. rewrite app_assoc. rewrite app_length.
      rewrite -!list_to_set_seq. rewrite seq_app. simpl. 
      rewrite list_to_set_app_L. rewrite !list_to_set_seq.

      rewrite (length_upd_middle e2 e1). remember (length (t1 ++ e1 :: t2)) as N.
      rewrite -HeqN. remember (set_seq 0 N) as D. 
      
      rewrite difference_union_distr_l_L. rewrite subseteq_empty_difference; [| done].
      rewrite union_empty_l. intros [DOM2 NDOM1]%elem_of_difference.
      split; [| done].
      f_equal.

      assert (¬ (efs = [])) as FORK.
      { intros NOFORK. inversion H6. subst. inversion H4; subst; done. }
      inversion H6. subst. inversion H4; subst; try done.
      simpl in DOM2. rewrite union_empty_r in DOM2. apply elem_of_singleton in DOM2.
      simpl. set_solver.
    Qed.            

    Lemma finish_obls_steps extr omtr τ n π' deg
      (BOUND: n <= LIM_STEPS)
      (LE: exists π, ps_phases OP (trace_last omtr) !! τ = Some π /\ phase_le π' π)
      :
      ⊢ HL_OM_trace_interp'_step extr omtr τ n None -∗ (cp OP π' deg (H2 := oGS))==∗
        ∃ δ', state_interp extr (trace_extend omtr τ δ') (irisG := @heapG_irisG _ _ _ hGS).
    Proof.
      iIntros "TI'' cp".
      rewrite /HL_OM_trace_interp'_step.

      destruct extr; [done| ].
      iDestruct "TI''" as (δ__k) "(HEAP&MSI&%TRANSS&%TH_OWN&%DPO&%OBLS&->&%STEP&%NOFORK)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP.
      destruct LE as (π__max & PH & LE0).
      
      iMod (burn_cp_upd_impl with "[$] [$]") as "X".
      { eexists. split; eauto.
        rewrite -PH.
        (* TODO: use stricter version of progress_step_dpo_pres for nsteps *)
        admit. }
      iDestruct "X" as "(%δ' & MSI & %BURNS)". 
      iModIntro. iExists _. simpl. iFrame.
      
      assert (threads_own_obls OP a δ') as TH_OWN'.
      { eapply locale_nofork_step_obls_pres; eauto.
        2: { apply gset_pick_None in NOFORK.
             apply set_eq_subseteq. split.
             - apply empty_difference_subseteq_L in NOFORK. done.
             - eapply locale_step_sub; eauto. }
        red. eexists. split; [eauto| ].
        eexists. split; eauto. }
      
      iPureIntro. do 2 split; auto.
      - red. repeat split; auto.
        simpl. red. eexists. split; eauto.
        + eexists. split; eauto. eexists. split; eauto.
        + by right. 
      - eapply progress_step_dpo_pres; eauto.
        do 2 (eexists; split; eauto). 
    Admitted. 

    Lemma finish_obls_steps_fork extr omtr τ τ' n π' π deg R0 R' 
      (BOUND: n <= LIM_STEPS)
      (* can use th_phase_ge here, since it'll only be used after BMU *)
      (* TODO: unify these proofs? *)
      (* (LE: exists π, ps_phases OP (trace_last omtr) !! τ = Some π /\ phase_le π' π) *)
      (LE: phase_le π' π)
      :
      ⊢ HL_OM_trace_interp'_step extr omtr τ n (Some τ') -∗ (cp OP π' deg (H2 := oGS)) -∗ obls OP τ R0 (H2 := oGS) -∗ th_phase_ge OP τ π (H2 := oGS) ==∗
        ∃ δ' π1 π2, state_interp extr (trace_extend omtr τ δ') (irisG := @heapG_irisG _ _ _ hGS) ∗ obls OP τ (R0 ∖ R') (H2 := oGS) ∗ th_phase_ge OP τ π1 (H2 := oGS) ∗ obls OP τ' R' (H2 := oGS) ∗ th_phase_ge OP τ' π2 (H2 := oGS) .
    Proof.
      iIntros "TI'' cp OB PH".
      rewrite /HL_OM_trace_interp'_step.
      destruct extr; [done| ].
      
      iDestruct "TI''" as (δ__k) "(HEAP&MSI&%TRANSS&%TH_OWN&%DPO&%OBLS&->&%STEP&%FORK)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP.
      
      apply gset_pick_Some in FORK. 
      eapply locale_step_fresh_exact in FORK; eauto.  
      destruct FORK as (LOCS' & FRESH).

      (* destruct LE as (π__max & PH & LE0). *)
      iDestruct (th_phase_msi_ge with "[$] [$]") as %(π__max & PH & LE0).
      
      iMod (burn_cp_upd_impl with "[$] [$]") as "X".
      { eexists. split; eauto.
        red. etrans; eauto. }
      iDestruct "X" as "(%δ' & MSI & %BURNS)".

      assert (obls_eq OP δ' (dom (ps_obls OP (trace_last omtr)))) as OBLS'.
      { eapply (progress_step_obls_pres _ (trace_last omtr)); eauto.
        2: done. 
        eexists. do 2 (esplit; eauto). }
      assert (dom_phases_obls OP δ') as DPO'.
      { eapply progress_step_dpo_pres; eauto.
        eexists. do 2 (esplit; eauto). }
       
      iMod (fork_locale_upd_impl with "[$] [$] [$]") as "Y"; eauto. 
      { rewrite DPO'. rewrite OBLS'.
        rewrite -TH_OWN. apply FRESH. }
      iDestruct "Y" as "(%δ'' & %π1 & %π2 & MSI & PH1 & PH2 & OB1 & OB2 & %FORKS)".
      
      iModIntro. do 3 iExists _. simpl. iFrame.

      (* TODO: make a lemma? *)
      assert (dom (ps_obls OP δ'') = dom (ps_obls OP δ') ∪ {[ τ' ]}) as OBLS''.
      { inversion FORKS. subst. subst ps'.
        destruct δ'. simpl. subst new_obls0. simpl in *.
        rewrite !dom_insert_L.
        enough (τ ∈ dom ps_obls).
        { clear -H2. set_solver. }
        rewrite -DPO'. simpl. eapply elem_of_dom; eauto. }
      (* TODO: make a lemma? *)
      assert (dom (ps_phases OP δ'') = dom (ps_phases OP δ') ∪ {[ τ' ]}) as PHASES''.
      { inversion FORKS. subst. subst ps'.
        destruct δ'. simpl. subst new_phases0. simpl in *.
        rewrite !dom_insert_L.
        enough (τ ∈ dom ps_phases).
        { clear -H2. set_solver. }
        eapply elem_of_dom; eauto. }

      iPureIntro. do 2 split; auto.
      - red. repeat split; auto.
        simpl. red. eexists. split; eauto.
        + eexists. split; eauto. eexists. split; eauto.
        + left. eauto. 
      - red. rewrite LOCS'.
        rewrite OBLS''. f_equal. set_solver.
      - red. rewrite OBLS'' PHASES''. f_equal.
        done. 
      Unshelve. done. 
    Qed. 
      
    Lemma BMU_intro E ζ b (P : iProp Σ):
      ⊢ P -∗ BMU E ζ b P.
    Proof. 
      rewrite /BMU. iIntros "**". iModIntro.
      iExists _. iFrame. iPureIntro. lia.
    Qed. 

    Lemma BMU_frame E ζ b (P Q : iProp Σ):
      ⊢ P -∗ BMU E ζ b Q -∗ BMU E ζ b (P ∗ Q).
    Proof. 
      rewrite /BMU. iIntros "P BMU **".
      iMod ("BMU" with "[$]") as "(%&?&?&?)". iModIntro. 
      iExists _. iFrame.
    Qed. 

    Lemma BMU_wand E ζ b (P Q : iProp Σ):
      ⊢ (P -∗ Q) -∗ BMU E ζ b P -∗ BMU E ζ b Q.
    Proof. 
      rewrite /BMU. iIntros "PQ BMU **".
      iMod ("BMU" with "[$]") as "(%&?&?&?)". iModIntro. 
      iExists _. iFrame. by iApply "PQ". 
    Qed. 

    Lemma BMU_MU E ζ b (P : iProp Σ) π
      (BOUND: b <= LIM_STEPS)
      :
      ⊢ (th_phase_ge OP ζ π (H2 := oGS) -∗ BMU E ζ b ((P) ∗ ∃ ph deg, cp OP ph deg (H2 := oGS) ∗ ⌜ phase_le ph π ⌝)) -∗
        th_phase_ge OP ζ π (H2 := oGS) -∗
        MU E ζ P.
    Proof.
      rewrite /MU /BMU. iIntros "BMU PH" (etr otr) "TI'".      
      iDestruct (th_phase_msi_ge with "[TI'] [$]") as %(π__max & PH & LE0).
      { rewrite /HL_OM_trace_interp'. destruct etr; [done| ].
        iDestruct "TI'" as "(?&?&?&?)". iFrame. }
      iSpecialize ("BMU" with "[$]").
      iSpecialize ("BMU" $! etr otr 0 None with "[TI']").
      { rewrite /HL_OM_trace_interp' /HL_OM_trace_interp'_step.
        destruct etr; [done| ].
        iDestruct "TI'" as "(HEAP&MSI&%OBLS&%DPO&->&%STEP&%NOFORK)".
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        by constructor. }
      iMod "BMU" as (n') "(TI'' & %BOUND' & P & (%ph & %deg & CP & %PH'))".
      iMod (finish_obls_steps with "[$] [$]") as (?) "SI".
      { lia. }
      { eexists. split; [apply PH| ].
        red. etrans; eauto. }
      iFrame.
      iModIntro. eauto.
    Qed.

    (* fork_locale_upd_impl *)
    Lemma BMU_MU__f E ζ ζ' b (P : iProp Σ) π R0 R'
      (BOUND: b <= LIM_STEPS)
      :
      ⊢ (th_phase_ge OP ζ π (H2 := oGS) -∗ BMU E ζ b
           (P ∗ (∃ ph deg, cp OP ph deg (H2 := oGS) ∗ ⌜ phase_le ph π ⌝) ∗
           th_phase_ge OP ζ π (H2 := oGS) ∗
           obls OP ζ R0 (H2 := oGS))) -∗
        th_phase_ge OP ζ π (H2 := oGS) -∗
        MU__f E ζ ζ' (P ∗ ∃ π1 π2, 
                     th_phase_ge OP ζ π1 (H2 := oGS) ∗ obls OP ζ (R0 ∖ R') (H2 := oGS)∗
                     th_phase_ge OP ζ' π2 (H2 := oGS) ∗ obls OP ζ' R' (H2 := oGS)).
    Proof.
      rewrite /MU__f /MU_impl /BMU. iIntros "BMU PH" (etr otr) "TI'".      
      iDestruct (th_phase_msi_ge with "[TI'] [$]") as %(π__max & PH & LE0).
      { rewrite /HL_OM_trace_interp'. destruct etr; [done| ].
        iDestruct "TI'" as "(?&?&?&?)". iFrame. }
      iSpecialize ("BMU" with "[$]").
      iSpecialize ("BMU" $! etr otr 0 (Some ζ') with "[TI']").
      { rewrite /HL_OM_trace_interp' /HL_OM_trace_interp'_step.
        destruct etr; [done| ].
        iDestruct "TI'" as "(HEAP&MSI&%OBLS&%DPO&->&%STEP&%NOFORK)".
        iExists _. iFrame. iPureIntro.
        repeat split; try done.
        by constructor. }
      iMod "BMU" as (n') "(TI'' & %BOUND' & P & (%ph & %deg & CP & %PH') & PH & OB )".
      iMod (finish_obls_steps_fork with "[$] [$] [$] [$]") as (?) "SI".
      { lia. }
      { done. }
      iDestruct "SI" as (π1 π2) "(SI & OB1 & PH1 & OB2 & PH2)".
      iModIntro. iExists _, _. iFrame "P SI". iFrame.
      do 2 iExists _. iFrame.  
    Qed.

    Lemma OU_BMU E ζ P b:
       ⊢ OU OP ζ (BMU E ζ b P) (H2 := oGS) -∗ BMU E ζ (S b) P.
    Proof.
      iIntros "OU". rewrite {2}/BMU /HL_OM_trace_interp'_step.
      iIntros (etr atr n f) "TI'". destruct etr; [done| ].
      iDestruct "TI'" as "(%δ & HEAP & MSI & %TRANS1 & %TH_OWN & %DPO & %OBLS_EQ & -> & %STEP & %FF)".
      rewrite /OU. iMod ("OU" with "[$]") as "(%δ' & MSI & %TRANS2 & CONT)".
      iSpecialize ("CONT" $! (etr :tr[ _ ]: _) with "[HEAP MSI]").
      { rewrite /HL_OM_trace_interp'_step. iExists _.  iFrame.
        iPureIntro. repeat split; eauto.
        - eapply rel_compose_nsteps_next. eexists. split; eauto.
        - eapply loc_step_obls_pres; eauto. }
      iMod "CONT" as "(%n' & TI' & %BOUND' & P)". iModIntro.
      rewrite FF. 
      iExists _. iFrame. iSplitL.
      - simpl. iDestruct "TI'" as (xx) "(?&?&?&?&?&?&?)".
        iExists _. iFrame. iPureIntro. done.
      - iPureIntro. lia. 
    Qed.

    (* an example usage of OU *)
    Lemma BMU_step_create_signal E ζ P b l R:
       ⊢ (∀ sid, sgn OP sid l (Some false) (H2 := oGS) -∗ obls OP ζ (R ∪ {[ sid ]}) (H2 := oGS) -∗ BMU E ζ b P) -∗ obls OP ζ R (H2 := oGS) -∗ BMU E ζ (S b) P.
    Proof.
      iIntros "CONT OB".
      iApply OU_BMU. iApply (OU_wand with "[CONT]").
      { setoid_rewrite bi.wand_curry. rewrite -bi.exist_wand_forall.
        iFrame. }
      iPoseProof (OU_create_sig with "OB") as "OU". done.
    Qed. 

  End BMU.

  Section TestProg.
    
    Let test_prog: expr :=
          let: "x" := ref (#1 + #1) in
          Fork(!"x")
    .

    Hypothesis (LIM_STEPS_LB: 5 <= LIM_STEPS).

    Lemma obls_proper ζ R1 R2 (EQUIV: R1 ≡ R2):
      ⊢ obls OP ζ R1 (H2 := oGS) ∗-∗ obls OP ζ R2 (H2 := oGS).
    Proof. set_solver. Qed. 


    Lemma test_spec (τ: locale heap_lang) (π: Phase) (d d': Degree) (l: Level)
      (DEG: opar_deg_lt d' d)
      :
      {{{ cp_mul OP π d 10 (H2 := oGS) ∗ th_phase_ge OP τ π (H2 := oGS) ∗ obls OP τ ∅ (H2 := oGS) ∗ exc_lb OP 5 (H2 := oGS) }}}
        test_prog @ τ
      {{{ x, RET #x; obls OP τ ∅ (H2 := oGS) }}}.
    Proof.
      iIntros (Φ). iIntros "(CPS & PH & OBLS & #EB) POST".
      rewrite /test_prog. 

      wp_bind (_ + _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step; [done| ].
      rewrite /Z.add. simpl. 
      iNext. iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      iApply OU_BMU.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iDestruct (exchange_cp_upd with "[$] [$] [$]") as "OU"; eauto.
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "[CPS' PH]". 
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS'") as "[CPS' CP']". 
      iSplitR "CP'".
      2: { do 2 iExists _. iFrame. iPureIntro.
           red. reflexivity. }

      iApply wp_value.

      wp_bind (ref _)%E. 
      iApply sswp_MU_wp; [done| ].
      iApply wp_alloc. iIntros "!> %x L ?".
      iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      iApply OU_BMU.
      iDestruct (OU_create_sig _ _ _ l with "[$]") as "OU".
      Unshelve. 2: by apply _. 
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "(%sid & SIG & OBLS)".
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iSplitR "CP". 
      2: { do 2 iExists _. iFrame. iPureIntro.
           red. reflexivity. }

      iApply wp_value.
      (* Set Printing All. *)
      (* Unset Printing Notations. *)

      wp_bind (Rec _ _ _). 
      iApply sswp_MU_wp; [done| ].      
      iApply sswp_pure_step; [done| ].
      iNext. iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      (* iApply OU_BMU. *)
      (* iDestruct (OU_set_sig with "OBLS SIG") as "OU"; [set_solver| ]. *)
      (* iApply (OU_wand with "[-OU]"); [| done]. *)
      (* iIntros "(SIG & OBLS)". *)
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP".
      2: { do 2 iExists _. iFrame. iPureIntro.
           red. reflexivity. }
      rewrite union_empty_l_L. 

      iApply wp_value. 

      iApply sswp_MU_wp; [done| ].      
      iApply sswp_pure_step; [done| ].
      iApply (BMU_MU with "[-PH] [$]"); [eauto| ]. iIntros "PH".
      iApply BMU_intro.
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
      iSplitR "CP". 
      2: { do 2 iExists _. iFrame. iPureIntro.
           red. reflexivity. }

      simpl. 

      iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[]").
      2: { iApply (BMU_MU__f with "[-PH]"); [apply LIM_STEPS_LB| ..].
           2: by iFrame.
           iIntros "PH".
           
           iApply OU_BMU.
           iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
           iApply (OU_wand with "[-CP PH]"). 
           2: { iApply (burn_cp_upd with "CP [$]"). }
           iIntros "PH".
           
           iApply BMU_intro. iFrame "PH OBLS".
           iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
           iSplitR "CP".
           2: { do 2 iExists _. iFrame. iPureIntro. eapply phase_le_refl. }

           iAccu. }

      iIntros "[(POST & CPS' & L & MT & SIG & CPS) R']".
      iDestruct "R'" as (π1 π2) "(PH1 & OB1 & PH2 & OB2)".
      
      iSplitR "POST CPS MT OB1 PH1"; cycle 1.  
      - iApply "POST". 
        iApply (obls_proper with "[$]").
        symmetry. apply subseteq_empty_difference. reflexivity.
      - iApply sswp_MU_wp; [done| ].
        iApply (wp_load with "[$]"). iNext. iIntros.
        iApply (BMU_MU with "[-PH2] [$]"); [eauto| ]. iIntros "PH2".
        iApply OU_BMU.
        iDestruct (OU_set_sig with "OB2 SIG") as "OU"; [set_solver| ].
        iApply (OU_wand with "[-OU]"); [| done].
        iIntros "[SIG OB2]". 
        iApply BMU_intro.
        iDestruct (cp_mul_take with "CPS'") as "[CPS' CP]".
        iSplitR "CP".
        2: { do 2 iExists _. iFrame. iPureIntro.
             (* TODO: expose the fact that phases increase after fork *)
             (* red. reflexivity. *)
             admit. 
        }

        iApply wp_value.
        simpl.
        iApply (obls_proper with "[$]"). set_solver.
        Unshelve. all: done. 
    Admitted. 

  End TestProg.
    
End ProgramLogic.
