From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From trillium.fairness Require Import locales_helpers utils. 
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z. 

Lemma tac_wp_bind `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} 
  K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

Global Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Global Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
      first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
            | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.


Section ProgramLogic.
  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.

  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

  Section MU.
    
    Definition extr_last_fork (extr: execution_trace heap_lang): option (locale heap_lang) :=
      match extr with
      | {tr[ _ ]} => None
      | extr' :tr[oζ]: c' =>
          let diff := locales_of_cfg c' ∖ locales_of_cfg (trace_last extr') in
          gset_pick diff
      end. 

    Definition trace_interp_interim (extr: execution_trace heap_lang)
      (mtr: auxiliary_trace M) (τ: locale heap_lang) oτ': iProp Σ :=
      match extr with
      | {tr[ _ ]} => False
      | extr' :tr[oζ]: c' =>
          let c := trace_last extr' in
          let δ := trace_last mtr in
          gen_heap_interp c'.2.(heap) ∗

          (* obls_si OP c δ (ObligationsGS0 := oGS) ∗   *)
          em_msi c δ (em_GS0 := eGS) ∗ 

          ⌜ oζ = Some τ ⌝ ∗
          ⌜ locale_step c (Some τ) c' ⌝ ∗
          ⌜ extr_last_fork $ extr' :tr[oζ]: c' = oτ' ⌝
    end.

    Let iG := @heapG_irisG _ _ _ hGS. 
    
    Definition MU_impl (f: option (locale heap_lang)) E ζ (P : iProp Σ) : iProp Σ := ∀ extr atr, 
      trace_interp_interim extr atr ζ f ={E}=∗
      ∃ δ2 ℓ, state_interp extr (trace_extend atr ℓ δ2) (irisG := iG) ∗ P.

    Definition MU := MU_impl None.
    Definition MU__f E ζ ζ' P := MU_impl (Some ζ') E ζ P.

    (* For each proofmode typeclass, there are two instances (for MU with and without fork)
       Both are proved with a single lemma *)

    Lemma ElimModal_bupd_MU_impl p f E ζ P Q:
      ElimModal True p false
        (|==> P) P
        (MU_impl f E ζ Q) (MU_impl f E ζ Q).
    Proof using.
      red. iIntros "_ [P IMPL]".
      rewrite bi.intuitionistically_if_elim.
      iMod "P". by iApply "IMPL".
    Qed.

    Global Instance ElimModal_bupd_MU p E ζ P Q:
      ElimModal True p false
        (|==> P) P
        (MU E ζ Q) (MU E ζ Q).
    Proof using. apply ElimModal_bupd_MU_impl. Qed. 

    Global Instance ElimModal_bupd_MU__f p f E ζ P Q:
      ElimModal True p false
        (|==> P) P
        (MU__f E f ζ Q) (MU__f E f ζ Q).
    Proof using. apply ElimModal_bupd_MU_impl. Qed.

    Lemma ElimModal_fupd_MU_impl p E' E ζ f P Q:
      ElimModal (E' ⊆ E) p false
        (|={E'}=> P) P
        (MU_impl f E ζ Q) (MU_impl f E ζ Q).
    Proof using.
      red. simpl. iIntros "%SUB [P IMPL]".
      rewrite bi.intuitionistically_if_elim.
      rewrite /MU_impl.
      iIntros (??) "TI'".
      iMod (fupd_mask_subseteq E') as "CLOS"; [done| ]. iMod "P".
      iMod "CLOS". iMod ("IMPL" with "[$] [$]").
      by iModIntro. 
    Qed.

    Global Instance ElimModal_fupd_MU p E' E ζ P Q:
      ElimModal (E' ⊆ E) p false
        (|={E'}=> P) P
        (MU E ζ Q) (MU E ζ Q).
    Proof using. apply ElimModal_fupd_MU_impl. Qed. 

    Global Instance ElimModal_fupd_MU__f p E' E ζ f P Q:
      ElimModal (E' ⊆ E) p false
        (|={E'}=> P) P
        (MU__f E f ζ Q) (MU__f E f ζ Q).
    Proof using. apply ElimModal_fupd_MU_impl. Qed.
    
    Lemma fupd_MU_impl f E ζ P:
      (|={E, ∅}=> MU_impl f ∅ ζ (|={∅, E}=>P)) -∗ MU_impl f E ζ P.
    Proof using.
      iIntros "MU". rewrite /MU_impl. iIntros.
      iMod "MU". iMod ("MU" with "[$]") as (??) "[SI P]".
      iMod "P". iModIntro. iExists _, _. iFrame.
    Qed.

    Lemma sswp_MU_wp_fupd s E E' ζ e Φ
      (NVAL: language.to_val e = None)
      :
      let sswp_post := λ e', (▷ MU E' ζ (|={E',E}=> WP e' @ s; ζ; E {{ Φ }}))%I in
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
      iApply (step_fupdN_le 2); [| done| ].
      { pose proof (trace_length_at_least extr). lia. }
      simpl.
      iApply (step_fupd_wand with "Hsswp").
      iIntros ">(Hσ & HMU & ->)".
      iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS' !> !>". 
      rewrite /MU. iSpecialize ("HMU" $! (extr :tr[Some ζ]: _) atr with "[MSI Hσ]").
      { clear NVAL Hvalid Hs EV.        
        
        rewrite /trace_interp_interim. simpl. 
        remember (trace_last extr) as xx. destruct xx as [tp h].
        inversion Hextr as [[TP HH]].
        
        iApply bi.sep_assoc. iSplitL.
        2: { iPureIntro. repeat rewrite and_assoc. split.
             - repeat rewrite -and_assoc. repeat split; eauto.  
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
        simpl. rewrite -TP -Heqxx. subst. iFrame. }
      iMod "CLOS'" as "_". iMod "HMU" as (??) "[Hσ Hwp]". iMod "Hwp". iModIntro.
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
    
    Lemma sswp_MUf_wp s E τ (Φ: val -> iProp Σ) e
      :
      (∀ τ', ▷ MU__f E τ τ' ((WP e @ s; τ'; ⊤ {{ fun r => fork_post (irisG := iG) τ' r }}) ∗ Φ #())) -∗
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
      { rewrite /trace_interp_interim. simpl.
        (* rewrite /obls_si. iDestruct "MSI" as "(M & %TS & %DPO)". *)
        remember (trace_last extr) as xx. destruct xx as [tp h].
        inversion Hexend as [[TP HH]].
        rewrite TP. simpl. iFrame. 
        iPureIntro. repeat split; try done. 
        (* - by rewrite -TP. *)
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
    
End ProgramLogic.
