From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context wptp_gen pwp wfree_traces calls.
From lawyer.nonblocking.tokens Require Import sub_expr logrel_tok.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em.
From lawyer Require Import program_logic.  
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From heap_lang Require Import sswp_logic lang.


Close Scope Z. 


Section CallTracker.

  Class CallTrackerPre Σ := {
    ct_pre_expr :: inG Σ (excl_authUR (option expr));
  }.

  Class CallTracker Σ := {
    ct_pre :: CallTrackerPre Σ;
    ct_γ: gname;
  }.

  Context `{CallTracker Σ}.

  Definition ct_auth (oe: option expr) := own ct_γ $ ● (Some $ Excl oe).
  Definition ct_frag (oe: option expr) := own ct_γ $ ◯ (Some $ Excl oe).

  Lemma ct_auth_frag_agree c1 c2:
    ct_auth c1 -∗ ct_frag c2 -∗ ⌜ c2 = c1 ⌝. 
  Proof using.
    simpl.
    rewrite bi.wand_curry -own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    iPureIntro. symmetry. by apply excl_auth_agree_L.
  Qed.  

  Lemma ct_auth_frag_update c1 c2 c':
    ct_auth c1 -∗ ct_frag c2 ==∗ ct_auth c' ∗ ct_frag c'. 
  Proof using.
    simpl. 
    rewrite bi.wand_curry -!own_op.
    iApply own_update. apply excl_auth_update. 
  Qed.

End CallTracker.


Section PwpExtra.
  Context (LG: LangEM heap_lang).
  Context `{invGS_gen HasNoLc Σ} {lGS: lgem_GS Σ} {ctGS: CallTracker Σ}.

  Context (m: val) (τ: locale heap_lang).

  Definition inside_call (K: ectx heap_lang) (i: nat) (etr: execution_trace heap_lang) (e: expr) :=
    let κ := TpoolCtx K τ in
    let last_ind := trace_length etr - 1 in
    exists (a: val),      
      (exists s, etr !! i = Some s /\ call_at κ s m a (APP := App)) /\
      i < last_ind /\ 
      (** finite_trace_to_trace reverses the trace; use alt def of no_return_before instead *)
      (* no_return_before (finite_trace_to_trace etr) κ i (trace_length etr - 1) /\ *)
      (forall j, i <= j <= last_ind -> from_option (nval_at κ) False (etr !! j)) /\
      from_option (fun eτ => under_ctx K eτ = Some e) False ((trace_last etr).1 !! τ)
  . 

  Lemma inside_call_extend extr tp1 tp2 K e σ1
    (Hζ : locale_of tp1 (fill K e) = τ)
    (Hextr : trace_ends_in extr (tp1 ++ fill K e :: tp2, σ1))
    (s : nat)
    (CALL : inside_call K s extr e)
    (e2 : expr)
    (σ2 : state)
    (STEP : ectx_language.prim_step e σ1 e2 σ2 [])
    (V2 : to_val e2 = None):
    inside_call K s (extr :tr[ Some τ ]: (tp1 ++ fill K e2 :: tp2 ++ [], σ2)) e2.
  Proof using.
    red in CALL. destruct CALL as (a & CALL & PREV & NORET & CUR).
    pose proof (trace_length_at_least extr) as LENnz. simpl in LENnz.
    remember (trace_length extr) as N.
    red. exists a. simpl. rewrite -HeqN. rewrite -HeqN in LENnz PREV.
     repeat split.
    - destruct CALL as (?&CALL&?). eexists. split; eauto.
      rewrite -CALL. apply trace_lookup_extend_lt. rewrite -HeqN. lia.
    - lia.
    - simpl. intros j DOM.
      assert (s <= j <= trace_length extr - 1 \/ j = trace_length extr) as [DOM' | ->].
      { lia. }
      + pose proof DOM' as X%NORET. 
        destruct (extr !! j) eqn:JTH; rewrite JTH /= in X; [| done].
        rewrite trace_lookup_extend_lt.
        2: { rewrite -HeqN. lia. }
        rewrite JTH. eauto.
      + rewrite trace_lookup_last.
        2: { simpl. rewrite -HeqN. lia. }
        simpl.
        red. eexists. split; [| apply V2]. 
        red.
        rewrite -Hζ. rewrite /from_locale.
        by rewrite from_locale_from_locale_of.
    - rewrite app_nil_r.
      rewrite -Hζ. rewrite /locale_of.
      rewrite list_lookup_middle; [| done].
      simpl. by apply under_ctx_spec.
  Qed. 

  Lemma bump_inside_call K s0 e τ' c'' etr
    (OTHER: τ' ≠ τ)
    (CALL: inside_call K s0 etr e)
    (STEP: locale_step (trace_last etr) (Some τ') c'')
    :
  inside_call K s0 (etr :tr[ Some τ' ]: c'') e.
  Proof using.
    clear -CALL STEP OTHER.
    unfold inside_call in *.
    destruct CALL as (a & CALL & PREV & NORET & CUR).
    exists a. repeat split.
    - destruct CALL as (?&?&?).
      eexists. split; eauto. rewrite -H.
      apply trace_lookup_extend_lt. lia.
    - simpl in *. lia.
    - simpl. rewrite Nat.sub_0_r.
      intros j [GE LE]. apply Nat.le_lteq in LE as [LT | ->].
      { simpl in *. specialize (NORET j ltac:(lia)).
        destruct (etr !! j) eqn:JTH; [| done].
        rewrite trace_lookup_extend_lt; [| done].
        by rewrite JTH. }
      rewrite trace_lookup_extend /=; [| done].
      specialize (NORET (trace_length etr -1) ltac:(lia)).
      destruct (etr !! (trace_length etr - 1)) eqn:LAST; [| done]. simpl in *.
      rewrite trace_lookup_last in LAST.
      2: simpl; lia.
      inversion LAST. subst c.
      destruct NORET as (?&?&?). simpl in *.
      eapply locale_step_other_same in STEP; eauto.
      2: congruence.
      red. eauto.
    - simpl.
      destruct ((trace_last etr).1 !! τ) eqn:TT; [| done]. simpl in *.
      apply under_ctx_spec in CUR. subst. 
      eapply locale_step_other_same in STEP; eauto.
      2: { apply from_locale_lookup. eauto. }
      2: congruence.
      apply from_locale_lookup in STEP. rewrite STEP /=.
      eapply under_ctx_spec; eauto.
  Qed.

  Context (tok: iProp Σ).

  Definition safe_sub_values `{heap1GS Σ} (c: cfg heap_lang): iProp Σ :=
    ∀ e v, ⌜ c.1 !! τ = Some e ⌝ -∗
           ⌜ is_sub_expr (Val v) e ⌝ -∗ 
           interp tok v.

  Definition ct_interp `{heap1GS Σ} (etr: execution_trace heap_lang): iProp Σ
    (* (oe: option expr) *)
    :=
    ∃ (oe: option expr), ct_auth oe ∗
    (tok ∗ ⌜ oe = None ⌝ ∗ safe_sub_values (trace_last etr) ∨
     ∃ e K s, ⌜ oe = Some e /\ inside_call K s etr e⌝ ∗ from_option safe_sub_values ⌜ False ⌝ (etr !! s))
  .

  (* Definition irisG_phys_cti (LG: LangEM heap_lang) `{invGS_gen HasNoLc Σ} {lG: lgem_GS Σ}: *)
  (*   irisG heap_lang LoopingModel Σ := {| *)
  (*     state_interp etr mtr := (phys_SI LG etr mtr (lG := lG) ∗ ct_interp etr)%I; *)
  (*     fork_post := fun _ _ => (⌜ True ⌝)%I; *)
  (* |}. *)
  
End PwpExtra.

(* (* TODO: rename *) *)
(* Definition iris_OM_into_phys_cti {Σ} `(Hinv : @IEMGS heap_lang M LG EM Σ) (CT: CallTracker Σ) *)
(*   (m: val) (τ: locale heap_lang) (tok: iProp Σ) *)
(*   : *)
(*   irisG heap_lang LoopingModel Σ. *)
(* Proof using. *)
(*   eapply (irisG_phys_cti m τ tok); apply Hinv. *)
(* Defined. *)
