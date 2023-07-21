From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre.
(* From trillium.fairness Require Export resources fuel. *)
From trillium.fairness.heap_lang Require Export lang.

Class ExecutionModel (M: Model) := {

    (* TODO: how to express that these two are typeclasses themselves? *)
    em_preGS: gFunctors -> Set;
    em_GS: gFunctors -> Set;
    em_Σ: gFunctors;
    em_Σ_subG: forall Σ, subG em_Σ Σ -> em_preGS Σ;        

    (* em_valid_state_evolution_fairness: execution_trace heap_lang -> auxiliary_trace M -> Prop; *)
    em_valid_evolution_step:
    olocale heap_lang → cfg heap_lang → mstate M → mlabel M → mstate M → Prop;

    (* em_fork_post {Σ} *)
    em_thread_post {Σ} `{em_GS Σ}
    : locale heap_lang ->
      (* val -> *)
      iProp Σ;
    em_msi {Σ} `{em_GS Σ}: cfg heap_lang -> mstate M -> iProp Σ;
    
    em_init_resource {Σ: gFunctors} `{em_GS Σ}: mstate M → iProp Σ;
    (* TODO: currently we assume that postconditions of all threads coincide *)
    (* em_init_thread_post {Σ}: locale heap_lang -> val -> iProp Σ; *)
    em_is_init_st: cfg heap_lang -> mstate M -> Prop;
    
    em_initialization Σ `{ePreGS: em_preGS Σ}: 
    forall (s1: mstate M) (σ: cfg heap_lang)
      (INIT_ST: em_is_init_st σ s1),
      ⊢ (|==> ∃ eGS: em_GS Σ, @em_init_resource _ eGS s1 ∗ @em_msi _ eGS σ s1)
}.


(* TODO: the missing fact of em_GS etc. being typeclasses
   hardens automatic resolution of their instances *)
Class heapGpreS Σ `(EM: ExecutionModel) := HeapPreG {
  heapGpreS_inv :> invGpreS Σ;
  heapGpreS_gen_heap :> gen_heapGpreS loc val Σ;
  heapGpreS_em :> em_preGS Σ;
}.

Class heapGS Σ `(EM: ExecutionModel) := HeapG {
  heap_inG :> heapGpreS Σ EM;

  heap_invGS :> invGS_gen HasNoLc Σ;
  heap_gen_heapGS :> gen_heapGS loc val Σ;

  heap_fairnessGS :> em_GS Σ;
}.

Definition heapΣ `(EM: ExecutionModel M) : gFunctors :=
  #[ invΣ; gen_heapΣ loc val; em_Σ ].

(* TODO: automatize *)
Global Instance subG_heapPreG {Σ} `{EM: ExecutionModel M} :
  subG (heapΣ EM) Σ → heapGpreS Σ EM.
Proof.
  intros. 
  enough (em_preGS Σ); [solve_inG| ].
  apply em_Σ_subG. solve_inG.
Qed. 

Definition em_valid_state_evolution_fairness `{EM: ExecutionModel M}
  (extr : execution_trace heap_lang) (auxtr: auxiliary_trace M) :=
  match extr, auxtr with
  | (extr :tr[oζ]: σ), auxtr :tr[ℓ]: δ =>
      (* labels_match (LM:=LM) oζ ℓ ∧ LM.(lm_ls_trans) (trace_last auxtr) ℓ δ ∧ *)
      (* tids_smaller es δ *)
      em_valid_evolution_step oζ σ (trace_last auxtr) ℓ δ
  | _, _ => True
  end.

#[global] Instance heapG_irisG `{EM: ExecutionModel M} `{HGS: !heapGS Σ EM}:
  irisG heap_lang M Σ := {
    state_interp extr auxtr :=
      (⌜em_valid_state_evolution_fairness extr auxtr⌝ ∗
       gen_heap_interp (trace_last extr).2.(heap) ∗
       em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS))%I ;
    fork_post tid := fun _ => em_thread_post tid (em_GS0 := heap_fairnessGS);
}.


Section GeneralProperties.
  Context `{EM: ExecutionModel M}. 
  Context `{HGS: @heapGS Σ _ EM}.
  Let eGS := heap_fairnessGS. 

  Lemma posts_of_empty_mapping  (e1 e: expr) v (tid : nat) (tp : list expr):
    tp !! tid = Some e ->
    to_val e = Some v ->
    posts_of tp (
        (* (λ (_ : val), 0%nat ↦M ∅) *)
        (fun _ => em_thread_post 0%nat (em_GS0 := eGS))
                   ::  (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) tp)))) -∗
      (* tid ↦M ∅. *)
      em_thread_post tid (em_GS0 := eGS).
  Proof.
    intros Hsome Hval. simpl.
    
    rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (fun _ => em_thread_post tid)) _) //.
    apply elem_of_list_omap.
    exists (e, (fun _ => em_thread_post tid (em_GS0 := eGS))); split; last first.
    - simpl. apply fmap_Some. exists v. split; done.
    - destruct tp as [|e1' tp]; first set_solver. simpl.
      apply elem_of_cons.
      destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq.
      apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//.
      rewrite /locale_of /=.
      rewrite list_lookup_fmap fmap_Some. simpl in Hsome.
      exists (e1 :: take tid tp, e). rewrite drop_0. split.
      + erewrite prefixes_from_lookup =>//.
      + rewrite /locale_of /= take_length_le //.
        assert (tid < length tp)%nat; last lia. by eapply lookup_lt_Some.
  Qed.

  Lemma from_locale_from_lookup tp0 tp tid e :
    from_locale_from tp0 tp tid = Some e <-> (tp !! (tid - length tp0)%nat = Some e ∧ (length tp0 <= tid)%nat).
  Proof.
    split.
    - revert tp0 tid. induction tp as [| e1 tp1 IH]; intros tp0 tid.
      { unfold from_locale. simpl. done. }
      unfold from_locale. simpl.
      destruct (decide (locale_of tp0 e1 = tid)).
      + intros ?; simplify_eq. rewrite /locale_of /= Nat.sub_diag.
        split; [done|lia].
      + intros [H Hlen]%IH. rewrite app_length /= in H.
        rewrite app_length /= in Hlen.
        destruct tid as [|tid]; first lia.
        assert (Heq1 : (length tp0 + 1 = S (length tp0))%nat) by lia.
        rewrite Heq1 in Hlen.
        assert (length tp0 ≤ tid)%nat by lia.
        assert (Heq : (S tid - length tp0)%nat = (S ((tid - (length tp0))))%nat) by lia.
        rewrite Heq /=. split.
        * rewrite -H. f_equal. lia.
        * transitivity tid; try lia. assumption.
    - revert tp0 tid. induction tp as [|e1 tp1 IH]; intros tp0 tid.
      { set_solver. }
      destruct (decide (tid = length tp0)) as [-> | Hneq].
      + rewrite Nat.sub_diag /=. intros  [? _]. simplify_eq.
        rewrite decide_True //.
      + intros [Hlk Hlen]. assert (length tp0 < tid)%nat as Hle by lia.
        simpl. rewrite decide_False //. apply IH. split.
        * assert (tid - length tp0 = S ((tid - 1) - length tp0))%nat as Heq by lia.
          rewrite Heq /= in Hlk. rewrite -Hlk app_length /=. f_equal; lia.
        * rewrite app_length /=. apply Nat.le_succ_l in Hle. rewrite Nat.add_comm //.
  Qed.

  
  Lemma from_locale_lookup tp tid e :
    from_locale tp tid = Some e <-> tp !! tid = Some e.
  Proof.
    assert (from_locale tp tid = Some e <-> (tp !! tid = Some e ∧ 0 ≤ tid)%nat) as H; last first.
    { split; intros ?; apply H; eauto. split; [done|lia]. }
    unfold from_locale. replace (tid) with (tid - length (A := expr) [])%nat at 2;
      first apply from_locale_from_lookup. simpl; lia.
  Qed.
  
  Definition indexes {A} (xs : list A) := imap (λ i _, i) xs.
  
  Lemma locales_of_list_from_indexes (es' es : list expr) :
    locales_of_list_from es' es = imap (λ i _, length es' + i)%nat es.
  Proof.
    revert es'. induction es; [done|]; intros es'.
    rewrite locales_of_list_from_cons=> /=. rewrite /locale_of.
    f_equiv; [lia|]. rewrite IHes. apply imap_ext.
    intros x ? Hin. rewrite app_length=> /=. lia.
  Qed.
  
  Lemma locales_of_list_indexes (es : list expr) :
    locales_of_list es = indexes es.
  Proof. apply locales_of_list_from_indexes. Qed.

End GeneralProperties.

(* (* TODO: uncomment this and remove duplicate code from fuel.v *) *)
(* Section TracesMatch. *)
(*   Context `{EM: ExecutionModel M}.  *)

(*   (* TODO: Why do we need explicit [LM] here? *) *)

(*   Definition valid_lift_fairness *)
(*              (φ: execution_trace heap_lang -> auxiliary_trace M -> Prop) *)
(*              (extr : execution_trace heap_lang) (auxtr : auxiliary_trace M) := *)
(*     em_valid_state_evolution_fairness extr auxtr ∧ φ extr auxtr. *)

(*   (* TODO: move*) *)
(*   From trillium.fairness Require Export inftraces *)
(*     fairness *)
(*   . *)
(*   Let auxtrace := trace (mstate M) (mlabel M). *)

(*   Context (state_rel: cfg heap_lang -> mstate M -> Prop). *)
(*   Context (lbl_rel: olocale heap_lang -> mlabel M -> Prop). *)
(*   Hypothesis (LBL_REL_EM: forall oζ σ δ1 ℓ δ2, *)
(*                  em_valid_evolution_step oζ σ δ1 ℓ δ2 -> *)
(*                  lbl_rel oζ ℓ).  *)
(*   Hypothesis (STEP_EM: forall oζ σ δ1 ℓ δ2, *)
(*                  em_valid_evolution_step oζ σ δ1 ℓ δ2 -> *)
(*                  mtrans δ1 ℓ δ2).  *)

(*   Definition exaux_traces_match: *)
(*     extrace heap_lang → auxtrace → Prop := *)
(*     traces_match lbl_rel *)
(*       state_rel *)
(*       locale_step *)
(*       (@mtrans M).  *)

(*   (* TODO: Why do we need explicit [LM] here? *) *)
(*   Lemma valid_inf_system_trace_implies_traces_match_strong *)
(*         (φ : execution_trace heap_lang -> auxiliary_trace M -> Prop) *)
(*         (ψ : _ → _ → Prop) *)
(*         ex atr iex iatr progtr (auxtr : auxtrace): *)
(*     (forall (ex: execution_trace heap_lang) (atr: auxiliary_trace M), *)
(*         φ ex atr -> state_rel (trace_last ex) (trace_last atr)) -> *)
(*     (forall (ex: execution_trace heap_lang) (atr: auxiliary_trace M), *)
(*         φ ex atr -> em_valid_state_evolution_fairness ex atr) -> *)
(*     (∀ extr auxtr, φ extr auxtr → ψ (trace_last extr) (trace_last auxtr)) → *)
(*     exec_trace_match ex iex progtr -> *)
(*     exec_trace_match atr iatr auxtr -> *)
(*     valid_inf_system_trace φ ex atr iex iatr -> *)
(*     traces_match lbl_rel *)
(*                  (λ σ δ, state_rel σ δ ∧ ψ σ δ) *)
(*                  locale_step *)
(*                  (@mtrans M) progtr auxtr. *)
(*   Proof.  *)
(*     intros Hφ1 Hφ2 Hφψ. *)
(*     revert ex atr iex iatr auxtr progtr. cofix IH. *)
(*     intros ex atr iex iatr auxtr progtr Hem Ham Hval. *)
(*     inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq. *)
(*     - inversion Hem; inversion Ham. econstructor; eauto. *)
(*       pose proof (Hφ1 ex atr Hphi). *)
(*       split; [by simplify_eq|]. simplify_eq. by apply Hφψ. *)
(*     - inversion Hem; inversion Ham. subst. *)
(*       pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'. *)
(*       specialize (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as STEP. *)
(*       red in STEP.        *)
(*       econstructor. *)
(*       + eapply LBL_REL_EM; eauto.  *)
(*       + eauto. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; done. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; eapply STEP_EM; eauto.  *)
(*       + eapply IH; eauto. *)
(*   Qed. *)

(*   (* TODO: Why do we need explicit [LM] here? *) *)
(*   Lemma valid_inf_system_trace_implies_traces_match *)
(*         (φ: execution_trace heap_lang -> auxiliary_trace M -> Prop) *)
(*         ex atr iex iatr progtr (auxtr : auxtrace): *)
(*     (forall (ex: execution_trace heap_lang) (atr: auxiliary_trace M), *)
(*         φ ex atr -> state_rel (trace_last ex) (trace_last atr)) -> *)
(*     (forall (ex: execution_trace heap_lang) (atr: auxiliary_trace M), *)
(*         φ ex atr -> em_valid_state_evolution_fairness ex atr) -> *)
(*     exec_trace_match ex iex progtr -> *)
(*     exec_trace_match atr iatr auxtr -> *)
(*     valid_inf_system_trace φ ex atr iex iatr -> *)
(*     exaux_traces_match progtr auxtr. *)
(*   Proof. *)
(*     intros Hφ1 Hφ2. *)
(*     revert ex atr iex iatr auxtr progtr. cofix IH. *)
(*     intros ex atr iex iatr auxtr progtr Hem Ham Hval. *)
(*     inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq. *)
(*     - inversion Hem; inversion Ham. econstructor; eauto. *)
(*       pose proof (Hφ1 ex atr Hphi). *)
(*       by simplify_eq. *)
(*     - inversion Hem; inversion Ham. subst. *)
(*       pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'. *)
(*       specialize (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as STEP. *)
(*       red in STEP.        *)
(*       econstructor. *)
(*       + eauto. *)
(*       + eauto. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; done. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; eapply STEP_EM; eauto.  *)
(*       + eapply IH; eauto. *)
(*   Qed. *)

(* End TracesMatch.  *)
