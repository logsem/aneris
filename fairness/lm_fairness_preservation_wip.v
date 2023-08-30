From stdpp Require Import option.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness fuel traces_match trace_utils.
From trillium.fairness Require Export lm_fairness_preservation. 
Require Import Coq.Logic.Classical.

(* TODO: move these files to trillium.fairness *)
From trillium.fairness.examples.comp Require Export trace_lookup trace_len my_omega lemmas. 


Section InnerLMTraceFairness.
  Context `{LMi: LiveModel Gi Mi}.
  (* Context `{EqDecision Gi}. *)

  Context `{LMo: LiveModel Go Mo}.

  Context (lift_Gi: Gi -> fmrole Mo).
  Hypothesis (INJlg: Inj eq eq lift_Gi). 

  Context (state_rel: fmstate Mo → lm_ls LMi → Prop).

  Let lm_model_traces_match :=
    lm_exaux_traces_match_gen
      (fmtrans Mo)
      lift_Gi
      state_rel.

  (* TODO: move *)
  Lemma traces_match_same_length_impl {L1 L2 S1 S2 : Type}
    R1 R2 step1 step2 tr1 tr2 len1 len2
    (LEN1: trace_len_is tr1 len1)
    (LEN2: trace_len_is tr2 len2)
    (MATCH: @traces_match L1 L2 S1 S2 R1 R2 step1 step2 tr1 tr2)
    (LT: NOmega.lt len1 len2):
    False. 
  Proof.
    destruct len1; [done| ].
    pose proof (proj2 (LEN2 n)) as LL2. specialize (LL2 ltac:(lia_NO len2)) as [atr2 AFTER2].
    pose proof (traces_match_after _ _ _ _ _ _ _ _ MATCH AFTER2) as (atr1 & AFTER1 & _).
    specialize (proj1 (LEN1 _) (mk_is_Some _ _ AFTER1)). simpl. lia.
  Qed.
    

  (* TODO: move *)
  Lemma traces_match_same_length {L1 L2 S1 S2 : Type}
    R1 R2 step1 step2 tr1 tr2 len1 len2
    (LEN1: trace_len_is tr1 len1)
    (LEN2: trace_len_is tr2 len2)
    (MATCH: @traces_match L1 L2 S1 S2 R1 R2 step1 step2 tr1 tr2):
    len1 = len2.
  Proof. 
    unfold trace_len_is in *.
    destruct (NOmega.lt_trichotomy len1 len2) as [?|[?|?]]; auto; exfalso. 
    - eapply traces_match_same_length_impl with (tr1 := tr1) (tr2 := tr2); eauto. 
    - apply traces_match_flip in MATCH. 
      eapply traces_match_same_length_impl with (tr1 := tr2) (tr2 := tr1); eauto.
  Qed. 

  (* TODO: move *)
  Lemma trace_label_lookup_simpl {St L: Type} (tr: trace St L) i step ℓ
    (TLi: tr !! i = Some step)
    (SLi: tr L!! i = Some ℓ):
    exists s1 s2, step = (s1, Some (ℓ, s2)). 
  Proof.
    rewrite /label_lookup in SLi. rewrite /lookup /trace_lookup in TLi.
    (* destruct (trace_lookup_impl tr i) as [[??]|]; congruence.  *)
    destruct (after i tr); try done.
    destruct t; try done. inversion SLi. inversion TLi. subst. eauto.  
  Qed. 

  Local Ltac gd t := generalize dependent t.

  (* TODO: move *)
  Lemma state_lookup_0 {St L: Type} (tr: trace St L):
    tr S!! 0 = Some (trfirst tr). 
  Proof. by destruct tr. Qed.

  Definition inner_obls_exposed (lmtr_o: auxtrace (LM := LMo)) :=
    forall k δo_k gi, lmtr_o !! k = Some δo_k ->
                 (exists (δi: LiveState Gi Mi) (ρi: fmrole Mi),
                    state_rel (ls_under δo_k) δi /\
                    ls_mapping δi !! ρi = Some gi) ->
                 lift_Gi gi ∈ dom (ls_mapping δo_k). 
  

  (* TODO: move, generalize? *)
  From Paco Require Import paco1 paco2 pacotac.
  Lemma upto_stutter_auxtr_trfirst lmtr_o mtr_o
    (CORRo: upto_stutter_auxtr lmtr_o mtr_o (LM := LMo)): 
    ls_under (trfirst lmtr_o) = trfirst mtr_o.
  Proof.
    punfold CORRo.
    2: { apply upto_stutter_mono. }    
    by inversion CORRo. 
  Qed. 

  (* TODO: rename? *)
  Lemma eventual_step_or_unassign lmtr_o mtr_o lmtr_i ρ go δi f
    (MATCH: lm_model_traces_match mtr_o lmtr_i)
    (CORRo: upto_stutter_auxtr lmtr_o mtr_o (LM := LMo))
    (INNER_OBLS: inner_obls_exposed lmtr_o)
  (* (INF : trace_len_is tr_o NOinfinity *)
  (* (INF' : trace_len_is lmtr_i NOinfinity *)
  (EN: ∀ (m : nat) (δi_m : lm_ls LMi),
      lmtr_i S!! m = Some δi_m → role_enabled ρ δi_m)
  (NOρ : ∀ (m : nat) (ℓ : lm_lbl LMi),
          lmtr_i L!! m = Some ℓ → ∀ go' : Gi, ℓ ≠ Take_step ρ go')
  (ASGρ : ∀ (k : nat) (δi_k : lm_ls LMi),
           lmtr_i S!! k = Some δi_k → ls_mapping δi_k !! ρ = Some go)
  (ST0: lmtr_i S!! 0 = Some δi)
  (FUEL0: ls_fuel δi !! ρ = Some f):
    ∃ m, pred_at lmtr_i m (steps_or_unassigned ρ).
  Proof.
    Local Set Printing Coercions.
    gd lmtr_i. gd δi. gd mtr_o. gd lmtr_o. induction f.
    { intros.
      pose proof (traces_match_first _ _ _ _ _ _ MATCH) as REL0.
      pose proof (upto_stutter_auxtr_trfirst _ _ CORRo) as CORR0. 
      assert (is_Some (ls_mapping δi !! ρ)) as [gi MAPi].
      { apply elem_of_dom. rewrite ls_same_doms. eapply elem_of_dom; eauto. } 

      specialize (INNER_OBLS 0 (trfirst lmtr_o) gi). specialize_full INNER_OBLS.
      { apply state_lookup_0. }
      { do 2 eexists. split; eauto.
        rewrite CORR0. rewrite state_lookup_0 in ST0. congruence. }

      foobar. 
        
      clear -CORRo.
      red in CORRo. 
      
      



  (* TODO: is it possible to unify this proof with those in lm_fairness_preservation? *)
  (* TODO: renaming of arguments? *)
  Lemma inner_LM_trace_fair_aux (tr_o: mtrace Mo) (lmtr_i: auxtrace (LM := LMi)):
    infinite_trace tr_o ->
    lm_model_traces_match tr_o lmtr_i ->
    (∀ ρ, fair_model_trace ρ tr_o) -> (forall ρ, fair_aux ρ lmtr_i (LM := LMi)).
  Proof. 
    intros INF MATCH FAIRo ρ.
    destruct (classic (fair_aux ρ lmtr_i)) as [| UNFAIR]; [done| exfalso].

    rewrite /fair_aux in UNFAIR. setoid_rewrite <- pred_at_or in UNFAIR. 
    apply not_all_ex_not in UNFAIR as [n UNFAIR].
    apply imply_to_and in UNFAIR as [ENn UNFAIR].
    pose proof (not_ex_all_not _ _ UNFAIR) as X. simpl in X.
    clear UNFAIR. rename X into UNFAIR.

    assert (trace_len_is tr_o NOinfinity) as INF'.
    { admit. }
    assert (trace_len_is lmtr_i NOinfinity) as INF''.
    { pose proof (trace_has_len lmtr_i) as [li ?].
      forward eapply traces_match_same_length as INF''; [| |by apply MATCH|]; eauto.
      by subst. }
    
    setoid_rewrite pred_at_neg in UNFAIR; [| by apply INF''].
    setoid_rewrite pred_at_trace_lookup' in UNFAIR. simpl in UNFAIR.
    assert (forall m δi_m, n <= m -> lmtr_i S!! m = Some δi_m -> role_enabled ρ (ls_under δi_m)) as EN.
    { intros. apply Nat.le_sum in H as [d ->].
      specialize (UNFAIR d) as (? & ? & MTH & UNFAIR).
      eapply trace_state_lookup_simpl in MTH; eauto. subst.
      apply Decidable.not_or in UNFAIR.
      tauto. }
    assert (forall m ℓ, n <= m -> lmtr_i L!! m = Some ℓ -> forall go', ℓ ≠ Take_step ρ go') as NOρ.
    { intros. apply Nat.le_sum in H as [d ->].
      specialize (UNFAIR d) as (? & ? & MTH & UNFAIR).
      eapply trace_label_lookup_simpl in MTH as (?&?&EQ); eauto.
      inversion EQ. subst.
      apply Decidable.not_or, proj2 in UNFAIR.
      simpl in UNFAIR. intros ->. eauto. }
      
    (* apply pred_at_trace_lookup in ENn as (δi & NTH & ENn). *)
    (* red in ENn. Local Set Printing Coercions. *)
    clear ENn. 

    assert (exists j go, n <= j /\ forall k δi_k, j <= k -> lmtr_i S!! k = Some δi_k ->
                                       ls_mapping δi_k !! ρ = Some go) 
      as (j & go & LE & ASGρ). 
    { admit. }

    assert (is_Some (lmtr_i S!! j)) as [δi_j JTH].
    { eapply state_lookup_dom; eauto. done. }
    assert (is_Some (ls_fuel δi_j !! ρ)) as [f FUEL].
    { apply elem_of_dom. rewrite -ls_same_doms.
      apply ls_mapping_dom.
      eapply EN; eauto. }  
      
    

    

End InnerLMTraceFairness. 
