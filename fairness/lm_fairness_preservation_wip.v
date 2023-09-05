From stdpp Require Import option.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness fuel traces_match trace_utils.
From trillium.fairness Require Export lm_fairness_preservation. 
Require Import Coq.Logic.Classical.

(* TODO: move these files to trillium.fairness *)
From trillium.fairness.examples.comp Require Export trace_lookup trace_len my_omega lemmas trace_helpers.

From Paco Require Import paco1 paco2 pacotac.


(* TODO: rename *)
Section Foobar. 
  Context `{LM: LiveModel G M}.
  Context `{Countable G}.

  Local Set Printing Coercions.
  Local Ltac gd t := generalize dependent t.

  (* TODO: move *)
  Lemma after_0_id {St L : Type} (tr : trace St L):
    after 0 tr = Some tr.
  Proof. done. Qed. 

  (* TODO: move *)
  Lemma upto_stutter_step_correspondence auxtr (mtr: mtrace M)
    (Po: LiveState G M -> option (mlabel LM) -> Prop)
    (Pi: M -> option (option (fmrole M)) -> Prop)
    (LIFT: forall δ oℓ, Po δ oℓ -> Pi (ls_under δ) (match oℓ with 
                                              | Some ℓ => Ul ℓ (LM := LM)
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_auxtr auxtr mtr (LM := LM) ->
    (* (∃ n, pred_at auxtr n Po) -> *)
    (* ∃ m, pred_at mtr m Pi. *)
    forall n atr_aux,
      after n auxtr = Some atr_aux ->
      pred_at atr_aux 0 Po ->
    exists m atr_m,
      after m mtr = Some atr_m /\ pred_at atr_m 0 Pi /\ 
      upto_stutter_auxtr atr_aux atr_m.
  Proof.
    intros Hupto n. gd auxtr. gd mtr. 

      induction n as [|n]; intros auxtr mtr Hupto atr_aux AFTER A0.
      - rewrite after_0_id in AFTER. assert (atr_aux = mtr) as -> by congruence.
        do 2 eexists. split; [| split]; [..| by eauto].
        { by erewrite after_0_id. }
        punfold Hupto; [| by apply upto_stutter_mono']. inversion Hupto; simplify_eq.
        + rename A0 into Hpa.
          rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
          by apply LIFT in Hpa. 
        + rewrite -> !pred_at_0 in A0.
          rewrite /pred_at /=. destruct auxtr; simpl in *; try congruence.
          * apply LIFT in A0. congruence.
          * apply LIFT in A0. destruct ℓ; simpl in *; try done.
            all: subst; eapply PI0; eauto.
        + rewrite -> !pred_at_0 in A0.
          apply pred_at_0. rewrite <- H1.
          by eapply LIFT in A0. 
      - punfold Hupto; [| by apply upto_stutter_mono']. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
        + simpl in AFTER. 
          eapply IHn; eauto.
          by pfold.
        + simpl in AFTER. 
          specialize (IHn str btr). specialize_full IHn.
          { inversion IH; eauto. done. } 
          all: eauto.
          destruct IHn as (m & atr_m & AFTER' & UPTO'). 
          exists (S m). eauto. 
  Qed.

  Definition upto_stutter_auxtr_at `{LM: LiveModel G M}
    auxtr (mtr: mtrace M) n m :=
    exists atr_aux atr_m, 
      after n auxtr = Some atr_aux /\
      after m mtr = Some atr_m /\ 
      upto_stutter_auxtr atr_aux atr_m (LM := LM).
    
  (* TODO: move *)
  Lemma upto_stutter_step_correspondence_alt auxtr (mtr: mtrace M)
    (Po: LiveState G M -> option (mlabel LM) -> Prop)
    (Pi: M -> option (option (fmrole M)) -> Prop)
    (LIFT: forall δ oℓ, Po δ oℓ -> Pi (ls_under δ) (match oℓ with 
                                              | Some ℓ => Ul ℓ (LM := LM)
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_auxtr auxtr mtr (LM := LM) ->
    forall n, pred_at auxtr n Po ->
    exists m, pred_at mtr m Pi /\ upto_stutter_auxtr_at auxtr mtr n m. 
  Proof.
    intros UPTO n NTH.
    forward eapply pred_at_after_is_Some as [atr AFTER]; eauto.
    rewrite (plus_n_O n) pred_at_sum AFTER in NTH. 
    forward eapply upto_stutter_step_correspondence as (m&?&AFTERm&Pm&?); eauto.
    exists m. split.
    - rewrite (plus_n_O m) pred_at_sum AFTERm. apply Pm.
    - red. eauto.
  Qed.    

  (* TODO: move, replace original proof (but keep old signature) *)
  Lemma upto_stutter_fairness_0 ρ auxtr (mtr: mtrace M):
    upto_stutter_auxtr auxtr mtr (LM := LM) ->
    (∃ n, pred_at auxtr n (λ δ ℓ, ¬role_enabled (G := G) ρ δ \/ ∃ ζ, ℓ = Some (Take_step ρ ζ))) ->
    ∃ m, pred_at mtr m (λ δ ℓ, ¬role_enabled_model ρ δ \/ ℓ = Some $ Some ρ).
  Proof.
    intros UPTO [n NTH].
    forward eapply pred_at_after_is_Some as [atr AFTER]; eauto.
    rewrite (plus_n_O n) in NTH. 
    rewrite pred_at_sum AFTER in NTH. 
    forward eapply upto_stutter_step_correspondence; eauto.
    3: { intros (m & atr_m & AFTERm & Pm & UPTO').
         exists m. rewrite (plus_n_O m) pred_at_sum AFTERm. apply Pm. }
    - intros ?? Po. destruct Po as [?| [? ->]]; eauto. 
    - intros. destruct H0; [| done]. eauto.
  Qed.

End Foobar. 


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
    forall k δo_k gi, lmtr_o S!! k = Some δo_k ->
                 (exists (δi: LiveState Gi Mi) (ρi: fmrole Mi),
                    state_rel (ls_under δo_k) δi /\
                    ls_mapping δi !! ρi = Some gi) ->
                 lift_Gi gi ∈ dom (ls_mapping δo_k). 
  

  (* TODO: move, generalize? *)
  Lemma upto_stutter_trfirst {St S' L L' : Type} 
    (Us : St → S') (Ul: L → option L') 
    btr str
    (CORR: upto_stutter Us Ul btr str):
    trfirst str = Us (trfirst btr). 
  Proof.
    punfold CORR.
    2: { apply upto_stutter_mono. }
    by inversion CORR.
  Qed. 

  (* TODO: move *)
  Lemma upto_stutter_after' {St S' L L' : Type} (Us : St → S') (Ul: L → option L') 
    {btr : trace St L} {str : trace S' L'} (n : nat) {btr' : trace St L}:
    upto_stutter Us Ul btr str
    → after n btr = Some btr'
      → ∃ (n' : nat) (str' : trace S' L'),
          after n' str = Some str' ∧ upto_stutter Us Ul btr' str'.
  Proof. 
    have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
    { intros P [x ?]. by exists (S x). }

    intros. 
    gd btr. gd str. gd btr'. induction n as [|n IH]; intros btr' str btr Hupto Hafter.
    { injection Hafter => <-. clear Hafter. exists 0, str. done. }
    punfold Hupto; [| apply upto_stutter_mono]. 
    inversion Hupto; subst. 
    - done.
    - simpl in Hafter. rename btr0 into btr. 
      specialize (IH btr' str btr). specialize_full IH; eauto.
      by pfold.
    - simpl in Hafter. rename btr0 into btr. rename str0 into str.
      specialize (IH btr' str btr).
      specialize_full IH; eauto. 
      (* TODO: proper way of doing it? *)
      inversion H1; eauto. done.
  Qed. 

  (* TODO: move *)
  Lemma upto_stutter_state_lookup' {St S' L L' : Type} (Us : St → S') (Ul: L → option L') 
    {btr : trace St L} {str : trace S' L'} (n : nat) bst:
    upto_stutter Us Ul btr str
    → btr S!! n = Some bst ->
      ∃ (n' : nat),
        str S!! n' = Some (Us bst).
  Proof.
    intros UPTO NTH.
    pose proof (trace_has_len btr) as [? LEN]. 
    pose proof (proj1 (state_lookup_dom _ _ LEN n) (mk_is_Some _ _ NTH)) as BOUND.
    pose proof (proj2 (LEN _) BOUND) as [btr_n AFTER].
    forward eapply (upto_stutter_after' _ _ n UPTO); eauto.
    intros (n' & str' & AFTER' & UPTOn).
    exists n'.
    rewrite -(Nat.add_0_r n'). erewrite <- state_lookup_after; eauto.
    rewrite state_lookup_0. f_equal.     
    erewrite upto_stutter_trfirst; [..| apply UPTOn]; eauto.
    f_equal. apply Some_inj.
    rewrite -state_lookup_0.
    erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r.
  Qed. 

  (* TODO: move *)
  Lemma trace_state_lookup_simpl' {St L: Type}
    (tr: trace St L) i st:
    (exists step, tr !! i = Some step /\ fst step = st) <-> tr S!! i = Some st. 
  Proof.
    rewrite /state_lookup /lookup /trace_lookup.
    destruct after.
    2: { split; [intros (?&?&?) | intros ?]; done. }
    destruct t.
    all: split; [intros  ([??]&?&?) | intros [=]]; simpl in *; subst.
    all: congruence || eauto. 
  Qed. 

  (* TODO: move *)
  Lemma trace_label_lookup_simpl' {St L: Type}
    (tr: trace St L) i ℓ:
    (exists s1 s2, tr !! i = Some (s1, Some (ℓ, s2))) <-> tr L!! i = Some ℓ. 
  Proof.
    split.
    - intros (?&?&?%state_label_lookup). tauto.
    - rewrite /label_lookup /lookup /trace_lookup.
      destruct after; [| done].
      destruct t; [done| ]. intros [=->]. eauto.
  Qed. 

  Lemma state_lookup_after_0 {St L : Type} (tr atr : trace St L) n
    (AFTER: after n tr = Some atr):
    tr S!! n = Some (trfirst atr).
  Proof. 
    rewrite -(Nat.add_0_r n).
    erewrite <- state_lookup_after; eauto.
    apply state_lookup_0.
  Qed.

  (* TODO: move *)
  Lemma trace_lookup_after' {St L : Type} (tr: trace St L) n st:
    (exists atr, after n tr = Some atr /\ trfirst atr = st) <-> tr S!! n = Some st. 
  Proof. 
    destruct (after n tr) as [atr| ] eqn:AFTER.
    2: { split; [by intros (?&?&?)| ].
         pose proof (trace_has_len tr) as [len ?]. 
         eintros ?%mk_is_Some%state_lookup_dom; eauto.
         eapply trace_len_neg in AFTER; eauto. lia_NO len. }
    erewrite state_lookup_after_0; eauto.
    split. 
    - intros (?&[=->]&?). congruence.
    - intros [=]. eauto.
  Qed. 

  Lemma trace_lookup_after_strong {St L : Type} (tr: trace St L) s1 ℓ s2 n:
    (exists atr', after n tr = Some (s1 -[ℓ]-> atr') /\ trfirst atr' = s2) <-> tr !! n = Some (s1, Some (ℓ, s2)). 
  Proof. 
    destruct (after n tr) as [atr| ] eqn:AFTER.
    2: { split; [by intros (?&?&?)| ].
         pose proof (trace_has_len tr) as [len LEN].
         intros NTH.
         forward eapply (proj1 (trace_lookup_dom_strong _ _ LEN n)); eauto.
         eapply trace_len_neg in AFTER; eauto. lia_NO len. }

    rewrite /lookup /trace_lookup AFTER. 
    split.
    - intros (?&[=->]&?). congruence.
    - intros EQ. destruct atr; [congruence| ].
      inversion EQ. subst. eauto. 
  Qed.

  (* TODO: move *)
  Lemma trace_lookup_dom_neg {St L : Type} (tr : trace St L) (len : nat_omega)
    (LEN: trace_len_is tr len):
    ∀ i, tr !! i = None ↔ NOmega.le len (NOnum i).
  Proof. 
    intros. erewrite <- trace_len_neg; eauto.
    rewrite /lookup /trace_lookup. destruct after; [destruct t| ]; done.
  Qed. 

  (* TODO: move *)
  Lemma traces_match_after' {L1 L2 S1 S2 : Type} (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop) 
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop) 
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat) 
    (tr1' : trace S1 L1):
    traces_match Rℓ Rs trans1 trans2 tr1 tr2
    → after n tr1 = Some tr1'
      → ∃ tr2' : trace S2 L2,
          after n tr2 = Some tr2' ∧ traces_match Rℓ Rs trans1 trans2 tr1' tr2'.
  Proof.
    intros ?%traces_match_flip ?.
    forward eapply traces_match_after as (?&?&?); eauto.
    eexists. split; eauto.
    by apply traces_match_flip.
  Qed. 


  Lemma traces_match_trace_lookup_general {L1 L2 S1 S2: Type}
    (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop) 
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop) 
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat)
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2):
    match tr1 !! n, tr2 !! n with
    | Some step1, Some step2 => 
        Rs (fst step1) (fst step2) /\
          match snd step1, snd step2 with 
          | Some (ℓ1, s1'), Some (ℓ2, s2') => Rℓ ℓ1 ℓ2 /\ Rs s1' s2'
          | None, None => True
          | _, _ => False
          end
    | None, None => True
    | _ , _ => False
    end. 
  Proof. 
    pose proof (trace_has_len tr1) as [len LEN1]. pose proof (trace_has_len tr2) as [? LEN2].
    forward eapply (traces_match_same_length _ _ _ _ tr1 tr2) as X; eauto. subst x.
    destruct (tr1 !! n) as [[s1 step1]| ] eqn:STEP1, (tr2 !! n) as [[s2 step2]| ] eqn:STEP2. 
    4: done. 
    3: { eapply mk_is_Some, trace_lookup_dom in STEP2; eauto. 
         eapply trace_lookup_dom_neg in STEP1; eauto.
         lia_NO len. }
    2: { eapply mk_is_Some, trace_lookup_dom in STEP1; eauto. 
         eapply trace_lookup_dom_neg in STEP2; eauto.
         lia_NO len. }

    (* pose proof (trace_state_lookup_simpl' _ _ _ (@ex_intro _ _ _ STEP1)) as ST1.
     *)
    forward eapply (proj1 (trace_state_lookup_simpl' tr1 n s1)) as ST1; eauto.  
    forward eapply (proj1 (trace_state_lookup_simpl' tr2 n s2)) as ST2; eauto.  
    simpl in *.
    pose proof (proj2 (trace_lookup_after' _ _ _) ST1) as (atr1 & AFTER1 & A1).
    forward eapply traces_match_after' with (tr1 := tr1) (tr2 := tr2); eauto.
    intros (atr2 & AFTER2 & A2). 
    split.
    { apply traces_match_first in A2.
      erewrite state_lookup_after_0 in ST1; eauto. 
      erewrite state_lookup_after_0 in ST2; eauto.
      congruence. }
    destruct step1 as [[ℓ1 s1']| ], step2 as [[ℓ2 s2']| ].
    4: done.
    3: { forward eapply (proj1 (trace_lookup_dom_strong _ _ LEN2 n)); eauto.
         forward eapply (proj1 (trace_lookup_dom_eq _ _ LEN1 n)); eauto.
         lia_NO' len. intros [=]. lia. }
    2: { forward eapply (proj1 (trace_lookup_dom_strong _ _ LEN1 n)); eauto.
         forward eapply (proj1 (trace_lookup_dom_eq _ _ LEN2 n)); eauto.
         lia_NO' len. intros [=]. lia. }
    
    apply trace_lookup_after_strong in STEP1 as (?&AFTER1'&?), STEP2 as (?&AFTER2'&?).
    erewrite AFTER1' in AFTER1. rewrite AFTER2' in AFTER2.
    inversion AFTER1. inversion AFTER2. subst atr1 atr2.
    inversion A2. subst. split; eauto.
    eapply traces_match_first; eauto.
  Qed.     

  Lemma traces_match_state_lookup_1 {L1 L2 S1 S2: Type}
    (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop) 
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop) 
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat) st1
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2)
    (ST1: tr1 S!! n = Some st1):
    exists st2, tr2 S!! n = Some st2 /\ Rs st1 st2.
  Proof. 
    apply trace_state_lookup_simpl' in ST1 as ([s1 ostep1] & NTH1 & <-).
    pose proof (traces_match_trace_lookup_general _ _ _ _ _ _ n MATCH) as STEPS.
    rewrite NTH1 in STEPS.
    destruct (tr2 !! n) as [[s2 ostep2]|] eqn:NTH2; [| done]. simpl in *.
    destruct STEPS. eexists. split; eauto.
    eapply trace_state_lookup_simpl'; eauto.
  Qed. 

  Lemma traces_match_label_lookup_1 {L1 L2 S1 S2: Type}
    (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop) 
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop) 
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat) ℓ1
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2)
    (LBL1: tr1 L!! n = Some ℓ1):
    exists ℓ2, tr2 L!! n = Some ℓ2 /\ Rℓ ℓ1 ℓ2. 
  Proof. 
    apply trace_label_lookup_simpl' in LBL1 as (s & s' & NTH1).
    pose proof (traces_match_trace_lookup_general _ _ _ _ _ _ n MATCH) as STEPS.
    rewrite NTH1 in STEPS.
    destruct (tr2 !! n) as [[s2 ostep2]|] eqn:NTH2; [| done]. simpl in *.
    destruct ostep2 as [[??]|]; [| tauto]. destruct STEPS as (?&?&?). 
    eexists. split; eauto.
    eapply trace_label_lookup_simpl'; eauto.
  Qed.

  (* TODO: move, ? unify definitions of _valid *)
  Lemma auxtrace_valid_steps' `{LM: LiveModel G M} (tr: auxtrace (LM := LM))
    i st ℓ st'
    (VALID: auxtrace_valid tr)
    (ITH: tr !! i = Some (st, Some (ℓ, st'))):
    lm_ls_trans LM st ℓ st'.
  Proof using.
    gd st. gd ℓ. gd st'. gd tr.
    induction i.
    { simpl. intros.
      inversion VALID.
      - subst. done.
      - subst. inversion ITH. by subst. }
    intros. simpl in ITH.
    destruct tr.
    { inversion ITH. }
    rewrite trace_lookup_cons in ITH.
    inversion VALID.  
    eapply IHi; eauto.
  Qed.

  Lemma fuel_must_not_incr_fuels {G M} oρ'
    (δ1 δ2: LiveState G M)
    ρ f1 f2
    (KEEP: fuel_must_not_incr oρ' δ1 δ2)
    (FUEL1: ls_fuel δ1 !! ρ = Some f1)
    (FUEL2: ls_fuel δ2 !! ρ = Some f2)
    (OTHER: oρ' ≠ Some ρ):
    f2 <= f1.
  Proof.
    red in KEEP. specialize (KEEP ρ). specialize_full KEEP.
    { by apply elem_of_dom. }
    destruct KEEP as [LE|[?|KEEP]].
    + rewrite FUEL1 FUEL2 in LE. simpl in LE. lia. 
    + tauto. 
    + apply proj1 in KEEP. destruct KEEP. eapply elem_of_dom; eauto.
  Qed.

  Lemma step_nonincr_fuels `{LM: LiveModel G M} ℓ
    (δ1 δ2: LiveState G M)
    ρ f1 f2
    (STEP: lm_ls_trans LM δ1 ℓ δ2)
    (FUEL1: ls_fuel δ1 !! ρ = Some f1)
    (FUEL2: ls_fuel δ2 !! ρ = Some f2)
    (OTHER: forall g, ℓ ≠ Take_step ρ g):
    f2 <= f1.
  Proof.
    destruct ℓ. 
    all: eapply fuel_must_not_incr_fuels; eauto; [apply STEP|..]; congruence.
  Qed. 
  

  Lemma role_fuel_decreases `{LM: LiveModel G M} (tr: auxtrace (LM := LM)) δ0 ρ f0
    (ST0: tr S!! 0 = Some δ0)
    (FUEL0: ls_fuel δ0 !! ρ = Some f0)
    (NOρ: ∀ i ℓ, tr L!! i = Some ℓ → ∀ g, ℓ ≠ Take_step ρ g)
    (ASGρ: ∀ i δ, tr S!! i = Some δ → ρ ∈ dom (ls_mapping δ))
    (VALID: auxtrace_valid tr):
    forall i δ f, 
      tr S!! i = Some δ -> ls_fuel δ !! ρ = Some f -> f <= f0. 
  Proof.
    induction i; intros δ f ST FUEL. 
    { assert (δ0 = δ) as -> by congruence. 
      assert (f0 = f) as -> by congruence. 
      done. }
    
    pose proof (trace_has_len tr) as [len LEN]. 
    forward eapply (proj2 (trace_lookup_dom_strong _ _ LEN i)).
    { eapply mk_is_Some, state_lookup_dom in ST; eauto. 
      lia_NO len. }
    intros (δ' & ℓ & δ_ & STEP).
    
    forward eapply auxtrace_valid_steps' as TRANS; eauto.
    apply state_label_lookup in STEP as (ST' & ST_ & LBL).
    assert (δ_ = δ) as ->; [| clear ST_].
    { rewrite Nat.add_1_r in ST_. congruence. }
    
    specialize (ASGρ _ _ ST'). rewrite ls_same_doms in ASGρ.
    pose proof ASGρ as ASGρ_.
    apply elem_of_dom in ASGρ as [f' FUEL'].
    specialize (IHi _ _ ST' FUEL').
    etrans; [| apply IHi]. 
    eapply step_nonincr_fuels in TRANS; eauto.
  Qed.

  (* TODO: move *)
  Lemma ls_same_doms' {G M} (δ: LiveState G M):
    forall ρ, is_Some (ls_mapping δ !! ρ) <-> is_Some (ls_fuel δ !! ρ).
  Proof. 
    intros. rewrite -!elem_of_dom. by rewrite ls_same_doms.
  Qed.

  (* TODO: move? try to unify with fair_aux_after *)
  (* TODO: add ∀ in fair_aux_SoU definition  *)
  Lemma fair_aux_SoU_after `{LM: LiveModel G M} ρ (auxtr: auxtrace (LM := LM))
    n auxtr':
    (forall k, fair_aux_SoU auxtr ρ k) ->
    after n auxtr = Some auxtr' ->
    (forall k, fair_aux_SoU auxtr' ρ k).
  Proof.
    rewrite /fair_aux_SoU => Hfair Hafter m Hpa.
    specialize (Hfair (n+m)).
    rewrite -> (pred_at_sum _ n) in Hfair. rewrite Hafter in Hfair.
    destruct (Hfair Hpa) as (p&Hp).
    exists (p).
    (* by rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n), Hafter in Hp. *)
    rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n) in Hp.
    by rewrite Hafter in Hp. 
  Qed.

  (* TODO: move; is there an existing lemma? *)
  Lemma after_S_tr_cons {St L: Type} (tr: trace St L) n s ℓ atr
    (AFTER: after n tr = Some (s -[ℓ]-> atr)):
    after (S n) tr = Some atr.
  Proof.
    by rewrite -Nat.add_1_r after_sum' AFTER.
  Qed.           

  (* TODO: move *)
  Lemma label_lookup_after {St L: Type} (tr atr: trace St L) (a: nat)
    (AFTER: after a tr = Some atr):
    forall k, atr L!! k = tr L!! (a + k).
  Proof. 
    intros. rewrite /label_lookup. 
    rewrite after_sum'. by rewrite AFTER.
  Qed.    

  (* TODO: move *)
  Lemma state_lookup_after {St L: Type} (tr atr: trace St L) (a: nat)
    (AFTER: after a tr = Some atr):
    forall k, atr S!! k = tr S!! (a + k).
  Proof. 
    intros. rewrite /state_lookup. 
    rewrite after_sum'. by rewrite AFTER.
  Qed.

  (* TODO: rename? *)
  Lemma eventual_step_or_unassign lmtr_o mtr_o lmtr_i ρ gi δi f
    (MATCH: lm_model_traces_match mtr_o lmtr_i)
    (CORRo: upto_stutter_auxtr lmtr_o mtr_o (LM := LMo))
    (FAIR_SOU: forall n gi, fair_aux_SoU lmtr_o (lift_Gi gi) n (LM := LMo))
    (INNER_OBLS: inner_obls_exposed lmtr_o)
    (NOρ : ∀ (m : nat) (ℓ : lm_lbl LMi),
          lmtr_i L!! m = Some ℓ → ∀ go' : Gi, ℓ ≠ Take_step ρ go')
  (ASGρ : ∀ (k : nat) (δi_k : lm_ls LMi),
           lmtr_i S!! k = Some δi_k → ls_mapping δi_k !! ρ = Some gi)
  (VALIDi: auxtrace_valid lmtr_i)
  (ST0: lmtr_i S!! 0 = Some δi)
  (FUEL0: ls_fuel δi !! ρ = Some f):
    ∃ m, pred_at lmtr_i m (steps_or_unassigned ρ).
  Proof.
    Local Set Printing Coercions.
    gd lmtr_i. gd δi. gd mtr_o. gd lmtr_o.
    pattern f. apply lt_wf_ind. clear f. intros f IH. intros. 
    pose proof (traces_match_first _ _ _ _ _ _ MATCH) as REL0.
    pose proof (upto_stutter_trfirst _ _ _ _ CORRo) as CORR0. 
    pose proof (ASGρ _ _ ST0) as MAPi. 
    
    pose proof (INNER_OBLS 0 (trfirst lmtr_o) gi) as OBLS0. specialize_full OBLS0.
    { apply state_lookup_0. }
    { do 2 eexists. split; eauto.
      rewrite -CORR0. rewrite state_lookup_0 in ST0. congruence. }
    
    pose proof (FAIR_SOU 0 gi) as FAIR. 
    red in FAIR. specialize_full FAIR.
    { by apply pred_at_trfirst. }
    destruct FAIR as [n_lo STEPlo].
    
    simpl in STEPlo. apply pred_at_trace_lookup' in STEPlo as (δo_n & stepo & STLo & SOUn).
    
    rewrite /steps_or_unassigned in SOUn. destruct SOUn as [UNASG | [go STEP]].
    { forward eapply upto_stutter_state_lookup'; eauto.
      { eapply trace_state_lookup_simpl'; eauto. }
      intros [n_mo STmo]. simpl in STmo.
      forward eapply traces_match_state_lookup_1; [apply MATCH| apply STmo| ].
      intros (δi_n & STlmi & RELn).
      red in INNER_OBLS. specialize_full INNER_OBLS.
      { eapply trace_state_lookup_simpl'. eauto. }
      { eauto. }
      simpl in INNER_OBLS. apply elem_of_dom in INNER_OBLS as [??].
      congruence. }
    
    destruct stepo as [[? δo_n']|]; [| done]. simpl in STEP.
    inversion STEP. subst. clear STEP.
    
    forward eapply upto_stutter_step_correspondence_alt with 
      (Po := fun δ oℓ => δ = δo_n /\ oℓ = Some (Take_step (lift_Gi gi) go))
      (Pi := fun st ooρ => st = ls_under δo_n /\ ooρ = Some $ Some $ lift_Gi gi).
    { by intros ?? [-> ->]. }
    { by intros ?[??]. }
    { apply CORRo. }
    { apply pred_at_trace_lookup'. eauto. } 
    intros (n_mo & STEPmo & UPTO').
    
    (* apply pred_at_trace_lookup in STEPmo as (st_mo & STmo & -> & Lmo). *)
    apply pred_at_trace_lookup' in STEPmo as (? & step_ & STEPmo & -> & LBL).
    destruct step_ as [[ℓ_mo st_mo']|]; simpl in LBL; [| done].
    inversion LBL. subst ℓ_mo. clear LBL.
    pose proof STEPmo as (STmo & Lmo & STmo')%state_label_lookup.
    
    forward eapply traces_match_label_lookup_1; [apply MATCH| ..]; eauto. 
    intros (ℓ_lm & Llmi & LBL_MATCH).
    simpl in LBL_MATCH. destruct LBL_MATCH as (? & LIFT_EQ & MATCHgi).
    apply INJlg in LIFT_EQ. subst x.
    
    apply trace_label_lookup_simpl' in Llmi as (δi_n_mo & δi_n_mo' & STEPlmi).
    assert (forall δ n, lmtr_i S!! n = Some δ -> exists f', ls_fuel δ !! ρ = Some f' /\ f' <= f) as NOFUEL.  
    { intros δ n ST. 
      pose proof (ASGρ _ _ ST) as ASG.
      apply mk_is_Some, ls_same_doms' in ASG as [f' FUEL].
      forward eapply role_fuel_decreases with (i := n); eauto.
      intros ?? ST'. apply ASGρ in ST'. by apply elem_of_dom. }
    
    forward eapply auxtrace_valid_steps' as TRANS; [| apply STEPlmi|]; eauto.
    pose proof STEPlmi as (ST&ST'&LBL)%state_label_lookup. 
    pose proof (NOFUEL _ _ ST) as (f_ & NOFUEL1 & LE_). 
    pose proof (NOFUEL _ _ ST') as (f_' & NOFUEL2 & LE_'). 

    assert (f_' < f -> ∃ m, pred_at lmtr_i m (steps_or_unassigned ρ)) as IH_APP.
    {
      clear -UPTO' STEPmo IH STLo ST' STEPlmi FAIR_SOU INNER_OBLS NOFUEL2 MATCH NOρ ASGρ.
      intros LT. 
      red in UPTO'. destruct UPTO' as (atr_lmo & atr_mo & AFTERlmo & AFTERmo & UPTO').
      apply trace_lookup_after_strong in STEPmo as (atr_mo' & AFTERmo' & HEADmo').
      rewrite AFTERmo in AFTERmo'. inversion AFTERmo'. subst atr_mo. 
      apply trace_lookup_after_strong in STLo as (atr_lo' & AFTERlo' & HEADlo').
      rewrite AFTERlmo in AFTERlo'. inversion AFTERlo'. subst atr_lmo.
      clear AFTERmo' AFTERlo'. 
      
      specialize IH with (m := f_') (lmtr_o := atr_lo') (mtr_o := atr_mo') (δi := δi_n_mo').
      apply trace_lookup_after_strong in STEPlmi as (atr_lmi & AFTERlmi & HEADlmi).
      specialize IH with (lmtr_i := atr_lmi).
      apply after_S_tr_cons in AFTERmo, AFTERlmo, AFTERlmi. 
      specialize_full IH.
      * lia. 
      * intros. eapply fair_aux_SoU_after; eauto.
      * red. intros.
        erewrite state_lookup_after in H; eauto. 
      * punfold UPTO'; [| apply upto_stutter_mono].
        inversion UPTO'; subst; try done.
        inversion H7; eauto. done.
      * done. 
      * eapply traces_match_after' in AFTERmo as (?&A'&?); [| apply MATCH].
        rewrite AFTERlmi in A'. by inversion A'.
      * intros. eapply NOρ.
        rewrite -H. symmetry. eapply label_lookup_after; eauto.
      * intros. eapply ASGρ. 
        rewrite -H. symmetry. eapply state_lookup_after; eauto.
      * (* TODO: admitted somewhere else? *)
        admit.
      * rewrite -ST'.
        rewrite (plus_n_O (_ + _)).
        rewrite -Nat.add_1_r in AFTERlmi. 
        eapply state_lookup_after; eauto.
      * destruct IH as [m PM].
        eexists (S n_mo + m). apply pred_at_sum.
        by rewrite AFTERlmi. }
     
    destruct ℓ_lm as [ρ' g| | ]; subst. 
    3: done. 
    - destruct (decide (ρ' = ρ)). 
      { subst. edestruct NOρ; eauto. }
      simpl in TRANS. destruct TRANS as (_&_&DECR&_).
      red in DECR. specialize (DECR ρ). specialize_full DECR. 
      1, 2: eapply elem_of_dom; eauto.
      { left; [congruence| ]. symmetry. eapply ASGρ; eauto. }
      rewrite NOFUEL1 NOFUEL2 /= in DECR.
      eapply IH_APP; eauto. lia. 
    -
      (* TODO: unify with above? *)
      simpl in TRANS. destruct TRANS as (_&DECR&_).
      red in DECR. specialize (DECR ρ). specialize_full DECR. 
      1, 2: eapply elem_of_dom; eauto.
      { left; [congruence| ]. symmetry. eapply ASGρ; eauto. }
      rewrite NOFUEL1 NOFUEL2 /= in DECR.
      eapply IH_APP; eauto. lia.
  Admitted.         


  (* TODO: is it possible to unify this proof with those in lm_fairness_preservation? *)
  (* TODO: renaming of arguments? *)
  Lemma inner_LM_trace_fair_aux (tr_o: mtrace Mo) (lmtr_i: auxtrace (LM := LMi)):
    infinite_trace tr_o ->
    lm_model_traces_match tr_o lmtr_i ->
    (∀ ρ, fair_model_trace ρ tr_o) -> (forall ρ, fair_aux ρ lmtr_i (LM := LMi)).
  Proof. 
    intros INF MATCH FAIRo ρ.
    destruct (classic (fair_aux ρ lmtr_i)) as [| UNFAIR]; [done| exfalso].

    rewrite /fair_aux in UNFAIR. 
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

    (* TODO: setoid_rewrite stopped working; any conflict with paco? *)
    (* setoid_rewrite pred_at_neg in UNFAIR; [| by apply INF'']. *)
    (* setoid_rewrite pred_at_trace_lookup' in UNFAIR. simpl in UNFAIR. *)
    erewrite forall_proper in UNFAIR.
    2: { intros. rewrite pred_at_or. apply pred_at_neg.
         by apply INF''. }
    simpl in UNFAIR. 
    setoid_rewrite pred_at_trace_lookup' in UNFAIR. 

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
