From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len.
From trillium.fairness.lawyer.obligations Require Import obligations_model.
From stdpp Require Import relations.

Ltac mss := multiset_solver. 

(* TODO: move *)
Section GmultisetUtils.
  Context `{Countable A}. 
  
  Lemma gmultiset_difference_exact (X Y: gmultiset A):
    X ∖ Y = X ∖ (X ∩ Y). 
  Proof using. clear. mss. Qed. 
  
  Lemma gmultiset_difference_twice (X Y Z: gmultiset A):
    X ∖ Y ∖ Z = X ∖ (Y ⊎ Z). 
  Proof using. clear. mss. Qed.
  
  Lemma gmultiset_cancel_l1 (X Y: gmultiset A):
    (X ⊎ Y) ∖ Y = X. 
  Proof using. clear. mss. Qed.
  
  Lemma gmultiset_cancel_l2 (X Y: gmultiset A):
    (X ⊎ Y) ∖ X = Y. 
  Proof using. clear. mss. Qed.
  
  Lemma gmultiset_difference_disjoint (X Y: gmultiset A)
    (DISJ: X ## Y):
    X ∖ Y = X.
  Proof using. clear -DISJ. mss. Qed. 
  
  Lemma gmultiset_split (X Y: gmultiset A):
    exists I X' Y', X = X' ⊎ I /\ Y = Y' ⊎ I /\ X' ## Y'.
  Proof using.
    set (I := X ∩ Y).
    exists I, (X ∖ I), (Y ∖ I). repeat split.
    1, 2: rewrite gmultiset_disj_union_comm; apply gmultiset_disj_union_difference; mss.
    mss. 
  Qed.

End GmultisetUtils.

Section MultisetOrder.
  Context `{Countable A}.
  Context (R: relation A).
  Context (PO: PartialOrder R).   

  (* reflexive version of Huet and Oppen definition *)
  Definition ms_le (X Y: gmultiset A) :=
    forall a, multiplicity a X > multiplicity a Y ->
    exists b, R a b /\ multiplicity b X < multiplicity b Y.

  Definition ms_lt := strict ms_le. 
  
  (* original Huet and Oppen definition *)
  Definition ms_lt' (X Y: gmultiset A) :=
    forall a, multiplicity a X > multiplicity a Y ->
    exists b, strict R a b /\ multiplicity b X < multiplicity b Y.

  Definition ms_le_dm (M N: gmultiset A) :=
    exists X Y, X ⊆ N /\ M = (N ∖ X) ⊎ Y /\ (forall y, y ∈ Y -> exists x, x ∈ X /\ strict R y x). 

  Lemma ms_le_equiv X Y:
    ms_le X Y <-> (ms_lt' X Y \/ X = Y).
  Proof using PO.
    rewrite /ms_le /ms_lt'. split.
    - intros LE.
      destruct (decide (X = Y)) as [-> | ?]; [tauto| ].
      left. intros a GTa.
      specialize (LE _ GTa). destruct LE as (b & Rab & LEb).
      destruct (decide (a = b)).
      { subst. lia. }
      exists b. split; [| done]. 
      split; auto. intros ?. edestruct PO; eauto.
    - intros [LT | ->].
      2: { lia. }
      intros a GTa.
      specialize (LT _ GTa). destruct LT as (b & Rab & LTb).
      eexists. repeat split; eauto. apply Rab.
  Qed.

  Lemma empty_ms_le X: ms_le ∅ X.
  Proof using.
    red. intros ?. rewrite multiplicity_empty. lia.
  Qed.

  (* TODO: generalize, move *)
  Lemma multiset_difference_empty (X: gmultiset A):
    X ∖ ∅ = X. 
  Proof using. clear R PO. multiset_solver. Qed. 

  Lemma ms_le_sub X Y (SUB: X ⊆ Y):
    ms_le X Y. 
  Proof using.
    clear PO. 
    red. multiset_solver. 
  Qed.

  (* TODO: should be a part of PartialOrder proof *)
  Lemma ms_le_refl X:
    ms_le X X.
  Proof using.
  Admitted. 
    

  Lemma ms_le_diff X Y:
    ms_le (X ∖ Y) X.
  Proof using.
    red. intros ?. rewrite multiplicity_difference. lia.
  Qed.

  Notation "'mlt' x X" := (multiplicity x X) (at level 20).
  (* Context `{∀ x y, Decision (R x y)}.  *)

  Lemma ms_le_equiv'    
    X Y:
    ms_le X Y <-> ms_le_dm X Y.
  Proof using.
  (*   rewrite /ms_le /ms_le_dm. split. *)
  (*   - rename X into M, Y into N. *)
  (*     (* intros LE. *) *)
  (*     (* set (M__max :=  *) *)
  (*     destruct (decide (M = ∅)) as [-> | NE]. *)
  (*     { intros. exists N, ∅. multiset_solver. }  *)
      
  (*     assert (exists m, m ∈ M /\ maximal R m M). *)
  (*     { enough (exists m, m ∈ (dom M) /\ maximal R m (dom M)). *)
  (*       2: { unshelve eapply minimal_exists_L; try by apply _. *)
  (*            intros E. destruct NE. admit. } *)
  (*       destruct H1 as (m & DOM & MAX). *)
  (*       exists m. split. *)
  (*       { eapply gmultiset_elem_of_dom; eauto. } *)
  (*       red. red. simpl. intros. apply MAX; eauto. *)
  (*       eapply gmultiset_elem_of_dom; eauto. } *)

  (*     destruct H1 as (m & Mm & MAXm).  *)
  (*     intros LE.       *)

      
  (*     exists ((mset_filter (fun a => R m a) N) ∖ M), ((mset_filter (fun a => ¬ R m a) M) ∖ N). *)
  (*     repeat split. *)
  (*     + admit. *)
  (*     + apply gmultiset_eq. intros a. *)
  (*       destruct (decide (R m a)). *)
  (*       * rewrite multiplicity_disj_union. *)
          
      
             
  (*            apply gmultiset_eq. intros. rewrite multiplicity_empty. *)
  (*            destruct (multiplicity x M) eqn:FF; [done| ]. *)
             
  (*            intros ?%dom_empty_L.  *)
  (*       - apply _.  *)

      
  (*     generalize dependent N. pattern M. apply gmultiset_ind. *)
  (*     { intros. exists N, ∅. multiset_solver. } *)
  (*     clear M. intros m M IH N' LE. *)

  (*     assert (exists n, n ∈ N' /\ R m n) as (n & N'n & Rmn). *)
  (*     { admit. } *)

  (*     pose proof (gmultiset_disj_union_difference' _ _ N'n) as EQ. *)
  (*     rewrite EQ. rewrite EQ in LE.  *)
  (*     remember (N' ∖ {[+ n +]}) as N. clear HeqN. clear N' N'n EQ. *)

  (*     setoid_rewrite multiplicity_disj_union in LE. *)
  (*     setoid_rewrite multiplicity_singleton' in LE.  *)

      
      
  (*     specialize (IH N). destruct IH. *)
  (*     { intros. *)
  (*       specialize (LE a). *)
        
  (*       destruct (decide (a = n)). *)
  (*       { subst. *)
  (*         rewrite decide_False in LE; [| admit]. *)
  (*         simpl in LE.  *)
        
  (*       destruct (decide (a = n)). *)
  (*       { specialize (LE term+) *)

  (*         subst. *)

  (*         lia.  *)
      
      
  (*     destruct (decide (m ∈ N)). *)
  (*     2: { specialize (IH N). destruct IH. *)
  (*          { intros. specialize (LE a). destruct LE as (b & ab & LT).  *)
  (*            { rewrite multiplicity_disj_union. lia. } *)
  (*            rewrite multiplicity_disj_union in LT. *)
  (*            rewrite multiplicity_singleton' in LT.  *)
  (*            eexists. split; eauto.  *)
             
      
  (*     specialize (IH (N ∖ {[+ m +]})). *)
  (*     destruct IH.  *)
  (*     { intros a GT.  *)
  (*       destruct (decide *)
  (*     intros LE.  *)
  Admitted.

  Lemma ms_le_disj_union X1 Y1 X2 Y2
    (LE1: ms_le X1 Y1) (LE2: ms_le X2 Y2):
    ms_le (X1 ⊎ X2) (Y1 ⊎ Y2).
  Proof using.
    clear PO. 
    apply ms_le_equiv'. apply ms_le_equiv' in LE1, LE2. red in LE1, LE2.
    destruct LE1 as (B1 & S1 & IN1 & -> & LT1), LE2 as (B2 & S2 & IN2 & -> & LT2).
    red. exists (B1 ⊎ B2), (S1 ⊎ S2). repeat split.
    - multiset_solver.
    - multiset_solver.
    - intros ? [I1 | I2]%gmultiset_elem_of_disj_union.
      + destruct (LT1 _ I1) as (b1 & INB1 & R1). multiset_solver.
      + destruct (LT2 _ I2) as (b2 & INB2 & R2). multiset_solver.
  Qed. 
  
  Global Instance ms_le_Proper:
     Proper (equiv ==> equiv ==> iff) ms_le.
  Proof using. clear PO. red. intros ??????. mss. Qed. 

  Global Instance ms_lt_Proper:
     Proper (equiv ==> equiv ==> iff) ms_lt.
  Proof using. clear PO. red. intros ??????. mss. Qed. 

  Lemma big_opS_ms_le `{Countable B} f g (X: gset B)
    (LE: forall x, ms_le (f x) (g x)):
    ms_le ([^op set] x ∈ X, f x) ([^op set] x ∈ X, g x).
  Proof using.
    pattern X. apply set_ind_L; clear X.
    { rewrite !big_opS_empty. apply empty_ms_le. }
    intros. rewrite !big_opS_insert; auto. simpl. rewrite !gmultiset_op.
    apply ms_le_disj_union; eauto.
  Qed. 

  Lemma ms_le_exchange X u v n 
    (INu: u ∈ X)
    (LTuv: strict R v u):
    ms_le (X ∖ {[+ u +]} ⊎ n *: {[+ v +]}) X.
  Proof using PO.
    apply gmultiset_disj_union_difference' in INu.
    remember (X ∖ {[+ u +]}) as V.
    rewrite gmultiset_disj_union_comm in INu. 
    rewrite INu. clear INu HeqV X.
    eapply ms_le_disj_union; [apply ms_le_refl| ..].
    red. intros ?. rewrite multiplicity_scalar_mul !multiplicity_singleton'.
    destruct (decide (a = v)) as [->|?]; [| lia].
    intros. eexists. split; [apply LTuv| ].
    rewrite multiplicity_scalar_mul !multiplicity_singleton'.
    rewrite decide_False.
    2: { intros ->. apply LTuv. done. }
    rewrite decide_True; [lia| done].
  Qed.  
      
  Global Instance ms_le_PreOrder: PreOrder ms_le.
  Proof using. Admitted.

  Global Instance ms_le_AntiSymm: AntiSymm eq ms_le.
  Proof using.
    red. intros ?? LE1 LE2.
    red in LE1, LE2. apply gmultiset_eq. intros a.
    (* TODO: consider the maximal element with differing multiplicity *)
    (* destruct (Nat.lt_trichotomy (multiplicity a x) (multiplicity a y)) as [?|[?|?]]; eauto. *)
    (* - specialize (LE2 _ H0). *)
  Admitted.

  Goal PartialOrder ms_le.
    esplit; apply _.
  Defined. 

End MultisetOrder.



Section MultisetDefs.
  Context `{Countable A}.

  Section MultisetMap.
    Context `{Countable B}. 
    Context (f: A -> B). 

    Definition mset_map (g: gmultiset A): gmultiset B :=
      list_to_set_disj $ fmap f $ elements g.

    Lemma elem_of_mset_map (g: gmultiset A):
      forall b, b ∈ mset_map g <-> exists a, f a = b /\ a ∈ g.
    Proof using.
      intros. rewrite /mset_map.
      rewrite elem_of_list_to_set_disj.
      rewrite elem_of_list_fmap.
      apply exist_proper. intros ?. apply ZifyClasses.and_morph; [done| ].
      apply gmultiset_elem_of_elements.
    Qed. 
  
    Lemma mset_map_empty:
      mset_map ∅ = ∅. 
    Proof using. mss. Qed. 
  
    Lemma mset_map_disj_union (X Y: gmultiset A):
      mset_map (X ⊎ Y) = mset_map X ⊎ mset_map Y.
    Proof using.
      apply gmultiset_eq. intros.
      rewrite /mset_map. rewrite -list_to_set_disj_app -fmap_app.       
      f_equal. apply list_to_set_disj_perm. f_equiv. 
      apply gmultiset_elements_disj_union.
    Qed.

    Lemma mset_map_sub (X Y: gmultiset A)
      (SUB: X ⊆ Y):
      mset_map X ⊆ mset_map Y.
    Proof using.
      apply gmultiset_disj_union_difference in SUB. rewrite SUB.
      rewrite mset_map_disj_union. mss.
    Qed. 

    (* Lemma mset_map_diff_1 (X: gmultiset A) (r: A): *)
    (*   mset_map (X ∖ {[+ r +]}) = mset_map X ∖ {[+ f r +]}.  *)
    (* Proof using. *)
      

    Lemma mset_map_sub_diff (X Y: gmultiset A)
      (SUB: Y ⊆ X):
      mset_map (X ∖ Y) = mset_map X ∖ mset_map Y.
    Proof using.
      apply gmultiset_disj_union_difference in SUB.
      rewrite SUB. remember (X ∖ Y) as V. clear HeqV SUB.
      rewrite mset_map_disj_union. 
      rewrite !gmultiset_cancel_l2. mss. 
    Qed. 
      
    (*   rewrite /mset_map.  *)
      
    (*   rewrite gmultiset_difference_exact. *)
    (*   forward eapply (gmultiset_disj_union_difference (X ∩ Y) X); [mss| ]. *)
    (*   intros EQ. *)
    (*   remember (X ∖ (X ∩ Y)) as V. rewrite EQ.  *)
      
    (*   rewrite /mset_map.  *)
    (* Admitted. *)

    Lemma mset_map_singleton (x: A):
      mset_map {[+ x +]} = {[+ f x +]}.
    Proof using.
      rewrite /mset_map. rewrite gmultiset_elements_singleton.
      rewrite list_fmap_singleton. mss.
    Qed. 

    Lemma mset_map_mul (X: gmultiset A) (n: nat):
      mset_map (n *: X) = n *: (mset_map X). 
    Proof using.
      induction n.
      { rewrite !gmultiset_scalar_mul_0. mss. }
      rewrite !gmultiset_scalar_mul_S_r. rewrite mset_map_disj_union. 
      by rewrite IHn.
    Qed. 

    (* Lemma ms_le_map (R: relation B) X Y: *)
    (*   ms_le R (mset_map X) (mset_map Y) <-> ms_le (fun a1 a2 => R (f a1) (f a2)) X Y. *)
    (* Proof using. *)
    (*   rewrite /ms_le. *)
    (*   split. *)
    (*   - intros. specialize (H1 (f a)). specialize_full H1. *)
    (*     {  *)

  End MultisetMap.

  Section MultisetFilter.
    Context (P : A → Prop). 
    Context `{∀ x, Decision (P x)}. 

    Definition mset_filter (g: gmultiset A): gmultiset A :=
      list_to_set_disj $ filter P $ elements g. 

    Lemma mset_filter_spec g:
      forall a, a ∈ mset_filter g <-> a ∈ g /\ P a.
    Proof using.
      intros. rewrite /mset_filter.
      rewrite elem_of_list_to_set_disj elem_of_list_filter.
      rewrite gmultiset_elem_of_elements. tauto.
    Qed.

    Lemma mset_filter_empty:
      mset_filter ∅ = ∅. 
    Proof using. mss. Qed.

    Lemma mset_filter_disj_union x y:
      mset_filter (x ⊎ y) = mset_filter x ⊎ mset_filter y.
    Proof using.
      rewrite /mset_filter.
      rewrite -list_to_set_disj_app. rewrite -filter_app. 
      apply list_to_set_disj_perm. apply filter_Permutation.
      apply gmultiset_elements_disj_union.
    Qed.

    Lemma mset_filter_False g
      (FALSE: forall a, a ∈ g -> ¬ P a):
      mset_filter g = ∅.
    Proof using.
      destruct (decide (mset_filter g = ∅)) as [| NE]; [done| ]. 
      apply gmultiset_choose in NE as [? IN].
      apply mset_filter_spec in IN as [??]. set_solver.
    Qed. 

    Lemma mset_filter_singleton a:
      mset_filter {[+ a +]} = if (decide (P a)) then {[+ a +]} else ∅.
    Proof using.
      rewrite /mset_filter. rewrite gmultiset_elements_singleton.
      rewrite filter_cons !filter_nil.
      destruct decide; mss.
    Qed. 

    Lemma mset_filter_multiplicity g (a: A):
      multiplicity a (mset_filter g) =
      if (decide (P a)) then multiplicity a g else 0.
    Proof using. 
      revert a. pattern g. apply gmultiset_ind; clear g. 
      { intros ?. rewrite mset_filter_empty multiplicity_empty.
        destruct decide; auto. }
      intros x g IH a.
      rewrite mset_filter_disj_union mset_filter_singleton.
      rewrite !multiplicity_disj_union. rewrite multiplicity_singleton'. 
      rewrite IH. 
      destruct (decide (P x)), (decide (P a)); try rewrite multiplicity_singleton'.
      - lia.
      - rewrite decide_False; [| by intros ->]. lia.
      - rewrite decide_False; [| by intros ->].
        rewrite multiplicity_empty. lia.
      - rewrite multiplicity_empty. lia.
    Qed.

    Lemma mset_filter_subseteq_mono:
      Proper (subseteq ==> subseteq) mset_filter.
    Proof using.
      red. intros ????.
      rewrite !mset_filter_multiplicity.
      destruct decide; mss.
    Qed. 

    Lemma mset_filter_difference x y:
      mset_filter (x ∖ y) = mset_filter x ∖ mset_filter y.
    Proof using.
      apply gmultiset_eq. intros a.
      rewrite !multiplicity_difference !mset_filter_multiplicity !multiplicity_difference.
      destruct decide; mss. 
    Qed.

    Lemma mset_filter_mul_comm g n:
      mset_filter (n *: g) = n *: mset_filter g.
    Proof using.
      apply gmultiset_eq. intros ?.
      rewrite multiplicity_scalar_mul.
      rewrite !mset_filter_multiplicity.
      destruct decide; try mss. 
      by rewrite multiplicity_scalar_mul.
    Qed. 

  End MultisetFilter.
  
End MultisetDefs.


Definition maximal {A C : Type} {H : ElemOf A C} (R : relation A) (x : A) (X : C) :=
  minimal (flip R) x X.

Section Termination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.

  Section WfSetMin.

    Definition minimal_in_prop {A: Type} (R : relation A) (x : A) (P : A -> Prop) :=
      ∀ y : A, P y → R y x → R x y. 

    Context `{R: relation A}.
    Hypothesis (SIG_WF: wf R).

    Theorem sets_have_min (P: A -> Prop)
      (NE: exists a, P a):
      exists a, P a /\ minimal_in_prop R a P. 
    Proof. Admitted. 

  End WfSetMin.


  Section SignalsEventuallySet.
    Context (tr: obls_trace OP).

    Context (sig_le: relation Level).
    Hypothesis (SIG_WF: wf (strict sig_le)).

    Context (lvl__def: Level). 

    Definition lvl_at (sid_i: SignalId * nat): Level :=
      let '(sid, i) := sid_i in
      from_option (fun δ => from_option fst lvl__def (ps_sigs _ δ !! sid)) lvl__def (tr S!! i).

    Require Import Coq.Program.Wf.
    
    Definition tr_sig_lt: relation (SignalId * nat) := MR (strict sig_le) lvl_at. 

(*     wf (MR R m) *)
(* measure_wf *)

    Lemma tr_sig_lt_wf: wf tr_sig_lt.
    Proof using SIG_WF. apply measure_wf. apply SIG_WF. Qed.

    Definition never_set_after sid c := 
      forall i, c <= i -> from_option (fun δ => from_option snd true (ps_sigs _ δ !! sid)) true (tr S!! i) = false. 

    Context {set_before: SignalId -> nat}.

    Definition approx_expects (k: nat) (eps: gset (@ExpectPermission Degree)) :=
      ([^op set] ep ∈ eps, let '(sid, π, d) := ep in
        (2 * (LIM_STEPS + 2) * set_before sid - k) *: {[+ d +]}
      ).

    Instance cmp_phase'_dec: forall (x y: Phase * Degree),
        Decision (phase_le x.1 y.1).
    Proof using.
      intros [??] [??]. simpl.
      rewrite /phase_le. solve_decision.
    Qed. 

    Local Instance cmp_phase'_dec' π0:
      ∀ x : Phase * Degree, Decision ((λ '(π, _), phase_le π π0) x). 
    Proof using.
      intros [??]. simpl.
      rewrite /phase_le. solve_decision.
    Qed.

    Local Instance cmp_phase'_dec'' π0:
    ∀ x : SignalId * Phase * Degree, Decision ((λ '(_, π, _), phase_le π π0) x).
    Proof using.
      intros [[??]?]. rewrite /phase_le. solve_decision.
    Qed. 

    Let π0 := namespaces.nroot. 
    Definition PF (π: Phase) (k: nat) (δ: ProgressState OP) :=
      (mset_map snd ∘ (mset_filter (fun '(π_, _) => phase_le π_ π)) ∘ (ps_cps OP)) δ
        ⊎
      approx_expects k (filter (fun '(_, π_, _) => phase_le π_ π) (ps_eps OP δ)). 

    Definition TPF (π: Phase) (i: nat): gmultiset Degree :=
      from_option (PF π ((LIM_STEPS + 2) * i)) ∅ (tr S!! i).

    Context (deg_le: relation Degree).

    (* TODO: move *)
    Lemma scalar_mul_le `{Countable K} (s: gmultiset K) m n
      (LE: m <= n):
      m *: s ⊆ n *: s.
    Proof using.
      clear -LE. 
      apply Nat.le_sum in LE as [d ->]. multiset_solver.
    Qed.

    Lemma ms_le_exp_le m n eps
      (LE: m <= n):
      ms_le deg_le (approx_expects n eps) (approx_expects m eps).
    Proof using. 
      rewrite /approx_expects.
      eapply big_opS_ms_le. intros [[??]?].
      apply ms_le_sub.
      apply scalar_mul_le. lia.
    Qed.

    Lemma approx_expects_add k eps e 
      (FRESH: e ∉ eps):
      let n := (2 * (LIM_STEPS + 2) * set_before (fst $ fst e) - k) in
      approx_expects k (eps ∪ {[ e ]}) = approx_expects k eps ⊎ n *: {[+ e.2 +]}.
    Proof using.
      rewrite (union_comm_L _ {[ e ]}).
      rewrite /approx_expects.
      rewrite -leibniz_equiv_iff. 
      rewrite big_opS_insert; auto.
      rewrite gmultiset_op gmultiset_disj_union_comm. f_equiv.
      destruct e as [[??]?]. done.
    Qed.

    (* TODO: move *)
    Lemma gset_singleton_if_equiv `{Countable K} (P: K -> Prop)
      `{forall k, Decision (P k)}:
      forall k, filter P ({[ k ]}: gset K) = if (decide (P k)) then {[ k ]} else ∅.
    Proof using.
      clear -EqDecision1. 
      intros. destruct decide; set_solver.
    Qed.

    Definition phases_incompat π1 π2 := ¬ phase_le π1 π2 /\ ¬ phase_le π2 π1. 

    (* Definition loc_step_no_exp sid δ1 τ δ2 := *)
    (*   loc_step OP δ1 τ δ2 /\ (forall π d, ¬ expects_ep OP δ1 τ δ2 sid π d). *)

    Definition loc_step_no_exp_all δ1 τ δ2 :=
      (exists π δ, burns_cp OP δ1 τ δ2 π δ) \/
      (exists π δ δ' n, exchanges_cp OP δ1 τ δ2 π δ δ' n) \/
      (exists l, creates_signal OP δ1 τ δ2 l) \/
      (exists s, sets_signal OP δ1 τ δ2 s) \/
      (exists s π δ δ', creates_ep OP δ1 τ δ2 s π δ δ').

    Lemma loc_step_split δ1 τ δ2:
      loc_step OP δ1 τ δ2 <->
      (loc_step_no_exp_all δ1 τ δ2 \/ (exists sid π d, expects_ep OP δ1 τ δ2 sid π d)).
    Proof using.
      clear set_before. 
      rewrite /loc_step_no_exp_all. split.
      - intros [T|[T|[T|[T|[T|T]]]]]; tauto.
      - intros [[T|[T|[T|[T|T]]]] | ?]; red; tauto.
    Qed. 
      
    Lemma loc_step_no_exp_all_ms_le π__ow δ1 τ δ2 k
      (STEP: loc_step_no_exp_all δ1 τ δ2)
      (* (OTHER: *)
      (*   let π := default π0 (ps_phases _ δ1 !! τ) in *)
      (*   phases_incompat π__ow π) *)
      :
      ms_le deg_le (PF π__ow (S k) δ2) (PF π__ow k δ1).
    Proof using.
      rewrite /PF.
      destruct STEP as [T|[T|[T|[T|T]]]]. 
      - destruct T as (?&?&T). inversion T; subst. 
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. apply mset_filter_subseteq_mono. mss.
        + apply ms_le_exp_le. lia.
      - destruct T as (?&?&?&?&T). inversion T; subst. 
        destruct δ1. simpl in *. 
        apply ms_le_disj_union.
        + subst new_cps0.
          rewrite !mset_filter_disj_union mset_map_disj_union.
          rewrite !mset_filter_difference. 
          rewrite !mset_filter_mul_comm.
          rewrite !mset_filter_singleton. 
          destruct decide.
          2: { rewrite decide_False; [| tauto].
               rewrite multiset_difference_empty gmultiset_scalar_mul_empty.
               rewrite mset_map_empty.
               eapply ms_le_Proper; [reflexivity | | reflexivity].
               mss. }
          rewrite decide_True; [| tauto].
          rewrite mset_map_sub_diff. 
          2: { apply gmultiset_singleton_subseteq_l.
               by apply mset_filter_spec. }
          rewrite mset_map_mul !mset_map_singleton. simpl.
          apply ms_le_exchange.
          * admit.
          * eapply elem_of_mset_map. eexists (_, _). split; eauto.
            apply mset_filter_spec. split; eauto. 
          * admit.          
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.  
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&?&?&?&T). inversion T; subst.
        destruct δ1. simpl in *.
        subst new_cps0 new_eps0.
        
        rewrite !mset_filter_difference. 
        rewrite !mset_filter_singleton.        
        rewrite filter_union_L.
        destruct decide.
        2: { rewrite filter_singleton_not_L; [| tauto].
             rewrite multiset_difference_empty. rewrite union_empty_r_L.
             apply ms_le_disj_union.
             + apply ms_le_sub. reflexivity. 
             + apply ms_le_exp_le. lia. }

        rewrite filter_singleton_L; [| tauto]. 

        rewrite mset_map_sub_diff. 
        2: { apply gmultiset_singleton_subseteq_l.
             by apply mset_filter_spec. }
        rewrite mset_map_singleton. simpl.

        destruct (decide ((x, x0, x2) ∈ ps_eps)).
        { rewrite union_comm_L subseteq_union_1_L; [| set_solver].
          apply ms_le_disj_union.
          + apply ms_le_sub. mss. 
          + apply ms_le_exp_le. lia. }
        
        forward eapply (approx_expects_add (S k)) as ->.
        { by intros [??]%elem_of_filter. } 
        rewrite (gmultiset_disj_union_comm _ ((_ - _) *: _)) gmultiset_disj_union_assoc. 
        apply ms_le_disj_union; revgoals. 
        + apply ms_le_exp_le. lia. 
        + simpl. apply ms_le_exchange.
          * admit.
          * eapply elem_of_mset_map. eexists (_, _). split; eauto.
            apply mset_filter_spec. split; eauto. 
          * admit.
    Admitted. 


    Lemma other_loc_step_ms_le π__ow δ1 τ δ2 k
      (STEP: loc_step OP δ1 τ δ2)
      (OTHER:
        let π := default π0 (ps_phases _ δ1 !! τ) in
        phases_incompat π__ow π):
      ms_le deg_le (PF π__ow (S k) δ2) (PF π__ow k δ1).
    Proof using.
      clear sig_le SIG_WF. 
      rewrite /PF.
      apply loc_step_split in STEP as [NOEXP | EXP].
      { eapply loc_step_no_exp_all_ms_le; eauto. }
      destruct EXP as (?&?&?&T). inversion T; subst.
      destruct δ1. simpl in *.
      subst new_cps0.
      
      rewrite !mset_filter_disj_union mset_map_disj_union.
      rewrite !mset_filter_singleton.
      rewrite decide_False.
      2: { rewrite LOC_PHASE in OTHER. simpl in OTHER.
           red in OTHER. tauto. }
      
      rewrite mset_map_empty. apply ms_le_disj_union.
      + eapply ms_le_Proper; [reflexivity| | reflexivity]. mss.
      + apply ms_le_exp_le. lia. 
    Qed.

    (* TODO: rename never_set_after *)
      
    Lemma min_owner_loc_step_ms_le δ1 τ δ2 k (* s l *)
      (STEP: loc_step OP δ1 τ δ2)
      (SET_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                  let n := 2 * (LIM_STEPS + 2) * set_before sid in
                  k < n)
      :
      let π__ow := default π0 (ps_phases _ δ1 !! τ) in
      ms_le deg_le (PF π__ow (S k) δ2) (PF π__ow k δ1).
    Proof using.
      clear sig_le SIG_WF. 
      rewrite /PF.
      apply loc_step_split in STEP as [NOEXP | EXP].
      { eapply loc_step_no_exp_all_ms_le; eauto. }

      destruct EXP as (?&?&?&T). inversion T; subst.
      destruct δ1. simpl in *.
      subst new_cps0. rewrite LOC_PHASE. simpl. 
      
      rewrite !mset_filter_disj_union mset_map_disj_union.
      rewrite !mset_filter_singleton.
      rewrite decide_True; [| reflexivity]. rewrite mset_map_singleton. simpl. 

      (* rewrite mset_map_disj_union. *)
      rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union.
      { apply ms_le_refl. }
      rewrite (union_difference_singleton_L _ _ EP).
      
      rewrite filter_union_L.
      rewrite !gset_singleton_if_equiv.
      rewrite decide_True; [| tauto].
      
      rewrite (union_comm_L {[ _ ]} _).
      rewrite !approx_expects_add.
      2, 3: set_solver.
      simpl. rewrite gmultiset_disj_union_comm.
      rewrite -gmultiset_disj_union_assoc.
      apply ms_le_disj_union.
      { apply ms_le_exp_le. lia. }

      move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
      eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
      rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
    Qed.

    Hypothesis (SET_BEFORE_SPEC: 
                 forall sid i,
                   (forall c, ¬ never_set_after sid c) ->
                   set_before sid <= i ->
                   from_option (fun δ => from_option snd false (ps_sigs _ δ !! sid)) false (tr S!! i) = true).

    (* TODO: move *)
    Lemma strict_not_both {A: Type} (R: relation A) x y:
      strict R x y -> strict R y x -> False.
    Proof using.      
      clear. intros [??] [??]. done.
    Qed.

    Lemma tr_loc_step_nsteps_ms_le δ i τ δ' s k
      (ITH: tr S!! i = Some δ)
      (BOUND : k ≤ LIM_STEPS)

      (NEVER_SET : never_set_after s i)
      (MIN: minimal_in_prop tr_sig_lt (s, i)
          (λ ab : SignalId * nat, never_set_after ab.1 ab.2))

      (OWNER: s ∈ default ∅ (ps_obls _ δ !! τ))

      (STEPS: nsteps (λ p1 p2, loc_step OP p1 τ p2) k δ δ'):
      let π__ow := default π0 (ps_phases _ δ !! τ) in
      ms_le deg_le (PF π__ow (2 * (LIM_STEPS + 2) * i + k) δ') (PF π__ow (2 * (LIM_STEPS + 2) * i) δ).
    Proof using.
      generalize dependent δ'.
      induction k.
      { intros ? ->%obls_utils.nsteps_0.
        rewrite Nat.add_0_r. reflexivity. }
      intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
      specialize (IHk ltac:(lia) _ STEPS).
      etrans; eauto.

      (* follows from well-formedness of state *)
      assert (ps_phases OP δ !! τ = Some π__ow) as PH by admit. rewrite PH. simpl. 
      (* follows from preservation of phases before fork *)
      assert (ps_phases OP δ' !! τ = Some π__ow) as PH' by admit. 
      
      eapply ms_le_Proper; [| | eapply min_owner_loc_step_ms_le]; eauto.
      { rewrite PH'.
        rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
      { rewrite PH'. simpl. reflexivity. }

      intros sid π d EXP. simpl.
      inversion EXP. subst.
      rewrite PH' in LOC_PHASE. inversion LOC_PHASE. subst π__max.
      red in OBLS_LT. red in OBLS_LT.

      move NEVER_SET at bottom. red in NEVER_SET.
      specialize (NEVER_SET _ ltac:(reflexivity)).
      rewrite ITH in NEVER_SET. simpl in NEVER_SET. 
      destruct (ps_sigs OP δ !! s) as [[ls ?]|] eqn:SIG__min; [| done].
      simpl in NEVER_SET. subst. 
      
      assert (ps_sigs _ δ' !! s = Some (ls, false)) as SIG' by admit.
      assert (s ∈ default ∅ (ps_obls _ δ' !! τ)) as OBL' by admit.
      specialize (OBLS_LT ls). specialize_full OBLS_LT.
      { apply extract_Somes_gset_spec.
        destruct (ps_obls OP δ' !! τ) as [obs| ] eqn:OBLS'; [| set_solver].
        simpl in OBL'. simpl. apply elem_of_map. eexists. split; eauto.
        rewrite SIG'. done. }
      assert (strict sig_le l ls) as SIG_LT by admit. clear OBLS_LT.

      enough (set_before sid > i).
      { apply PeanoNat.Nat.le_succ_l in H0. 
        apply Nat.le_sum in H0 as [u EQ]. rewrite EQ. lia. }
      red. destruct (Nat.lt_ge_cases i (set_before sid)) as [?|GE]; [done| ].   

      (* either it was there when the big step started,
         or it's a new signal, but then the thread holds an obligation
         and cannot wait on it *)
      assert (ps_sigs OP δ !! sid = Some (l, false)) as SIG0 by admit.

      pose proof (SET_BEFORE_SPEC sid i). specialize_full H0; [| done| ].
      2: { rewrite ITH in H0. simpl in H0.
           rewrite SIG0 in H0. done. }

      intros c NEVER_SET_.
      assert (never_set_after sid i) as NEVER_SET' by admit. clear NEVER_SET_.
      move MIN at bottom. red in MIN. specialize (MIN (_, _) NEVER_SET').
      rewrite /tr_sig_lt /MR in MIN. simpl in MIN.
      rewrite ITH in MIN. simpl in MIN. rewrite SIG0 SIG__min in MIN. simpl in MIN.
      specialize (MIN SIG_LT).
      edestruct @strict_not_both; eauto. 
    Admitted.

    Theorem signals_eventually_set:
      ¬ exists sid c, never_set_after sid c. 
    Proof using.
      intros EX. apply ex_prod' in EX.
      eapply sets_have_min in EX; [| apply tr_sig_lt_wf].
      apply ex_prod in EX. simpl in EX. destruct EX as (s & c & UNSET & MIN).
      assert (τ__def: Locale) by admit.
      set (s_ow (i: nat) :=
             let owners := 
               dom $ filter (fun '(_, obls) => s ∈ obls)
               (from_option (ps_obls OP) ∅ (tr S!! i)) in
             default τ__def (gset_pick owners)
          ).

      set (OTF i := LTF (s_ow i) i).

      enough (exists d, c <= d /\ OTF d = ∅) as (d & LE & EMP). 
      { 
      

      

      

  End SignalsEventuallySet.


  Section NoInfExpects.
    Context (tr: obls_trace OP).
    Context {last_expect: SignalId -> nat}.
    Hypothesis (LAST_EXP_SPEC: 
                 forall sid δ1 δ2 τ k π d,
                   tr !! k = Some (δ1, Some (τ, δ2)) ->
                   expects_ep OP δ1 τ δ2 sid π d -> 
                   k <= last_expect sid).

    (* Definition PF (i: nat): gmultiset (@CallPermission Degree) := *)
    (*   from_option (ps_cps OP) ∅ (tr S!! i) ⊎ *)
    (*   (* ([^op set] ('(s, (π, d)) ∈ (∅: gset ExpectPermission)), ∅).  *) *)
    (*   ([^op set] ep ∈ (∅: gset (@ExpectPermission Degree)), *)
    (*     let '(sid, π, d) := ep in  *)
    (*     (last_expect sid - i) *: {[+ (π, d) +]} *)
    (*   ). *)

    Definition approx_expects (k: nat) (eps: gset (@ExpectPermission Degree)) :=
      ([^op set] ep ∈ eps, let '(sid, π, d) := ep in
        (2 * (LIM_STEPS + 2) * last_expect sid - k) *: {[+ ((* π,  *)d) +]}
      ).

    Definition PF' (k: nat) (δ: ProgressState OP) :=
      (mset_map snd ∘ (ps_cps OP)) δ ⊎
      (* ([^op set] ('(s, (π, d)) ∈ (∅: gset ExpectPermission)), ∅).  *)
        approx_expects k (ps_eps OP δ). 

    Definition PF (i: nat): gmultiset Degree :=
      from_option (PF' ((LIM_STEPS + 2) * i)) ∅ (tr S!! i). 

    Context (deg_le: relation Degree).

    (* Lemma approx_expects_next k eps: *)
    (*   approx_expects k eps = ∅ \/ *)
    (*   let add := [^op set] ep ∈ eps, let '(sid, π, d) := ep in {[+ ((* π,  *)d) +]} in *)
    (*   approx_expects k eps = approx_expects (S k) eps ⊎ add. *)
    (* Proof using. *)
    (*   rewrite /approx_expects.  *)

    (* Lemma approx_expects_le_sub m n eps *)
    (*   (LE: m <= n): *)
    (*   approx_expects n eps ⊆ approx_expects m eps. *)
    (* Proof using.  *)
    (*   rewrite /approx_expects. *)
    (*   setoid_rewrite elem_of_subseteq.  *)
    


    Lemma ms_le_exp_le m n eps
      (LE: m <= n):
      ms_le deg_le (approx_expects n eps) (approx_expects m eps).
    Proof using. 
      rewrite /approx_expects.
      eapply big_opS_ms_le. intros [[??]?].
      apply ms_le_sub.
      apply scalar_mul_le. lia.
    Qed.

    Lemma ms_le_PF_le m n δ
      (LE: m <= n):
      ms_le deg_le (PF' n δ) (PF' m δ).
    Proof using.
      rewrite /PF'. 
      apply ms_le_disj_union.
      + reflexivity.
      + apply ms_le_exp_le. lia.
    Qed. 

    Lemma approx_expects_add k eps e 
      (FRESH: e ∉ eps):
      let n := (2 * (LIM_STEPS + 2) * last_expect (fst $ fst e) - k) in
      approx_expects k (eps ∪ {[ e ]}) = approx_expects k eps ⊎ n *: {[+ e.2 +]}.
    Proof using.
      rewrite (union_comm_L _ {[ e ]}).
      rewrite /approx_expects.
      rewrite -leibniz_equiv_iff. 
      rewrite big_opS_insert; auto.
      rewrite gmultiset_op gmultiset_disj_union_comm. f_equiv.
      destruct e as [[??]?]. done.
    Qed. 

    Lemma burns_cp_ms_lt δ1 τ δ2 π d k
      (STEP: burns_cp OP δ1 τ δ2 π d):
      ms_lt deg_le (PF' (S k) δ2) (PF' k δ1).
    Proof using.
      rewrite /PF'. 
      inversion STEP; subst.
      destruct δ1. simpl in *.
      apply strict_spec_alt. 
      split. 
      - apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_le. lia.
      - rewrite mset_map_sub_diff. 
        2: { by apply gmultiset_singleton_subseteq_l. }
        assert (approx_expects (S k) ps_eps ⊆ approx_expects k ps_eps) by admit.
        rewrite mset_map_singleton. simpl.
        apply gmultiset_disj_union_difference' in CP. rewrite CP.
        rewrite mset_map_disj_union. rewrite mset_map_singleton. simpl.
        rewrite gmultiset_cancel_l2. mss.
    Admitted.       

    Lemma loc_step_decr δ1 τ δ2 k
      (STEP: loc_step OP δ1 τ δ2)
      (EXP_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                  let n := 2 * (LIM_STEPS + 2) * last_expect sid in
                  k < n):
      ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
    Proof using.
      rewrite /PF'. 
      destruct STEP as [T|[T|[T|[T|[T|T]]]]].
      - apply strict_include.
        destruct T as (?&?&T). eapply burns_cp_ms_lt; eauto.  
      - destruct T as (?&?&?&?&T). inversion T; subst. 
        destruct δ1. simpl in *. 
        apply ms_le_disj_union.
        + subst new_cps0. rewrite mset_map_disj_union.
          rewrite mset_map_sub_diff. 
          2: { by apply gmultiset_singleton_subseteq_l. }
          rewrite mset_map_mul !mset_map_singleton. simpl.
          apply ms_le_exchange.
          * admit.
          * eapply elem_of_mset_map. eexists (_, _). eauto.
          * admit.          
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.  
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&?&?&?&T). inversion T; subst.
        destruct δ1. simpl in *.
        subst new_cps0 new_eps0. 
        rewrite mset_map_sub_diff. 
        2: { by apply gmultiset_singleton_subseteq_l. }
        rewrite mset_map_singleton. simpl.

        destruct (decide ((x, x0, x2) ∈ ps_eps)).
        { rewrite union_comm_L subseteq_union_1_L; [| set_solver].
          apply ms_le_disj_union.
          + apply ms_le_sub. mss. 
          + apply ms_le_exp_le. lia. }
        forward eapply (approx_expects_add (S k)) as ->; eauto. simpl.
        rewrite (gmultiset_disj_union_comm _ ((_ - _) *: _)) gmultiset_disj_union_assoc.
        apply ms_le_disj_union.
        + apply ms_le_exchange.
          * admit.
          * eapply elem_of_mset_map. eexists (_, _). eauto.
          * admit.
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&?&?&T). inversion T; subst.
        destruct δ1. simpl in *.
        subst new_cps0. rewrite mset_map_disj_union.
        rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union.
        { apply ms_le_refl. }
        rewrite mset_map_singleton. simpl.
        rewrite (union_difference_singleton_L _ _ EP).
        rewrite (union_comm_L {[ _ ]} _). rewrite !approx_expects_add.
        2, 3: set_solver.
        simpl. rewrite gmultiset_disj_union_comm.
        rewrite -gmultiset_disj_union_assoc.
        apply ms_le_disj_union.
        { apply ms_le_exp_le. lia. }
        move EXP_BOUND at bottom. specialize_full EXP_BOUND; [by eauto| ].
        eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
        rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.  
    Admitted.

    Lemma forks_locale_ms_le δ1 τ δ2 τ' R k
      (FORK: forks_locale OP δ1 τ δ2 τ' R):
      ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
    Proof using.
      rewrite /PF'.
      inversion FORK; subst. 
      destruct δ1. simpl in *.
      apply ms_le_disj_union.
      + apply ms_le_sub. apply mset_map_sub. mss. 
      + apply ms_le_exp_le. lia.
    Qed.      

    Lemma loc_step_has_exp sid δ1 τ δ2
      (STEP: loc_step OP δ1 τ δ2)
      (NO_NOEXP: ¬ loc_step_no_exp sid δ1 τ δ2):
      exists π d, expects_ep OP δ1 τ δ2 sid π d.
    Proof using.
      rewrite /loc_step_no_exp in NO_NOEXP.
      apply Classical_Prop.not_and_or in NO_NOEXP as [? | EXP]; [tauto| ].
      apply not_forall_exists_not in EXP as [? EXP].
      apply not_forall_exists_not in EXP as [? EXP].
      apply NNP_P in EXP. eauto.
    Qed.

    From trillium.fairness.lawyer.obligations Require Import obls_utils.
    Notation " x ;;; y " := (rel_compose x y) (at level 20).

    Definition rep_no_exp n sid ps1 (θ: Locale) ps2 :=
      relations.nsteps (fun p1 p2 => loc_step_no_exp sid p1 θ p2) n ps1 ps2. 

    Definition progress_step_no_exp sid ps1 (θ: Locale) ps2 :=
    exists n, n <= LIM_STEPS /\
           ((* relations.nsteps (fun p1 p2 => loc_step_no_exp sid p1 θ p2) n *)
             (fun p1 p2 => rep_no_exp n sid p1 θ p2)
             ;;;
            (fun p1 p2 => exists π δ, burns_cp OP p1 θ p2 π δ)
           )
            ps1 ps2.

    Lemma progres_step_has_exp sid ps1 (θ: Locale) ps2
      (STEP: progress_step OP ps1 θ ps2)
      (NO_NOEXP: ¬ progress_step_no_exp sid ps1 (θ: Locale) ps2):
      False.
    Proof using.
      red in STEP. destruct STEP as (n & BOUND & (δ' & PSTEP & BSTEP)).
      assert (¬ rep_no_exp n sid ps1 (θ: Locale) δ').
      { intros ?. apply NO_NOEXP. red. eexists. split; eauto.
        destruct BSTEP as (?&?&?). 
        eexists. split; eauto. }

      clear -PSTEP H0. 

      

    Lemma tr_loc_step_nsteps_ms_le δ i τ δ' k
      (ITH: tr S!! i = Some δ)
      (BOUND : k ≤ LIM_STEPS)
      (STEPS: nsteps (λ p1 p2, loc_step OP p1 τ p2) k δ δ'):
  ms_le deg_le (PF' ((LIM_STEPS + 2) * i + k) δ') (PF' ((LIM_STEPS + 2) * i) δ).
    Proof using.
      generalize dependent δ'.
      induction k.
      { intros ? ->%obls_utils.nsteps_0.
        rewrite Nat.add_0_r. reflexivity. }
      intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
      specialize (IHk ltac:(lia) _ STEPS).
      etrans; eauto.
      eapply ms_le_Proper; [| reflexivity| eapply locx_step_decr]; eauto.
      { f_equiv. apply leibniz_equiv_iff. lia. }
      minimal


    Lemma step_decr i
      (VALID: obls_trace_valid OP tr):
      ms_lt deg_le (PF (S i)) (PF i).
    Proof using.
      rewrite /PF. simpl.
      pose proof (trace_has_len tr) as [len LEN]. 
      destruct (tr S!! S i) as [m'| ] eqn:ITH'.
      2: { rewrite ITH'. simpl. 
           (* apply empty_ms_le. *)
           (* TODO: exclude this case *)
           admit. 
      }
      forward eapply state_lookup_prev; [eauto| ..].
      { apply Nat.le_succ_diag_r. }
      intros [m ITH]. rewrite ITH ITH'. simpl.
      pose proof (trace_has_len tr) as [??]. 
      forward eapply (proj2 (label_lookup_dom tr _ _ _)).
      { apply mk_is_Some in ITH'.
        eapply state_lookup_dom in ITH'; eauto.
        rewrite Nat.add_1_r. apply ITH'. }
      intros [τ ITHl].
      forward eapply trace_valid_steps''; eauto.
      { rewrite Nat.add_1_r. eauto. }
      Unshelve. 2: done.
      intros STEP. simpl in STEP.

      red in STEP. destruct STEP as (mf & PSTEP & FSTEP).
      eapply (strict_transitive_r _ (PF' ((LIM_STEPS + 2) * i + (LIM_STEPS + 1)) mf)).
      { inversion FSTEP.
        2: { subst mf.
             rewrite /PF'. apply ms_le_disj_union.
             - reflexivity.
             - apply ms_le_exp_le. lia. }
        destruct H1 as (?&?&?). 
        subst y. eapply ms_le_Proper; [| reflexivity| eapply forks_locale_ms_le; eauto].
        f_equiv. apply leibniz_equiv_iff. lia. }
      clear FSTEP.

      red in PSTEP. destruct PSTEP as (k & BOUND & (mb & PSTEP & BSTEP)).
      eapply (strict_transitive_l _ (PF' ((LIM_STEPS + 2) * i + LIM_STEPS) mb)).
      { destruct BSTEP as (?&?&?).
        eapply ms_lt_Proper; [| reflexivity| eapply burns_cp_ms_lt; eauto].
        f_equiv. apply leibniz_equiv_iff. lia. }
      clear BSTEP.

      etrans.
      { eapply ms_le_PF_le with (m := (LIM_STEPS + 2) * i + k). lia. }
      clear dependent 
      
    
   
  End NoInfExpects.

  Lemma obls_fair_trace_terminate (tr: obls_trace OP):
    obls_trace_valid OP tr ->
    (∀ τ, obls_trace_fair OP τ tr) ->
    terminating_trace tr.
  Proof using.
    
  Admitted. 


End Termination.

