From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len.
From trillium.fairness.lawyer.obligations Require Import obligations_model.


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
  Proof using. clear PO. red. intros ??????. multiset_solver. Qed. 

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
      
  (* Global Instance ms_le_PreOrder: PreOrder ms_le. *)
  (* Proof using. *)
  (*   split. *)
  (*   - red. intros ??. lia. *)
  (*   - red. intros X Y Z LE1 LE2. *)

  (*     red. red in LE1, LE2. intros.   *)
      
  (*     apply ms_le_equiv'. *)
  (*     apply ms_le_equiv' in LE1, LE2. red in LE1, LE2. *)
  (*     destruct LE1 as (B1 & S1 & ?& -> &?).  *)
  (*     destruct LE2 as (B2 & S2 & ?& -> &?). *)

  (*     apply gmultiset_disj_union_difference in H3. *)
  (*     remember (Z ∖ B2) as KK. clear HeqKK.  *)
  (*     rewrite H3. clear H3 Z.   *)
  (*     apply gmultiset_disj_union_difference in H1. *)
  (*     rewrite H1. clear H1. *)
  (*     red. do 2 eexists. repeat split. *)
  (*     2: { replace ((B1 ⊎ (KK ⊎ S2) ∖ B1) ∖ B1) with ((KK ⊎ S2) ∖ B1) by multiset_solver. *)            

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

  Definition mset_filter (P : A → Prop)
    `{∀ x, Decision (P x)}
    (g: gmultiset A): gmultiset A.
  Admitted. 

End MultisetDefs.


Definition maximal {A C : Type} {H : ElemOf A C} (R : relation A) (x : A) (X : C) :=
  minimal (flip R) x X.



Section Termination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.


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
        (2 * LIM_STEPS * last_expect sid - k) *: {[+ ((* π,  *)d) +]}
      ).

    Definition PF' (k: nat) (δ: ProgressState OP) :=
      (mset_map snd ∘ (ps_cps OP)) δ ⊎
      (* ([^op set] ('(s, (π, d)) ∈ (∅: gset ExpectPermission)), ∅).  *)
        approx_expects k (ps_eps OP δ). 

    Definition PF (i: nat): gmultiset Degree :=
      from_option (PF' (LIM_STEPS * i)) ∅ (tr S!! i). 

    Context (deg_le: relation Degree).

    (* TODO: move *)
    Lemma scalar_mul_le `{Countable K} (s: gmultiset K) m n
      (LE: m <= n):
      m *: s ⊆ n *: s.
    Proof using.
      clear -LE. 
      apply Nat.le_sum in LE as [d ->]. multiset_solver.
    Qed.

    (* Lemma approx_expects_next k eps: *)
    (*   approx_expects k eps = ∅ \/ *)
    (*   let add := [^op set] ep ∈ eps, let '(sid, π, d) := ep in {[+ ((* π,  *)d) +]} in *)
    (*   approx_expects k eps = approx_expects (S k) eps ⊎ add. *)
    (* Proof using. *)
    (*   rewrite /approx_expects.  *)


    Lemma ms_le_decr_expr k eps:
      ms_le deg_le (approx_expects (S k) eps) (approx_expects k eps).
    Proof using. 
      rewrite /approx_expects.
      eapply big_opS_ms_le. intros [[??]?].
      apply ms_le_sub.
      apply scalar_mul_le. lia.
    Qed.

    Lemma approx_expects_add k eps e 
      (FRESH: e ∉ eps):
      let n := (2 * LIM_STEPS * last_expect (fst $ fst e) - k) in
      approx_expects k (eps ∪ {[ e ]}) = approx_expects k eps ⊎ n *: {[+ e.2 +]}.
    Proof using.
      rewrite (union_comm_L _ {[ e ]}).
      rewrite /approx_expects.
      rewrite -leibniz_equiv_iff. 
      rewrite big_opS_insert; auto.
      rewrite gmultiset_op gmultiset_disj_union_comm. f_equiv.
      destruct e as [[??]?]. done.
    Qed. 

    Lemma loc_step_decr δ1 τ δ2 k
      (STEP: loc_step OP δ1 τ δ2)
      (EXP_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                  let n := 2 * LIM_STEPS * last_expect sid in
                  k < n):
      ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
    Proof using.
      rewrite /PF'. 
      destruct STEP as [T|[T|[T|[T|[T|T]]]]].
      - destruct T as (?&?&T). inversion T; subst.
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_decr_expr.
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
        + apply ms_le_decr_expr.
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_decr_expr.
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.  
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_decr_expr.
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
          + apply ms_le_decr_expr. }
        forward eapply (approx_expects_add (S k)) as ->; eauto. simpl.
        rewrite (gmultiset_disj_union_comm _ ((_ - _) *: _)) gmultiset_disj_union_assoc.
        apply ms_le_disj_union.
        + apply ms_le_exchange.
          * admit.
          * eapply elem_of_mset_map. eexists (_, _). eauto.
          * admit.
        + apply ms_le_decr_expr.
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
        { apply ms_le_decr_expr. }
        move EXP_BOUND at bottom. specialize_full EXP_BOUND; [by eauto| ].
        eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
        rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.  
    Admitted. 
        
 
    Lemma step_decr i
      (VALID: obls_trace_valid OP tr):
      ms_lt deg_le (PF (S i)) (PF i).
    Proof using.
      rewrite /PF. simpl.
      pose proof (trace_has_len tr) as [len LEN]. 
      destruct (tr S!! S i) as [m'| ] eqn:ITH'.
      2: { rewrite ITH'. simpl. rewrite big_opS_empty.
           rewrite gmultiset_disj_union_right_id.
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

      red in STEP. 
    
   
  End NoInfExpects.

  Lemma obls_fair_trace_terminate (tr: obls_trace OP):
    obls_trace_valid OP tr ->
    (∀ τ, obls_trace_fair OP τ tr) ->
    terminating_trace tr.
  Proof using.
    
  Admitted. 


End Termination.

