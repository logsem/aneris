(* From iris.proofmode Require Import tactics. *)
From trillium.fairness Require Import fairness fair_termination.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
Require Import stdpp.decidable.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
Import derived_laws_later.bi.
From trillium.fairness Require Import lemmas trace_len trace_lookup trace_helpers utils.
From trillium.fairness.ext_models Require Import set_map_properties ext_models.
From trillium.fairness.examples.ticketlock Require Import fair_lock.

    

(* TODO: inherited from hahn? *)
Close Scope Z_scope. 


Section Model.

  Let tl_role := nat. 

  (* TODO: how to make Inductive and Record section-local? *)
  Inductive tl_role_stage := 
  | tl_L
  | tl_U (t: nat)
  .

  Let tl_role_st: Set := tl_role_stage * bool. 

  Let tl_role_map := gmap tl_role tl_role_st. 

  Record tl_st := mkTlSt {
                      owner: nat;
                      ticket: nat;
                      role_map: tl_role_map;
                    }. 

  Definition tl_state_wf
    '(mkTlSt o t rm) :=
    (* (o t: nat) (rm: tl_role_map) := *)
    o <= t /\
    (forall k, o <= k < t <-> exists ρ e, rm !! ρ = Some (tl_U k, e)) /\
    (forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o) /\
    (forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
       (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2).
    
  Notation "<{ o , t , rm }>" := (mkTlSt o t rm).

  #[global] Instance tl_role_eqdec: EqDecision tl_role.
  Proof using. solve_decision. Qed. 

  #[global] Instance tl_role_stage_eqdec: EqDecision tl_role_stage. 
  Proof using. solve_decision. Qed. 
  
  #[global] Instance tl_role_st_eqdec: EqDecision tl_role_st. 
  Proof using. solve_decision. Qed. 

  #[global] Instance tl_st_eqdec: EqDecision tl_st. 
  Proof using.
    solve_decision.
  Qed. 

  (* Definition tl_st_wf := { st | tl_state_wf st}. *)
    
  Lemma role_of_dec (rm: tl_role_map) (s: tl_role_st):
    {r | rm !! r = Some s} + (forall r, rm !! r ≠ Some s). 
  Proof using.
    pose proof (map_eq_dec_empty (filter (fun '(_, s') => s = s') rm)).
    destruct H as [NIN | IN].
    { right. intros r IN. 
      eapply map_filter_empty_not_lookup in NIN; eauto. }
    left. apply choice; eauto.
    { intros. solve_decision. }
    apply map_choose in IN. destruct IN as (r & s' & IN).
    apply map_filter_lookup_Some in IN. destruct IN as [IN <-]. eauto.
  Qed.  

  Let advance_next (st: tl_st) := 
        match role_of_dec (role_map st) (tl_U (owner st), true) with
        | inl (exist _ r _) => 
            let rm' := <[r := (tl_U (owner st), false)]> (role_map st) in
            mkTlSt (owner st) (ticket st) rm'
        | inr NO => st
        end.

  Inductive tl_trans: tl_st -> option tl_role -> tl_st -> Prop :=
  | tl_take_ticket o t rm r (R: rm !! r = Some (tl_L, true)):
    let next_en := if decide (o = t) then false else true in
    tl_trans <{o, t, rm}> (Some r) <{o, t + 1, <[r := (tl_U t, next_en)]> rm}>
  | tl_spin (o t k: nat) rm r (LT: o ≠ k) (R: rm !! r = Some (tl_U k, true)):
    tl_trans <{o, t, rm}> (Some r) <{o, t, rm}>
  | tl_unlock o t rm r (R: rm !! r = Some (tl_U o, true)):
    let st' := <{o + 1, t, <[r := (tl_L, false)]> rm}> in
    let st'' := advance_next st' in
    tl_trans <{o, t, rm}> (Some r) st''
  .

  Definition tl_live_roles (st: tl_st): gset tl_role :=
    dom (filter (fun '(r, (_, e)) => e = true) (role_map st)).

  Lemma live_spec_holds:
    forall s ρ s', tl_trans s (Some ρ) s' -> ρ ∈ tl_live_roles s.
  Proof.
    intros s ρ s' TRANS. rewrite /tl_live_roles.
    inversion TRANS; subst; simpl. 
    all: eapply elem_of_dom_2; apply map_filter_lookup_Some_2; done.
  Qed.

  #[global] Instance tlSt_inhabited: Inhabited tl_st. 
  Proof. exact (populate (mkTlSt 0 0 ∅)). Qed.

  Definition tl_fair_model: FairModel.
  Proof.
    refine({|
              fmstate := tl_st;
              fmrole := tl_role;
              fmtrans := tl_trans;
              live_roles := tl_live_roles;
              fm_live_spec := live_spec_holds;
            |}).
  Defined.

  
  Definition can_lock_st (ρ: tl_role) (st: tl_st) :=
    exists e, (role_map st) !! ρ = Some (tl_L, e). 

  Definition has_lock_st (ρ: tl_role) (st: tl_st) :=
    (exists e, (role_map st) !! ρ = Some (tl_U (owner st), e)).    

  Definition active_st (ρ: tl_role) (st: tl_st) :=
    exists r, (role_map st) !! ρ = Some (r, true).

  Lemma active_st_enabled (ρ: tl_role) (st: tl_st):
    active_st ρ st <-> @role_enabled_model tl_fair_model ρ st.
  Proof using.
    destruct st as [o t rm].
    rewrite /active_st /role_enabled_model. split.
    - intros [r RMρ]. destruct r.
      + eapply fm_live_spec. apply tl_take_ticket. eauto.
      + destruct (decide (o = t0)); eapply fm_live_spec. 
        * eapply tl_unlock; eauto. rewrite RMρ. congruence.
        * eapply tl_spin; eauto.
    - intros LIVE. simpl in LIVE. rewrite /tl_live_roles in LIVE.
      apply elem_of_dom in LIVE as [r LIVE]. eauto.
      apply map_filter_lookup_Some in LIVE as [? ?].
      destruct r. subst. eauto.      
  Qed. 

  Lemma active_st_dec (ρ: tl_role) (st: tl_st):
    Decision (active_st ρ st).
  Proof using. 
    rewrite /active_st.
    destruct (role_map st !! ρ).
    2: { right. intros (? & ?). congruence. }
    destruct p. destruct b.
    2: { right. intros (? & ?). congruence. }
    left. eexists. eauto.
  Qed. 
    

  Definition tl_init_st (n: nat): tl_st :=
    let rm := gset_to_gmap (tl_L, true) (set_seq 0 n) in
    <{ 0, 0, rm }>.

  Definition tl_is_init_st (st: tl_st) := 
    exists n, st = tl_init_st n. 


  Section TlExtTrans.

    Inductive allows_unlock : tl_st -> tl_st -> Prop :=
    | allows_unlock_step o t ρ rm (LOCK: rm !! ρ = Some (tl_U o, false)):
      allows_unlock (mkTlSt o t rm) (mkTlSt o t (<[ρ := (tl_U o, true)]> rm))
    .

    Inductive allows_lock ρ : tl_st -> tl_st -> Prop :=
    | allows_lock_step t o rm (LOCK: rm !! ρ = Some (tl_L, false)):
      allows_lock ρ (mkTlSt o t rm) (mkTlSt o t (<[ρ := (tl_L, true)]> rm))
    .

    Definition allow_unlock_impl '(mkTlSt o t rm) :=
      let unlockers := dom (filter (fun '(_, v) => v = (tl_U o, false)) rm) in
      let oρ := nth_error (elements unlockers) 0 in
      let rm' := match oρ with
                 | Some ρ => (<[ρ := (tl_U o, true)]> rm) 
                 | None => rm
                 end in
      mkTlSt o t rm'. 

    Definition allow_lock_impl ρ '(mkTlSt o t rm) := 
      mkTlSt o t (<[ρ := (tl_L, true)]> rm). 

    (* TODO: move*)
    Lemma lookup_empty_dom:
  ∀ {K : Type} {M : Type → Type} {D : Type} {H : ∀ A : Type, Dom (M A) D} 
    {H0 : FMap M} {H1 : ∀ A : Type, Lookup K A (M A)} 
    {H2 : ∀ A : Type, Empty (M A)} {H3 : ∀ A : Type, PartialAlter K A (M A)} 
    {H4 : OMap M} {H5 : Merge M} {H6 : ∀ A : Type, FinMapToList K A (M A)} 
    {EqDecision0 : EqDecision K} {H7 : ElemOf K D} {H8 : Empty D} 
    {H9 : Singleton K D} {H10 : Union D} {H11 : Intersection D} 
    {H12 : Difference D} `{FinMapDom K M D},
  ∀ {A : Type} (m : M A),
      m = ∅ <-> forall k, m !! k = None.
    Proof.
      intros. destruct (decide (m = ∅)).
      { subst. setoid_rewrite lookup_empty. done. }
      trans False; [tauto| ]. split; [done| ]. intros ALL. 
      apply map_choose in n as (?&?&n). by rewrite ALL in n.
    Qed.


    Lemma allows_unlock_impl_spec st (WF: tl_state_wf st):
      forall st', allows_unlock st st' <-> 
              (allow_unlock_impl st = st' /\ (exists ρ, has_lock_st ρ st /\ ¬ active_st ρ st)).
    Proof.
      destruct st as [o t rm]. intros [o' t' rm']. 
      erewrite exist_proper with (Q := fun ρ => rm !! ρ = Some (tl_U o, false)).
      2: { intros ρ. rewrite /has_lock_st /active_st. simpl.
           destruct (rm !! ρ).
           2: { split; [by intros [[? [=]] ?]| by intros [=]]. }
           simpl. split; [intros [[? [=]] ?]| intros [=]]; subst.
           - destruct x; auto. edestruct H1; eauto.
           - split; eauto. by intros [? [=]]. }
      red in WF. repeat apply proj2 in WF. 
      simpl. destruct (decide (dom (filter (λ '(_, v), v = (tl_U o, false)) rm) = ∅)).
      { apply dom_empty_inv_L in e.
        pose proof (proj1 (lookup_empty_dom _) e) as NO. 
        (* apply filter_empty_not_elem_of_L in e.  *)
        rewrite e. rewrite dom_empty_L elements_empty.
        trans False; split; try done.
        - intros AU. inversion AU. subst.
          specialize (NO ρ).
          apply map_filter_lookup_None_1 in NO. destruct NO.
          { by rewrite LOCK in H. }
          eapply H; eauto.
        - intros [_ [ρ SOME]]. specialize (NO ρ).
          apply map_filter_lookup_None_1 in NO. destruct NO.
          { by rewrite H in SOME. }
          eapply H; eauto. }
      apply set_choose_L in n as [ρ IN].
      destruct elements eqn:ELTS.
      { apply elements_empty_inv, leibniz_equiv_iff in ELTS.
        set_solver. }
      assert (t0 = ρ) as ->.
      { assert (t0 ∈ t0 :: l) as IN' by set_solver.
        rewrite -ELTS in IN'. apply elem_of_elements in IN'.
        apply elem_of_dom in IN as [? IN], IN' as [? IN'].
        apply map_filter_lookup_Some in IN as [??], IN' as [??].
        subst. eapply WF; eauto. }
      rewrite iff_and_impl_helper.
      2: { intros _.
           apply elem_of_dom in IN as [? IN].
           apply map_filter_lookup_Some in IN as [? ->]. eauto. }
      simpl. split.
      - intros AU. inversion AU. subst. f_equal; try done.
        apply elem_of_dom in IN as [? IN].
        apply map_filter_lookup_Some in IN as [? ->]. 
        eapply (WF ρ ρ0) in LOCK as ->; eauto.
      - intros EQ. inversion EQ. subst. econstructor.
        apply elem_of_dom in IN as [? IN].
        apply map_filter_lookup_Some in IN as [? ->].
        eauto.
    Qed.

    Lemma allows_lock_impl_spec ρ st
                                :
      forall st', allows_lock ρ st st' <-> 
              (allow_lock_impl ρ st = st' /\ (can_lock_st ρ st /\ ¬ active_st ρ st)).
    Proof.
      destruct st as [o t rm]. intros [o' t' rm'].
      rewrite /allow_lock_impl /can_lock_st /active_st. simpl.  
      destruct (rm !! ρ) as [[s e] |] eqn:R.
      2: { simpl. trans False; [| set_solver].
           apply neg_false. intros AL. inversion AL. subst.
           congruence. }
      split.
      - intros AL. inversion AL. subst.
        rewrite R in LOCK. inversion LOCK. subst. repeat split; eauto.
        by intros [??].
      - intros ([=]&[?[=]]&?). subst. econstructor.
        rewrite R. repeat f_equal.
        destruct x; [| done]. edestruct H6; eauto.
    Qed. 
      
    Instance allows_lock_ex_dec:
      forall st ρ, Decision (∃ st', allows_lock ρ st st'). 
    Proof using.
      intros [o t rm] ρ.
      destruct (decide (rm !! ρ = Some (tl_L, false))).
      - left. eexists. econstructor; eauto.
      - right. intros [st' L]. inversion L. congruence. 
    Qed.

    Lemma allows_unlock_ex_dec: 
      forall st, Decision (∃ st', allows_unlock st st'). 
    Proof using. 
      intros [o t rm]. 
      destruct (role_of_dec rm (tl_U o, false)) as [[r LOCK] | FREE].
      - left. eexists. econstructor. eauto.
      - right. intros [st' TRANS]. inversion TRANS. subst.
        set_solver.
    Qed. 
 

    Definition tl_active_exts st: gset fl_EI := 
      (if (allows_unlock_ex_dec st) then {[ flU ]} else ∅) ∪
      set_map (flL (M := tl_fair_model)) 
          (filter (fun ρ => exists st', allows_lock ρ st st') (dom (role_map st))).
    
    Lemma tl_active_exts_spec st ι:
      ι ∈ tl_active_exts st <-> ∃ st', @fl_ETs tl_fair_model allows_unlock allows_lock ι st st'.
    Proof using. 
      unfold tl_active_exts.
      etransitivity; [apply elem_of_union| ].
      destruct ι; simpl in *.
      - etransitivity; [| etransitivity]; [| eapply or_False |].
        { eapply Morphisms_Prop.or_iff_morphism; set_solver. }
        destruct (allows_unlock_ex_dec st).
        2: { split; [set_solver| ]. intros [st' UNL]. 
             destruct n. exists st'. congruence. }
        destruct e as [st' UNL]. etransitivity; [apply elem_of_singleton| ].
        split; auto. intros _. eauto.
      - etransitivity; [| etransitivity]; [| eapply False_or |].
        { eapply Morphisms_Prop.or_iff_morphism; destruct (allows_unlock_ex_dec st); set_solver. }
        rewrite -elem_of_map_inj_gset.
        2: { red. intros. congruence. }
        rewrite elem_of_filter.
        rewrite iff_and_impl_helper; [done| ].
        intros [? [?]]. simpl. by apply elem_of_dom.
    Qed. 

    (* Instance ExtTL: ExtModel tl_fair_model :=  *)
    (*   Build_ExtModel tl_fair_model _ _ _ _ _ tl_active_exts_spec. *)

    Instance ExtTL: ExtModel tl_fair_model := 
      @FL_EM tl_fair_model _ _ _ tl_active_exts_spec. 
    
  End TlExtTrans.
 
  Section ProgressProperties.

    Let ExtTL_FM := @ext_model_FM _ ExtTL. 

    Lemma tl_init_st_wf n:
      tl_state_wf (tl_init_st n). 
    Proof using. 
      rewrite /tl_init_st. 
      red. split; [lia| ]. split; [| split]. 
      - split; [lia| ]. intros [ρ [? RMρ]].
        apply lookup_gset_to_gmap_Some in RMρ as [_ ?]. congruence.
      - intros. rewrite lookup_gset_to_gmap_Some in H.
        by destruct H. 
      - intros. rewrite lookup_gset_to_gmap_Some in R1. 
        by destruct R1.
    Qed. 

    Section ProgressPropertiesImpl.

      Context (tr: mtrace ExtTL_FM).
      Hypothesis (VALID: mtrace_valid tr).
      (* Hypothesis (FROM_INIT: forall st (INIT: tr S!! 0 = Some st), *)
      (*             exists n, st = tl_init_st n).  *)
      Hypothesis (FROM_INIT: forall st (INIT: tr S!! 0 = Some st),
                     tl_state_wf st). 
      Hypothesis (FAIR: set_fair_model_trace (fun (ρ: fmrole ExtTL_FM) => 
                                                exists r, ρ = inl r) tr).

      Local Ltac gd t := generalize dependent t.
      
      Lemma lock_compete_kept (ρ: tl_role):
        @label_kept_state ExtTL_FM 
          (fun st => role_map st !! ρ = Some (tl_L, true)) (inl ρ).
      Proof using. 
        red. intros.
        inversion STEP; subst.
        - assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; auto. 
          all: try by rewrite lookup_insert_ne; auto.
          subst st''. rewrite /advance_next. 
          destruct (role_of_dec _ _); simpl.
          2: { rewrite lookup_insert_ne; auto. }
          destruct s; simpl.
          rewrite lookup_insert_ne.
          { rewrite lookup_insert_ne; auto. }
          intros ->. subst st'0 st'1. simpl in *. 
          rewrite lookup_insert_ne in e; auto.
          rewrite Ps in e. congruence.
        - destruct ι; inversion REL; subst; simpl in *.
          all: rewrite lookup_insert_ne; auto; 
            intros ->; rewrite Ps in LOCK; congruence.
      Qed.
      
      Lemma advance_next_owner st:
        owner (advance_next st ) = owner st.
      Proof using. 
        rewrite /advance_next. destruct role_of_dec as [[? ?] | ?]; auto.
      Qed. 
            
      Lemma advance_next_ticket st:
        ticket (advance_next st ) = ticket st.
      Proof using. 
        rewrite /advance_next. destruct role_of_dec as [[? ?] | ?]; auto.
      Qed.

      Lemma advance_next_helper_L o t (rm: tl_role_map) ρo ρ:
        role_map (advance_next (<{o + 1, t, <[ρo := (tl_L, false)]> rm}>)) !! ρ = Some (tl_L, false) <-> (rm !! ρ = Some (tl_L, false) \/ ρ = ρo).
      Proof using.
        (* clear eventual_release.  *)
        rewrite /advance_next.
        destruct role_of_dec as [[? ?] | ?]; simpl in *.
        - assert (x ≠ ρo) as NEQ.
          { intros ->. rewrite lookup_insert in e. congruence. }
          rewrite lookup_insert_ne in e; auto.
          destruct (decide (x = ρ)) as [-> | NEQ'].
          { rewrite lookup_insert. split; [congruence| ].
            intros [? | ->]; try congruence. rewrite e in H. congruence. }
          rewrite lookup_insert_ne; auto.
          destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite /advance_next. rewrite lookup_insert. tauto. }
          rewrite lookup_insert_ne; auto. split; auto.
          intros [? | ?]; done.
        - destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite /advance_next. rewrite lookup_insert. tauto. }
          rewrite lookup_insert_ne; auto. split; auto.
          intros [? | ?]; done.
      Qed. 

      Lemma advance_next_helper_U o t (rm: tl_role_map) ρo ρ k b
        (RMρo: rm !! ρo = Some (tl_U o, true))
        (UNIQ: forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
                 (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2)
        (TKo: forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o):
        role_map (advance_next (<{o + 1, t, <[ρo := (tl_L, false)]> rm}>)) !! ρ = Some (tl_U k, b) <-> (exists b', rm !! ρ = Some (tl_U k, b') /\ 
                    (k = o + 1 /\ b = false /\ b' = true \/
                     k ≠ o /\ k ≠ (o + 1) /\ b' = b)). 
      Proof using.
        rewrite /advance_next.
        destruct role_of_dec as [[? ?] | ?]; simpl in *.
        - assert (x ≠ ρo) as NEQ.
          { intros ->. rewrite lookup_insert in e. congruence. }
          rewrite lookup_insert_ne in e; auto.
          destruct (decide (x = ρ)) as [-> | NEQ'].
          { rewrite lookup_insert. split.
            - intros. inversion H. eexists. eauto.
            - intros [b' [RMρ ST]].
              rewrite e in RMρ. intuition; congruence. }
          rewrite lookup_insert_ne; auto.
          destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite lookup_insert. rewrite RMρo. split; intros ST. 
            - congruence.
            - destruct ST as [b' ST]; intuition; subst.
              + inversion H. lia.
              + congruence. }
          rewrite lookup_insert_ne; auto. split; intros; intuition. 
          + exists b. split; auto. right. repeat split; auto; intros ->.
            * destruct NEQ''. eapply UNIQ; eauto.
            * destruct NEQ'. eapply UNIQ; eauto.
          + destruct H as [b' [X ?]]. rewrite X.
            repeat f_equal. intuition. subst.  
            destruct NEQ'. eapply UNIQ; eauto. 
        - destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite /advance_next. rewrite lookup_insert.
            rewrite RMρo. split; intros; intuition; try congruence.
            destruct H as [? [? [?|?]]]; subst.
            - inversion H. lia.
            - intuition. congruence. }
          rewrite lookup_insert_ne; auto. split; intros; intuition; auto.
          + exists b. split; auto. right. repeat split; auto. 
            * intros ->. destruct NEQ''; eapply UNIQ; eauto.
            * intros ->. destruct b.
              ** destruct (n ρ). rewrite lookup_insert_ne; auto.
              ** apply TKo in H. lia.
          + destruct H as [? [? ?]]; intuition; subst; auto.
            destruct (n ρ). rewrite lookup_insert_ne; auto.
      Qed. 


      Ltac simpl_li_eq := match goal with
                          | H: <[?x:=?y]> ?m !! ?x = ?r |- _
                            => rewrite lookup_insert in H
                          end.
      Ltac simpl_li_eq' := match goal with
                           | |- <[?x:=?y]> ?m !! ?x = ?r
                             => rewrite lookup_insert
                           end.
      
      Ltac simpl_li_neq := match goal with
                           | H: <[?x:=?y]> ?m !! ?x' = ?r, NE: ?x ≠ ?x' |- _ => 
                               rewrite lookup_insert_ne in H; [| by apply NE]
                           | H: <[?x:=?y]> ?m !! ?x' = ?r, NE: ?x' ≠ ?x |- _ =>
                               rewrite lookup_insert_ne in H;
                               [| by apply not_eq_sym; apply NE]
                           end.
      Ltac simpl_li_neq' := match goal with
                           | NE: ?x ≠ ?x' |- <[?x:=?y]> ?m !! ?x' = ?r => 
                               rewrite lookup_insert_ne; [| by apply NE]
                           | NE: ?x' ≠ ?x |- <[?x:=?y]> ?m !! ?x' = ?r => 
                               rewrite lookup_insert_ne;
                               [| by apply not_eq_sym; apply NE]
                           end.
      
      Ltac simpl_li := (repeat simpl_li_eq); (repeat simpl_li_neq);
                       (try simpl_li_eq'); (try simpl_li_neq'). 

      Lemma step_preserves_tl_state_wf st ℓ st'
        (WF: tl_state_wf st) (STEP: fmtrans ExtTL_FM st ℓ st'):
        tl_state_wf st'.
      Proof using. 
        destruct st as [o t rm]. destruct st' as [o' t' rm'].
        red in WF. destruct WF as (LE & TKS & TKo & UNIQ).
        inversion STEP; subst.
        - inversion STEP0; subst; simpl in *; auto.
          + rename o' into o.
            split; [lia| ]. 
            split; [| split]. 
            * intros. specialize (TKS k).
              destruct (decide (k = t)) as [-> | NEQ].
              { split; [| lia]. intros T.
                exists ρ. eexists. rewrite lookup_insert. split; eauto. }
              etransitivity.
              { etransitivity; [| apply TKS]. lia. }
              split; intros; intuition. 
              ** destruct H as (?&?&?). 
                 do 2 eexists. rewrite lookup_insert_ne; eauto.
                 intros <-. congruence.
              ** destruct H as (?&?&?).
                 do 2 eexists.
                 rewrite <- H. symmetry. apply lookup_insert_ne.
                 intros <-. rewrite lookup_insert in H. congruence.
            * intros.
              destruct (decide (ρ0 = ρ)) as [-> | NEQ].
              2: { rewrite lookup_insert_ne in H; eauto. } 
              rewrite lookup_insert in H. inversion H.
              subst k next_en0.
              destruct (decide (o = t)); congruence.
            * intros. destruct (decide (ρ1 = ρ)), (decide (ρ2 = ρ)).
              all: subst; simpl_li; inversion R1; inversion R2; subst; auto. 
              1, 2: enough (k < k); [lia| ]; apply TKS; by eauto.
              eapply UNIQ; eauto.
          + subst st'' st'3 st'2 st'0 st' st'1.
             assert (o' = o + 1 /\ t' = t) as [-> ->].
             { rewrite /advance_next in H4.
               destruct (role_of_dec _ _) as [[? ?] | ?]; by inversion H4. }
             apply Nat.le_lteq in LE as [LT | ->].
             2: { enough (t < t); [lia| ]. apply TKS. eauto. }
             rewrite H4. red.
             split; [lia| ]. split; [| split]. 
             * intros. 
               rewrite /advance_next in H4.
               destruct (role_of_dec) as [[? ?] | ?]; simpl in *;
                 inversion H4; subst rm'; clear H4.
               ** destruct (decide (ρ = x)).
                  { subst x. rewrite lookup_insert in e. congruence. }
                  rewrite lookup_insert_ne in e; auto.
                  destruct (decide (k = o)) as [-> | NEQ].
                  { split; [lia| ]. intros (ρ' & e' & RMρ'). 
                    destruct (decide (ρ' = ρ)).
                    { subst ρ'. rewrite lookup_insert_ne in RMρ'; auto.
                      rewrite lookup_insert in RMρ'. congruence. }
                    destruct (decide (x = ρ')).
                    { subst x. rewrite lookup_insert in RMρ'.
                      inversion RMρ'. lia. }
                    rewrite !lookup_insert_ne in RMρ'; auto.
                    destruct n0. eapply UNIQ; eauto. }
                  etransitivity; [etransitivity| ]; [| by apply (TKS k) |].
                  { lia. }
                  split.
                  *** intros. destruct H as (?&?&?). 
                      destruct (decide (k = o + 1)).
                      **** subst. exists x, false. by rewrite lookup_insert.
                      **** do 2 eexists. 
                           rewrite !lookup_insert_ne; [by apply H| ..].
                           { congruence. }
                           intros <-. rewrite e in H. congruence.
                  *** intros. destruct H as (?&?&?). 
                      destruct (decide (k = o + 1)).
                      **** subst. eauto.
                      **** destruct (decide (x = x0)).
                           all: subst; simpl_li; inversion H; subst.
                           { lia. }
                           destruct (decide (ρ = x0)). 
                           all: subst; simpl_li; inversion H; subst; eauto. 
               ** specialize (TKS k). 
                  split.
                  *** intros [GEk LTk].
                      apply proj1 in TKS.
                      specialize_full TKS; [lia| ]. destruct TKS as (?&?&TKS). 
                      do 2 eexists. rewrite lookup_insert_ne; eauto.
                      intros <-. rewrite R in TKS.
                      inversion TKS. lia.
                  *** intros. destruct H as (?&?&H). 
                      destruct (decide (ρ = x)) as [-> | ?].
                      { rewrite lookup_insert in H. congruence. }
                      destruct (decide (k = o)) as [-> | NEQko].
                      **** rewrite lookup_insert_ne in H; auto. 
                           destruct n0. eapply UNIQ; eauto. 
                      **** enough (o <= k < t); [lia| ]. apply TKS.
                           rewrite lookup_insert_ne in H; eauto.
             * intros. rewrite /advance_next in H4.
               destruct role_of_dec as [[? ?] | ?]; simpl in *; 
                 inversion H4; subst rm'; clear H4.
               ** destruct (decide (ρ0 = x)), (decide (x = ρ)), (decide (ρ0 = ρ)); 
                    do 2 (subst; simpl_li; inversion H; inversion e; subst; auto).
                  apply TKo in H. subst k.
                  destruct n1. eapply UNIQ; eauto. 
               ** destruct (decide (ρ0 = ρ));
                    subst; simpl_li; inversion H; subst; auto. 
                  apply TKo in H. subst k.
                  destruct n0. eapply UNIQ; eauto. 
             * intros.
               pose proof H4 as rm'_eq. apply (f_equal role_map) in rm'_eq. simpl in rm'_eq.
               rewrite -rm'_eq in R1 R2. 
               eapply advance_next_helper_U in R1, R2; auto.
               destruct R1 as (?&?&R0), R2 as (?&?&R3).
               destruct R0, R3; intuition; subst.
               all: lia || eapply UNIQ; eauto.
        - destruct ι; simpl in REL; inversion REL; subst o0 t0 rm0 o' t' rm'.
          + split; auto. split; [| split]. 
            * intros. etransitivity; [etransitivity|]; [| apply TKS |]; [reflexivity|..].
              split; intros; intuition; destruct H as (?&?&?). 
              ** destruct (decide (x = ρ)) as [-> | NEQ].
                 *** exists ρ, true. rewrite lookup_insert. congruence.
                 *** exists x, x0. rewrite lookup_insert_ne; auto.
              ** destruct (decide (x = ρ)) as [-> | NEQ].
                 *** rewrite lookup_insert in H.
                     exists ρ, false. congruence.
                 *** rewrite lookup_insert_ne in H; auto.
                     eauto.
            * intros. eapply TKo; eauto. rewrite -H.
              symmetry. apply lookup_insert_ne.
              intros ->. rewrite lookup_insert in H. congruence.
            * intros.
              destruct (decide (ρ1 = ρ)), (decide (ρ2 = ρ)).
              all: subst; simpl_li; inversion R1; inversion R2; subst; auto. 
              all: eapply UNIQ; eauto.
          + split; auto. split; [| split]. 
            * intros. etransitivity; [etransitivity|]; [| apply TKS |]; [reflexivity|..].
              split; intros; intuition; destruct H as (?&?&?). 
              ** exists x, x0. destruct (decide (x = ρ)); 
                   subst; simpl_li; [congruence| auto]. 
              ** destruct (decide (x = ρ)); subst; simpl_li; inversion H; eauto.
            * intros. destruct (decide (ρ0 = ρ)); subst; simpl_li; try congruence.
              eapply TKo; eauto.
            * intros.
              destruct (decide (ρ1 = ρ)), (decide (ρ2 = ρ)).
              all: subst; simpl_li; inversion R1; inversion R2; subst; auto. 
              all: eapply UNIQ; eauto.
      Qed.


      Lemma tl_valid_trace_states i st (ITH: tr S!! i = Some st):
        tl_state_wf st. 
      Proof using FROM_INIT VALID.
        gd st. induction i.
        { intros. by apply FROM_INIT. }

        pose proof (trace_has_len tr) as [len LEN]. 
        intros [rm' t' o']. rewrite -Nat.add_1_r. intros ITH'.
        forward eapply trace_lookup_dom_strong with (i := i) as [_ ITH]; eauto.
        specialize_full ITH; [eapply state_lookup_dom; eauto| ].
        destruct ITH as (?&?&?&ITH). 
        forward eapply trace_valid_steps' as STEP; eauto.
        apply state_label_lookup in ITH.
        destruct ITH as (?&ITH0&?). 
        rewrite ITH' in ITH0. inversion ITH0. subst.
        eapply step_preserves_tl_state_wf; eauto.
      Qed.

      Lemma step_counters_mono st ℓ st' (STEP: fmtrans ExtTL_FM st ℓ st'):
        owner st <= owner st' /\ ticket st <= ticket st'.
      Proof using.
        inversion STEP; subst.
        - inversion STEP0; subst; simpl in *; try lia.
          subst st'1 st'0 st''. simpl in *.
          rewrite advance_next_owner advance_next_ticket. simpl. lia.
        - destruct ι; simpl in REL; inversion REL; subst; simpl; lia.
      Qed. 

      Lemma trace_counters_mono i j st st'
        (ITH: tr S!! i = Some st) (JTH: tr S!! j = Some st') (LE: i <= j):
        owner st <= owner st' /\ ticket st <= ticket st'.
      Proof using VALID.
        apply Nat.le_sum in LE as [d ->].
        gd i. gd st. gd st'. induction d.
        { intros. rewrite Nat.add_0_r in JTH.
          assert (st' = st) as -> by congruence. lia. }
        intros. rewrite Nat.add_succ_r -Nat.add_1_r in JTH.
        pose proof (trace_has_len tr) as [len LEN]. 
        forward eapply trace_lookup_dom_strong with (i := (i + d)) as [_ J'TH]; eauto.
        specialize_full J'TH; [eapply state_lookup_dom; eauto| ].
        destruct J'TH as (?&?&?&J'TH). 
        forward eapply trace_valid_steps' as STEP; eauto. 
        apply step_counters_mono in STEP; auto.  
        apply state_label_lookup in J'TH as (J'TH_ & JTH_ & LBL).
        assert (x1 = st') as -> by congruence.
        specialize (IHd _ _ _ ITH J'TH_). lia. 
      Qed.
      
      Lemma has_lock_kept (ρ: tl_role) (o: nat):
        @label_kept_state ExtTL_FM 
          (fun st => tl_state_wf st /\ owner st = o /\ has_lock_st ρ st) (inl ρ).
      Proof using FROM_INIT.
        red. intros. destruct Ps as (WF & OW & [b OWNER]).
        split. 
        { eapply step_preserves_tl_state_wf; eauto. }
        inversion STEP; subst.
        - rewrite /has_lock_st. assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; eauto. 
          { split; auto. rewrite lookup_insert_ne; eauto. }
          destruct NEQ. eapply WF; eauto.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *.
          all: split; [auto| red]. 
          + assert (ρ0 = ρ) as -> by (eapply WF; eauto).
            rewrite lookup_insert. eauto.
          + rewrite lookup_insert_ne; eauto.
            intros ->. congruence.
      Qed.

      (* it turns out shorter to just repeat the previous proof *)
      Lemma has_lock_active_kept (ρ: tl_role) (o: nat):
        @label_kept_state ExtTL_FM 
          (fun st => tl_state_wf st /\ owner st = o /\
                    role_map st !! ρ = Some (tl_U o, true)) (inl ρ).
      Proof using FROM_INIT.
        red. intros. destruct Ps as (WF & OW & OWNER).
        split. 
        { eapply step_preserves_tl_state_wf; eauto. }
        inversion STEP; subst.
        - rewrite /has_lock_st. assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; eauto. 
          { split; auto. rewrite lookup_insert_ne; eauto. }
          destruct NEQ. eapply WF; eauto.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *.
          all: split; [auto| ]. 
          + assert (ρ0 = ρ) as -> by (eapply WF; eauto).
            rewrite lookup_insert. eauto.
          + rewrite lookup_insert_ne; eauto.
            intros ->. congruence.
      Qed.

      Lemma lock_wait_kept (ρ ρo: tl_role) o n:
        @label_kept_state ExtTL_FM 
          (fun st => exists b bo, tl_state_wf st /\ 
                   role_map st !! ρ = Some (tl_U n, b) /\ 
                   role_map st !! ρo = Some (tl_U o, bo) /\
                   owner st = o) (inl ρo).
      Proof using FROM_INIT.
        red. intros. destruct Ps as (b & bo & WF & TKn & OWNER & OWo).
        forward eapply (has_lock_kept ρo (owner st) _ _ _ _ _ STEP). Unshelve.
        3: { eauto. }
        2: { repeat split; eauto. red. eauto. rewrite OWo. eauto. }
        intros (WF' & OWNER' & LOCK'). 
        
        destruct (decide (ρo = ρ)) as [-> | NEQ].
        { assert (n = owner st /\ bo = b) as [-> ->] by (split; congruence). 
          red in LOCK'. destruct LOCK' as [e LOCK']. 
          exists e, e. repeat split; eauto; congruence. }

        assert (owner st < n /\ b = true) as [LT ->].
        { destruct st as [o_ t rm]. simpl in *. subst o_.  
          destruct WF as (LE & TKS & TKO & UNIQ).
          destruct (decide (n = o)) as [-> | NEQ'].
          { destruct NEQ. eapply UNIQ; eauto. }
          specialize (TKS n). apply proj2 in TKS. specialize_full TKS; [eauto|]. 
          destruct b; [split; [lia|auto]| ].
          by apply TKO in TKn. }

        destruct LOCK' as [bo' LOCK'].
        exists true, bo'. repeat split; eauto; try congruence.  

        inversion STEP; subst.
        - inversion STEP0; subst; simpl in *.
          + rewrite lookup_insert_ne; auto.
            intros ->. congruence.
          + congruence.
          + subst st''.
            rewrite advance_next_owner in OWNER'.  subst st'0. simpl in *. lia.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *. 
          all: rewrite lookup_insert_ne; eauto; intros ->; congruence.
      Qed.

      Lemma lock_wait_active_kept (ρ ρo: tl_role) o n:
        @label_kept_state ExtTL_FM 
          (fun st => exists b, tl_state_wf st /\ 
                   role_map st !! ρ = Some (tl_U n, b) /\ 
                   role_map st !! ρo = Some (tl_U o, true) /\
                   owner st = o) (inl ρo).
      Proof using FROM_INIT.
        red. intros. destruct Ps as (b & WF & TKn & OWNER & OWo).
        forward eapply (has_lock_active_kept ρo (owner st) _ _ _ _ _ STEP). Unshelve.
        3: { eauto. }
        2: { repeat split; eauto. rewrite OWo. eauto. }
        intros (WF' & OWNER' & LOCK'). 
        
        destruct (decide (ρo = ρ)) as [-> | NEQ].
        { assert (n = owner st) as -> by congruence.
          exists true. repeat split; eauto; congruence. } 

        assert (owner st < n /\ b = true) as [LT ->].
        { destruct st as [o_ t rm]. simpl in *. subst o_.  
          destruct WF as (LE & TKS & TKO & UNIQ).
          destruct (decide (n = o)) as [-> | NEQ'].
          { destruct NEQ. eapply UNIQ; eauto. }
          specialize (TKS n). apply proj2 in TKS. specialize_full TKS; [eauto|]. 
          destruct b; [split; [lia|auto]| ].
          by apply TKO in TKn. }

        destruct LOCK' as [bo' LOCK'].
        exists true. split; eauto; try congruence. apply and_assoc. split; [| congruence].

        inversion STEP; subst.
        - inversion STEP0; subst; simpl in *.
          + assert (ρ0 ≠ ρ) by congruence. 
            rewrite lookup_insert_ne; auto. 
            split; auto. 
            rewrite lookup_insert_ne; auto. 
            intros ->. congruence.
          + split; auto. 
          + subst st''.
            rewrite advance_next_owner in OWNER'.  subst st'0. simpl in *. lia.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *. 
          all: split; auto; rewrite lookup_insert_ne; eauto; intros ->; congruence.
      Qed.

      
      Let tl_eventual_release := @eventual_release tl_fair_model _ _ _ 
                                   tl_active_exts_spec
                                   has_lock_st active_st.

      Lemma has_lock_unique st ρ1 ρ2
        (WF: tl_state_wf st)
        (LOCK1: has_lock_st ρ1 st) (LOCK2: has_lock_st ρ2 st):
        ρ1 = ρ2.
      Proof using.
        destruct LOCK1 as [? L1]. destruct LOCK2 as [? L2].
        destruct st. eapply WF; eauto.
      Qed.

      Lemma lock_eventually_acquired_iteration o t rm ρ i d
        (ST: tr S!! i = Some <{ o, t, rm }>)
        (R: rm !! ρ = Some (tl_U (S o + d), true))
        (EV_REL: tl_eventual_release tr ρ i):
        ∃ (n : nat) (st': tl_st),
          let e' := if (decide (d = 0)) then false else true in
          let a := if (decide (d = 0)) then 0 else 1 in
          i < n ∧ tr S!! n = Some st' ∧ owner st' = o + 1 /\
          role_map st' !! ρ = Some (tl_U (S o + d), e') /\
          forall k st_k, i <= k < n + a → tr S!! k = Some st_k → ¬ has_lock_st ρ st_k.
      Proof using VALID FROM_INIT FAIR.
        assert (exists ρo, has_lock_st ρo <{ o, t, rm }>) as [ρo LOCK].
        { apply tl_valid_trace_states in ST as (LE & TKS & _).
          apply Lt.le_lt_or_eq_stt in LE as [LT | ->].
          2: { enough (S t + d < t); [lia| ]. apply TKS. eauto. }
          specialize (TKS o). apply proj1 in TKS. specialize_full TKS; auto. }
        assert (ρo ≠ ρ) as NEQ.
        { intros ->. red in LOCK. destruct LOCK as [? LOCK]. 
          rewrite R in LOCK. inversion LOCK. lia. }
        
        forward eapply eventual_release_strenghten as HH; eauto.
        { apply active_st_dec. }
        { intros. split; auto. intros.
          assert (k = i) as -> by lia.
          rewrite ST in KTH. inversion KTH. subst st_k.
          intros [? LOCK']. rewrite R in LOCK'.
          simpl in LOCK'. inversion LOCK'. lia. }

        rename HH into EV_REL'. specialize_full EV_REL'.
        destruct EV_REL' as (k & (st' & KTH & LEik & ENρo) & MINk).
        
        forward eapply steps_keep_state with (i := i) (j := k) (k := k) as LOCK'.
        3: { apply (lock_wait_kept ρ ρo). }
        all: eauto.
        { eexists. split; [apply ST|]. 
          red in LOCK. destruct LOCK as [? LOCK]. do 2 eexists.
          split; [| split]; [..|split]; eauto. 
          eapply tl_valid_trace_states; eauto. }
        { intros. destruct IKJ as [[v ->]%Nat.le_sum KJ].
          intros ->. enough (k <= i + v); [lia| ]. apply MINk.
          forward eapply (proj1 (label_lookup_states tr (i + v))) as HH; eauto.
          destruct HH as [[st1 ST1] [st2 ST2]].
          eexists. split; [| split]; [eauto| lia|].
          forward eapply trace_valid_steps' as STEP; eauto.
          { eapply state_label_lookup; eauto. }
          inversion STEP; subst.
          apply active_st_enabled.
          eapply fm_live_spec; eauto. }
        simpl in LOCK'. destruct LOCK' as (b & bo & WF' & R' & Ro' & OW').
        assert (bo = true) as ->.
        { red in ENρo. destruct ENρo. congruence. }
        
        forward eapply (kept_state_fair_step VALID) with (i := k). 
        { apply (lock_wait_active_kept ρ ρo). }
        all: eauto.
        { simpl. intros. red. simpl. rewrite /ext_live_roles. 
          apply elem_of_union_l. apply elem_of_map_2.
          apply active_st_enabled. red.
          destruct Pst. eexists. apply H. }
        { simpl. repeat split; eauto. }
        intros (j & st'' & [[LEkj STEPj] MINj] & JTH & b_ & WF'' & RMρ'' & RMρo'' & OW'').
        assert (b_ = true) as ->.
        { destruct b_; auto.
          destruct st''; simpl in *. destruct WF'' as (? & ? & TKo'' & _).
          apply TKo'' in RMρ''. lia. }

        forward eapply (proj1 (label_lookup_states tr j)) as [_ [st''' J'TH]]; eauto.
        exists (j + 1), st'''. split; [lia| ]. split; [auto| ].
        forward eapply (trace_valid_steps' _ _ VALID j) as STEP; eauto.
        { eapply state_label_lookup; eauto. }
        inversion STEP; subst. inversion STEP0; subst; simpl in *.
        { congruence. }
        { rewrite RMρo'' in R0. inversion R0. lia. }
        subst st''0. split.
        { rewrite advance_next_owner. subst st'0. simpl. lia. }

        assert (exists ρ', rm0 !! ρ' = Some (tl_U (S (owner st')), true)) as [ρ' RM'].
        { destruct WF'' as (? & ? & ? & ?).          
          pose proof (H0 (S o + d)) as B. apply proj2 in B. specialize_full B.
          { rewrite OW''. eauto. }
          pose proof (H0 (S o)) as RR. apply proj1 in RR. specialize_full RR.
          { lia. }
          destruct RR as (ρ' & b' & R'_).
          exists ρ'. rewrite <- OW''. destruct b'; auto.
          apply H1 in R'_. lia. }
        rewrite -OW'' -Nat.add_1_r in RM'.
        assert (ρo ≠ ρ') as NEQ'.
        { intros <-. rewrite RMρo'' in RM'. inversion RM'. lia. }
        subst st'0. simpl. rewrite /advance_next.
        destruct role_of_dec as [[? ?] | ?]; simpl in *.
        2: { destruct (n ρ'). rewrite lookup_insert_ne; auto. }
        assert (x ≠ ρo) as NEQ''.
        { intros ->. rewrite lookup_insert in e. congruence. }
        rewrite lookup_insert_ne in e; auto.
        assert (x = ρ') as -> by (eapply WF''; eauto).
        assert (ρo ≠ ρ) as NEQ'''.
        { intros ->. rewrite RMρ'' in RMρo''. inversion RMρo''. lia. } 
        
        assert (∀ k0 st_k, i <= k0 < j + 1 → tr S!! k0 = Some st_k → ¬ has_lock_st ρ st_k) as NOLOCKρ.
        { destruct st' as [o' t' rm']. simpl in *.
          assert (o' = o) as -> by lia. 
          intros. intros LOCKρ'.
          forward eapply steps_keep_state with (i := i) (j := k0) (k := k0). 
          3: { apply has_lock_kept. }
          all: eauto. 
          { eexists. repeat split; eauto using tl_valid_trace_states. }
          { intros. intros ->.
            specialize (MINk k1). specialize_full MINk.
            { forward eapply (proj1 (label_lookup_states tr k1)) as [[? ?] [? ?]]; [eauto| ].
              eexists. split; eauto. split; [lia| ].
              apply active_st_enabled.
              red. enough (inl ρo ∈ live_roles ExtTL_FM x).
              { simpl in H4. rewrite /ext_live_roles in H4.
                apply elem_of_union in H4 as [? | ?].
                - apply elem_of_map_inj_gset in H4; [auto | congruence].
                - rewrite set_map_compose_gset in H4.
                  apply elem_of_map_1 in H4 as (? & ? & ?). congruence. }
              eapply fm_live_spec; eauto.
              pose proof (trace_valid_steps'' _ _ VALID k1). 
              eapply (trace_valid_steps'' _ _ VALID k1); eauto. }
            
            move MINj at bottom. specialize (MINj k1 (conj MINk H1)).
            lia. }
          { lia. }
          intros (? & ? & ?). 
          destruct NEQ'''. eapply has_lock_unique; eauto. }

        destruct (decide (ρ = ρ')) as [-> | ?].
        { rewrite lookup_insert.
          rewrite RMρ'' in e. inversion e. 
          destruct (decide (d = 0)) as [-> | ?]; [| lia]; auto.
          rewrite !Nat.add_0_r. auto. }
        do 2 (rewrite lookup_insert_ne; auto).
        destruct (decide (d = 0)) as [-> | ?]; split; try rewrite !Nat.add_0_r; auto.
        { rewrite Nat.add_0_r -Nat.add_1_r -OW'' in RMρ''.
          destruct n. eapply WF''; eauto. }
        intros. destruct (decide (k0 = j + 1)) as [? | ?].
        2: { eapply NOLOCKρ; eauto. lia. }
        subst. rewrite J'TH in H0. inversion H0. subst st_k. clear H0.
        rewrite /has_lock_st advance_next_owner /=.
        intros [e' LOCK']. apply advance_next_helper_U in LOCK'; eauto.
        2, 3: by apply WF''.
        destruct LOCK' as [e'' [RM0ρ bar]].
        rewrite RMρ'' in RM0ρ. inversion RM0ρ. lia.
      Qed.
        
      Lemma lock_eventually_acquired o t rm ρ i wt 
        (ST: tr S!! i = Some <{ o, t, rm }>)
        (WAIT: o ≠ wt)
        (R: rm !! ρ = Some (tl_U wt, true))
        (EV_REL: tl_eventual_release tr ρ i):
        ∃ (n : nat) (st' : tl_st),
          i < n ∧ tr S!! n = Some st' ∧ has_lock_st ρ st' ∧ ¬ active_st ρ st'.
      Proof using VALID FROM_INIT FAIR.
        assert (o < wt) as LT.
        { apply PeanoNat.Nat.le_neq. split; auto. 
          apply tl_valid_trace_states in ST. apply ST. eauto. }
        apply Nat.le_succ_l in LT. apply Nat.le_sum in LT as [d ->]. clear WAIT.
        gd i. gd o. gd rm. gd t. induction d.
        { intros. eapply lock_eventually_acquired_iteration in ST; eauto.
          simpl in ST.
          (* desc. *)
          destruct ST as (n&st'&ST). 
          rewrite Nat.add_0_r -Nat.add_1_r in ST. 
          rewrite /has_lock_st /active_st. 
          exists n, st'.
          rewrite decide_True in ST; [| done].  
          repeat split; try by apply ST.
          2: { intros [? ?]. intuition. congruence. }
          exists false. etransitivity; [apply ST| ]. 
          do 3 f_equal. lia. }
        intros. eapply lock_eventually_acquired_iteration in ST; eauto.
        simpl in ST. destruct ST as (n&st'&ST). 
        destruct st'. simpl in *.
        replace (S (o + S d)) with (S (S o) + d) in ST by lia.
        rewrite decide_False in ST; [| lia].
        destruct ST as (ST&ST0&ST1&ST2&ST3). 
        eapply IHd in ST2.
        2: { rewrite -Nat.add_1_r -ST1. eauto. }
        2: { do 2 red. intros. subst. simpl in *.
             rename ST3 into NOLOCKρ.
             do 2 red in EV_REL.
             eapply EV_REL; eauto.
             intros.
             destruct (Nat.le_gt_cases n j) as [LE | LT].
             { specialize (AFTER LE) as [? BETWEEN]. split; auto.
               intros.
               destruct (Nat.le_gt_cases k n) as [LE' | LT'].
               - eapply NOLOCKρ; [| apply KTH]. rewrite decide_False; lia.
               - eapply BETWEEN; [| apply KTH]. lia. }
             assert (ρ' ≠ ρ) as NEQ.
             { intros ->. edestruct (NOLOCKρ j); eauto. lia. }
             split; auto. intros. eapply NOLOCKρ; [| apply KTH]. lia. }
        destruct ST2 as (n0&st'&?). 
        exists n0, st'. repeat split; try by apply H. lia. 
      Qed.

      Lemma tl_ev_rel_extend i st ρ j
        (ITH: tr S!! i = Some st)
        (RMρ: role_map st !! ρ = Some (tl_L, true))
        (EV_REL: tl_eventual_release tr ρ i)
        (MIN: ∀ k : nat, i ≤ k ∧ tr L!! k = Some (Some (inl ρ)) → j ≤ k):
        tl_eventual_release tr ρ (j + 1).
      Proof using VALID.
        do 2 red. intros. simpl in *. rename j0 into k.  
        destruct (Nat.le_gt_cases i k) as [LEik | LTki].
        2: { eapply EV_REL; eauto. lia. } 
        
        assert (forall m st_m, i <= m <= j -> tr S!! m = Some st_m ->
                          role_map st_m !! ρ = Some (tl_L, true)) as KEEPρ.
        { intros.
          forward eapply steps_keep_state with (i := i) (j := j) (k := m).
          3: by apply lock_compete_kept.
          all: eauto.
          intros. intros ->. destruct (MIN k0); auto with lia. }
        
        destruct (Nat.le_gt_cases k j) as [LEkj | LTjk].
        - eapply EV_REL; eauto. intros.
          split. 
          + intros ->. specialize (KEEPρ k st'). specialize_full KEEPρ; auto.
            destruct HAS_LOCK. congruence. 
          + intros m st_m ? ? [?]. intros.
            specialize (KEEPρ m st_m). specialize_full KEEPρ; auto with lia. 
            congruence. 
        - destruct AFTER as [NEQ NOLOCKρ]; [lia| ].
          eapply EV_REL; eauto. intros. split; auto.
          intros m st_m ? ? LOCKρ.  
          destruct (Nat.le_gt_cases m j) as [LEmj | LTjm].
          + specialize (KEEPρ m st_m). specialize_full KEEPρ; auto with lia.
            destruct LOCKρ. congruence. 
          + edestruct NOLOCKρ; eauto. lia. 
      Qed.
        

      Theorem tl_progress ρ i st
        (ITH: tr S!! i = Some st)
        (CAN_LOCK: can_lock_st ρ st)
        (ACT: active_st ρ st)
        (EV_REL: tl_eventual_release tr ρ i):
        exists n st', i < n /\ tr S!! n = Some st' /\ has_lock_st ρ st' /\
                   ¬ active_st ρ st'.
      Proof using VALID FAIR FROM_INIT.
        red in CAN_LOCK. destruct CAN_LOCK as [e RMρ].
        assert (e = true) as -> by (destruct ACT; congruence). 

        forward eapply (kept_state_fair_step VALID (inl ρ)).
        { apply lock_compete_kept. }
        all: eauto.
        { clear dependent st. simpl. intros st STρ. 
          red. rewrite /ext_live_roles. simpl. rewrite /ext_live_roles. 
          apply elem_of_union_l. apply elem_of_map_2.
          simpl. rewrite /tl_live_roles.
          apply elem_of_dom. eexists. apply map_filter_lookup_Some_2; done. }
        intros (j & st' & [[LEij ITH'] MIN] & STEP & RMρ'). 

        apply Nat.le_sum in LEij as [d ->]. 
        forward eapply (proj1 (label_lookup_states tr (i + d))) as [_ [st'' ST''']]; eauto.
        forward eapply (proj1 (label_lookup_states tr (i + d))); [eauto| ].
        intros [_ [s'_ S'_]].
        assert (s'_ = st'') as -> by congruence. clear S'_. 
        forward eapply (trace_valid_steps' _ _ VALID (i + d)) as TRANS; auto. 
        { by eapply state_label_lookup. }
          
        simpl in TRANS. inversion TRANS as [? ? ? TRANS'| ]; subst.
        inversion TRANS'; subst; simpl in *.
        all: try by rewrite RMρ' in R.
        destruct (decide (o = t)) as [<- | WAIT]. 
        { exists (i + d + 1). eexists.
          repeat split; [lia|..]; try by eauto.
          - red. eexists. simpl. rewrite lookup_insert. eauto. 
          - rewrite /active_st. simpl. rewrite lookup_insert. intros [? [=]]. }
        
        eapply lock_eventually_acquired in ST'''.
        - destruct ST''' as (?&?&?). do 2 eexists.
          repeat split; try by apply H. lia.
        - apply WAIT.
        - rewrite lookup_insert. eauto.
        - eapply (tl_ev_rel_extend i); eauto with lia. 
      Qed.

    End ProgressPropertiesImpl. 

    Instance TLFairLock: 
      @FairLock tl_fair_model 
        allows_unlock allows_lock 
        _ tl_active_exts_spec
        can_lock_st has_lock_st active_st tl_state_wf.
    Proof.
      econstructor.
      - red. intros.
        eapply tl_progress; eauto.
      - apply allows_unlock_impl_spec.
      - apply allows_lock_impl_spec.
      - intros. solve_decision.
      - intros. solve_decision.
      - intros. rewrite /active_st.
        destruct (role_map st !! ρ) as [[? b] |] eqn:R; rewrite R. 
        + destruct b; [left | right]; eauto. by intros [? [=]].
        + right. by intros [? [=]].         
    Qed.      

  End ProgressProperties. 

End Model.
