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

  Definition tl_role := nat. 

  (* TODO: how to make Inductive and Record section-local? *)
  Inductive tl_role_stage := 
  | tl_L
  | tl_U (t: nat)
  .

  Definition tl_role_st: Set := tl_role_stage * bool. 

  Definition tl_role_map := gmap tl_role tl_role_st. 

  Definition tl_st' := (nat * nat * tl_role_map)%type. 

  Definition tl_state_wf
    (st': tl_st'): Prop :=
    let '(o, t, rm) := st' in
    (* (o t: nat) (rm: tl_role_map) := *)
    o <= t /\
    (forall k, o <= k < t <-> exists ρ e, rm !! ρ = Some (tl_U k, e)) /\
    (forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o) /\
    (forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
       (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2).

    
  Record tl_st := mkTlSt {
                      owner: nat;
                      ticket: nat;
                      role_map: tl_role_map;
                      tl_wf: tl_state_wf (owner, ticket, role_map);
                    }. 

  Definition simpl_tl_st '(mkTlSt o t rm wf): tl_st' := (o, t, rm). 

  #[global] Instance tl_role_eqdec: EqDecision tl_role.
  Proof using. solve_decision. Defined.

  #[global] Instance tl_role_stage_eqdec: EqDecision tl_role_stage. 
  Proof using. solve_decision. Defined.
  
  #[global] Instance tl_role_st_eqdec: EqDecision tl_role_st. 
  Proof using. solve_decision. Defined.

  Instance wf_PI st': ProofIrrel (tl_state_wf st').
  Proof. apply make_proof_irrel. Qed. 

  #[global] Instance tl_st_eqdec: EqDecision tl_st. 
  Proof using.
    intros [o1 t1 rm1 wf1] [o2 t2 rm2 wf2].
    destruct (decide (o1 = o2 /\ t1 = t2 /\ rm1 = rm2)).
    2: { right. set_solver. }
    destruct a as (->&->&->).
    left. eapply @f_equal. apply wf_PI.  
  Qed. 

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

  (* Let advance_next (o t: nat) rm :=  *)
  Definition advance_next: tl_st' -> tl_st' :=
        fun '(o, t, rm) =>
        match role_of_dec rm (tl_U o, true) with
        | inl (exist _ r _) => 
            let rm' := <[r := (tl_U o, false)]> rm in
            (* mkTlSt (owner st) (ticket st) rm' *)
            (o, t, rm')
        | inr NO => (o, t, rm)
        end.

  Notation "<{ o , t , rm }>" := (o, t, rm).

  Inductive tl_trans': tl_st' -> option tl_role -> tl_st' -> Prop :=
  | tl_take_ticket o t rm r (R: rm !! r = Some (tl_L, true)):
    let next_en := if decide (o = t) then false else true in
    tl_trans' <{o, t, rm}> (Some r) <{o, t + 1, <[r := (tl_U t, next_en)]> rm}>
  | tl_spin (o t k: nat) rm r (LT: o ≠ k) (R: rm !! r = Some (tl_U k, true)):
    tl_trans' <{o, t, rm}> (Some r) <{o, t, rm}>
  | tl_unlock o t rm r (R: rm !! r = Some (tl_U o, true)):
    let st' := <{o + 1, t, <[r := (tl_L, false)]> rm}> in
    let st'' := advance_next st' in
    tl_trans' <{o, t, rm}> (Some r) st''
  .

  Definition tl_trans st1 oρ st2 :=
    tl_trans' (simpl_tl_st st1) oρ (simpl_tl_st st2). 

  Definition tl_live_roles (st: tl_st): gset tl_role :=
    dom (filter (fun '(r, (_, e)) => e = true) (role_map st)).

  Lemma live_spec_holds:
    forall s ρ s', tl_trans s (Some ρ) s' -> ρ ∈ tl_live_roles s.
  Proof.
    intros s ρ s' TRANS. rewrite /tl_live_roles.
    destruct s, s'. 
    inversion TRANS; subst; simpl. 
    all: eapply elem_of_dom_2; apply map_filter_lookup_Some_2; done.
  Qed.

  Definition tl_init_st' (n: nat): tl_st' :=
    let rm := gset_to_gmap (tl_L, true) (set_seq 0 n) in
    <{ 0, 0, rm }>.

  Lemma tl_init_st'_wf n:
    tl_state_wf (tl_init_st' n). 
  Proof using. 
    rewrite /tl_init_st'. 
    red. split; [lia| ]. split; [| split]. 
    - split; [lia| ]. intros [ρ [? RMρ]].
      apply lookup_gset_to_gmap_Some in RMρ as [_ ?]. congruence.
    - intros. rewrite lookup_gset_to_gmap_Some in H.
      by destruct H. 
    - intros. rewrite lookup_gset_to_gmap_Some in R1. 
      by destruct R1.
  Qed. 
  
  #[global] Instance tlSt_inhabited: Inhabited tl_st. 
  Proof.
    apply populate. esplit.
    apply (tl_init_st'_wf 0).
  Qed. 

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

  Definition disabled_st ρ st :=
    exists r, (role_map st) !! ρ = Some (r, false).

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


  Lemma advance_next_helper_U o t (rm: tl_role_map) ρo ρ k b
    (RMρo: rm !! ρo = Some (tl_U o, true))
    (UNIQ: forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
             (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2)
    (TKo: forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o):
    snd (advance_next (<{o + 1, t, <[ρo := (tl_L, false)]> rm}>)) !! ρ = Some (tl_U k, b) <-> (exists b', rm !! ρ = Some (tl_U k, b') /\
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
  
  Lemma step_preserves_tl_state_wf st ℓ st'
    (WF: tl_state_wf st) (STEP: tl_trans' st ℓ st'):
    tl_state_wf st'.
  Proof using. 
    destruct st as [[o t] rm]. destruct st' as [[o' t'] rm'].
    red in WF. destruct WF as (LE & TKS & TKo & UNIQ).
    inversion STEP; subst; simpl in *; auto.
    + rename o' into o.
      split; [lia| ]. 
      split; [| split]. 
      * intros. specialize (TKS k).
        destruct (decide (k = t)) as [-> | NEQ].
        { split; [| lia]. intros T.
          exists r. eexists. rewrite lookup_insert. split; eauto. }
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
        destruct (decide (r = ρ)) as [-> | NEQ].
        2: { rewrite lookup_insert_ne in H; eauto. } 
        rewrite lookup_insert in H. inversion H.
        subst k next_en0.
        destruct (decide (o = t)); congruence.
      * intros. destruct (decide (ρ1 = r)), (decide (ρ2 = r)).
        all: subst; simpl_li; inversion R1; inversion R2; subst; auto. 
        1, 2: enough (k < k); [lia| ]; apply TKS; by eauto.
        eapply UNIQ; eauto.
    + subst st'' st'2 st'1 st'0 st'.
      assert (o' = o + 1 /\ t' = t) as [-> ->].
      { rewrite /advance_next in H.
        destruct (role_of_dec _ _) as [[? ?] | ?]; by inversion H. }
      apply Nat.le_lteq in LE as [LT | ->].
      2: { enough (t < t); [lia| ]. apply TKS. eauto. }
      rewrite H. red.
      split; [lia| ]. split; [| split]. 
      * intros. 
        rewrite /advance_next in H.
        destruct (role_of_dec) as [[? ?] | ?]; simpl in *;
          inversion H; subst rm'; clear H.
        ** destruct (decide (r = x)).
           { subst x. rewrite lookup_insert in e. congruence. }
           rewrite lookup_insert_ne in e; auto.
           destruct (decide (k = o)) as [-> | NEQ].
           { split; [lia| ]. intros (ρ' & e' & RMρ'). 
             destruct (decide (ρ' = r)).
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
                    destruct (decide (r = x0)). 
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
               destruct (decide (r = x)) as [-> | ?].
               { rewrite lookup_insert in H. congruence. }
               destruct (decide (k = o)) as [-> | NEQko].
               **** rewrite lookup_insert_ne in H; auto. 
                    destruct n0. eapply UNIQ; eauto. 
               **** enough (o <= k < t); [lia| ]. apply TKS.
                    rewrite lookup_insert_ne in H; eauto.
      * intros. rewrite /advance_next in H.
        destruct role_of_dec as [[? ?] | ?]; simpl in *; 
          inversion H; subst rm'; clear H.
        ** destruct (decide (r = x)), (decide (x = ρ)), (decide (r = ρ)); 
             do 2 (subst; simpl_li; inversion H0; inversion e; subst; auto).
           apply TKo in H0. subst k.
           destruct n1. eapply UNIQ; eauto. 
        ** destruct (decide (r = ρ));
             subst; simpl_li; inversion H0; subst; auto. 
           apply TKo in H0. subst k.
           destruct n0. eapply UNIQ; eauto. 
      * intros.
        pose proof H as rm'_eq. apply (f_equal snd) in rm'_eq. simpl in rm'_eq.
        rewrite -rm'_eq in R1 R2. 
        eapply advance_next_helper_U in R1, R2; auto.
        destruct R1 as (?&?&R0), R2 as (?&?&R3).
        destruct R0, R3; intuition; subst.
        all: lia || eapply UNIQ; eauto.
  Qed. 
        
  Lemma tl_trans_reduce st1' oρ st2'
    (TRANS': tl_trans' st1' oρ st2')
    (WF1: tl_state_wf st1'):
    exists st1 st2, simpl_tl_st st1 = st1' /\ simpl_tl_st st2 = st2' /\ tl_trans st1 oρ st2.
  Proof.
    destruct st1' as [[o1 t1] rm1], st2' as [[o2 t2] rm2].
    pose proof (step_preserves_tl_state_wf _ _ _ WF1 TRANS') as WF2.  
    exists (mkTlSt o1 t1 rm1 WF1), (mkTlSt o2 t2 rm2 WF2).
    done. 
  Qed. 

  Definition enhance_tl_st' (st': tl_st') (wf: tl_state_wf st'): tl_st.
    destruct st' as [[o t] rm].
    eapply mkTlSt; eauto.
  Defined. 

  Lemma tl_trans_reduce' o1 t1 rm1 wf1 oρ o2 t2 rm2
    (TRANS': tl_trans' (o1, t1, rm1) oρ (o2, t2, rm2)):
    tl_trans (mkTlSt o1 t1 rm1 wf1) oρ (mkTlSt o2 t2 rm2 (step_preserves_tl_state_wf _ _ _ wf1 TRANS')).
  Proof.
    done. 
  Qed.


  Lemma tl_trans_reduce'' o1 t1 rm1 wf1 oρ st2'
    (TRANS': tl_trans' (o1, t1, rm1) oρ st2'):
    tl_trans (mkTlSt o1 t1 rm1 wf1) oρ (enhance_tl_st' st2' (step_preserves_tl_state_wf _ _ _ wf1 TRANS')). 
  Proof.
    destruct st2' as [[o2 t2] rm2]. done. 
  Qed.

  Lemma tl_strong_FM: FM_strong_lr tl_fair_model.
  Proof. 
    red. intros. 
    destruct st as [o t rm].
    rewrite /active_st. simpl.
    rewrite /tl_live_roles. simpl. rewrite elem_of_dom.  
    split.
    - intros [[r ?] RMρ]. apply map_filter_lookup_Some in RMρ as [RMρ ->].  
      destruct r.
      + eexists. 
        unshelve apply tl_trans_reduce'.
        4: by apply tl_take_ticket.
       + destruct (decide (o = t0)). 
        * eexists. unshelve apply tl_trans_reduce''. 
          2: { subst. eapply tl_unlock. by rewrite RMρ. }
        * eexists. unshelve apply tl_trans_reduce''.
          2: { eapply tl_spin; eauto. }
    - intros [st' STEP]. destruct st'.
      inversion STEP; subst.
      all: eexists; eapply map_filter_lookup_Some; split; done.
  Qed.

  (* TODO: move *)
  Lemma ex_prod {A B: Type} {P: A * B -> Prop}:
    (exists ab, P ab) <-> (exists a b, P (a, b)).
  Proof. split; [intros [[??] ?]| intros (?&?&?)]; eauto. Qed.  

  Lemma active_st_enabled (ρ: tl_role) (st: tl_st):
    active_st ρ st <-> @role_enabled_model tl_fair_model ρ st.
  Proof using.
    rewrite /role_enabled_model. simpl.
    rewrite /tl_live_roles /active_st.
    rewrite elem_of_dom.    
    rewrite /is_Some.
    rewrite ex_prod. apply exist_proper. intros.
    rewrite ex_det_iff.
    2: { intros ? ?%map_filter_lookup_Some. apply H. }
    rewrite map_filter_lookup_Some. tauto. 
  Qed.

  Global Instance active_st_dec (ρ: tl_role) (st: tl_st):
    Decision (active_st ρ st).
  Proof using. 
    rewrite /active_st.
    destruct (role_map st !! ρ).
    2: { right. intros (? & ?). congruence. }
    destruct p. destruct b.
    2: { right. intros (? & ?). congruence. }
    left. eexists. eauto.
  Qed. 
    
  Global Instance disabled_st_dec (ρ: tl_role) (st: tl_st):
    Decision (disabled_st ρ st).
  Proof using. 
    rewrite /disabled_st.
    destruct (role_map st !! ρ).
    2: { right. intros (? & ?). congruence. }
    destruct p. destruct b.
    { right. intros (? & ?). congruence. }
    left. eexists. eauto.
  Qed. 
    

  (* Definition tl_is_init_st (st: tl_st) :=  *)
  (*   exists n, st = tl_init_st n.  *)

  Section TlExtTrans.

    Inductive allows_unlock' ρ : tl_st' -> tl_st' -> Prop :=
    | allows_unlock_step o t rm (LOCK: rm !! ρ = Some (tl_U o, false)):
      allows_unlock' ρ (o, t, rm) (o, t, (<[ρ := (tl_U o, true)]> rm))
    .

    Inductive allows_lock' ρ : tl_st' -> tl_st' -> Prop :=
    | allows_lock_step t o rm (LOCK: rm !! ρ = Some (tl_L, false)):
      allows_lock' ρ (o, t, rm) (o, t, (<[ρ := (tl_L, true)]> rm))
    .

    Definition allows_unlock ρ st1 st2 := 
      allows_unlock' ρ (simpl_tl_st st1) (simpl_tl_st st2). 

    Definition allows_lock ρ st1 st2 := 
      allows_lock' ρ (simpl_tl_st st1) (simpl_tl_st st2).

    Lemma allows_unlock'_preserves_tl_state_wf ρ st st'
      (STEP: allows_unlock' ρ st st')
      (WF: tl_state_wf st):
      tl_state_wf st'.
    Proof.
      destruct st as [[o t] rm]. destruct st' as [[o' t'] rm'].
      red in WF. destruct WF as (LE & TKS & TKo & UNIQ).
      inversion STEP; subst.
      split; auto.
      split; [| split]. 
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
    Qed. 
 
    Lemma allows_lock'_preserves_tl_state_wf ρ st st'
      (STEP: allows_lock' ρ st st')
      (WF: tl_state_wf st):
      tl_state_wf st'.
    Proof.
      destruct st as [[o t] rm]. destruct st' as [[o' t'] rm'].
      red in WF. destruct WF as (LE & TKS & TKo & UNIQ).
      inversion STEP; subst.
      split; auto. split; [| split]. 
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

    Instance allows_lock_ex_dec:
      forall st ρ, Decision (∃ st', allows_lock ρ st st'). 
    Proof using.
      intros [o t rm] ρ. rewrite /allows_lock. simpl. 
      destruct (decide (rm !! ρ = Some (tl_L, false))).
      - left. simpl.
        forward eapply allows_lock_step as AL.
        { apply e. }
        pose proof (allows_lock'_preserves_tl_state_wf _ _ _ AL tl_wf0) as WF2.
        exists (mkTlSt o t (<[ρ:=(tl_L, true)]> rm) WF2).
        done. 
      - right. intros [st' L]. inversion L. congruence. 
    Defined.

    Instance allows_unlock_ex_dec: 
      forall st ρ, Decision (∃ st', allows_unlock ρ st st'). 
    Proof using. 
      intros [o t rm] ρ. rewrite /allows_unlock. simpl. 
      destruct (decide (rm !! ρ = Some (tl_U o, false))). 
      - left. 
        forward eapply allows_unlock_step as AL.
        { apply e. }
        pose proof (allows_unlock'_preserves_tl_state_wf _ _ _ AL tl_wf0) as WF2.
        exists (mkTlSt o t (<[ρ:=(tl_U o, true)]> rm) WF2).
        done. 
      - right. intros [st' TRANS]. inversion TRANS. subst. set_solver.
    Defined.  

    Definition tl_active_exts st: gset fl_EI := 
      set_map (flU (M := tl_fair_model)) 
          (filter (fun ρ => exists st', allows_unlock ρ st st') (dom (role_map st)))
      ∪
      set_map (flL (M := tl_fair_model)) 
          (filter (fun ρ => exists st', allows_lock ρ st st') (dom (role_map st))).
    
    Lemma tl_active_exts_spec st ι:
      ι ∈ tl_active_exts st <-> ∃ st', @fl_ETs tl_fair_model allows_unlock allows_lock ι st st'.
    Proof using. 
      destruct st as [o t rm wf]. 
      unfold tl_active_exts.
      rewrite elem_of_union.
      rewrite !elem_of_map. repeat setoid_rewrite elem_of_filter.
      simpl.  
      erewrite exist_proper.
      2: { intros. rewrite and_assoc. apply iff_and_impl_helper.
           intros [? [[o2 t2 rm2 wf2] AU]]. subst.
           red in AU. simpl in AU. inversion AU. subst.  
           by eapply elem_of_dom. }
      rewrite or_comm. 
      erewrite exist_proper.
      2: { intros. rewrite and_assoc. apply iff_and_impl_helper.
           intros [? [[o2 t2 rm2 wf2] AU]]. subst.
           red in AU. simpl in AU. inversion AU. subst.  
           by eapply elem_of_dom. }
      destruct ι; set_solver. 
    Qed. 

    Definition is_unused ρ st :=
      ρ ∉ dom (role_map st). 

    Definition waits_st ρ (st: tl_st) :=
      exists b k, role_map st !! ρ = Some (tl_U k, b) /\
              k ≠ owner st.

    Definition does_lock ρ st := can_lock_st ρ st \/ waits_st ρ st.

    Instance does_lock_dec ρ st: Decision (does_lock ρ st).
    Proof.
      rewrite /does_lock /can_lock_st /waits_st.
      destruct st as [o t rm wf]. 
      destruct (rm !! ρ) as [[rs e]| ] eqn:R; simpl; rewrite !R. 
      2: { simpl. right. set_solver. }
      simpl. destruct rs as [| m]. 
      { left. eauto. }
      destruct (decide (o = m)).
      - subst. right. set_solver.
      - left. eauto.
    Qed. 
        
    Definition tl_FLP: FairLockPredicates tl_fair_model.
      (* the simple way doesn't get through *)
      (* refine {| fair_lock.can_lock_st := can_lock_st |}.  *)
      unshelve esplit.
      - exact does_lock.
      - exact has_lock_st.
      - exact is_unused. 
      (* ???  *)
      (* 1-3: solve_decision.  *)
      (* all: solve_decision. *)
      - solve_decision.
      - solve_decision.
      - solve_decision.
    Defined. 
      
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

  End TlExtTrans.
 
End Model.

  Notation "<{ o , t , rm }>" := (o, t, rm).

  Ltac unfold_ρ_props ρ :=
    repeat
      match goal with
      | H: waits_st ρ ?st |- _ => destruct H as (?&?&H&?)
      | H: does_unlock ρ ?st |- _ => simpl in H
      | H: has_lock_st ρ ?st |- _ => destruct H as [? H]
      | H: can_lock_st ρ ?st |- _ => destruct H as [? H]
      | H: disabled_st ρ ?st |- _ => destruct H as [? H]
      | H: active_st ρ ?st |- _ => destruct H as [? H]
      end.
  
  Ltac subst_ρ_props ρ :=
    repeat
      match goal with
      | X: role_map ?st !! ρ = Some ?st1,
          Y: role_map ?st !! ρ = Some ?st2
        |- _ => rewrite X in Y; inversion Y
      end.
  
  Ltac simpl_ρ ρ := unfold_ρ_props ρ; subst_ρ_props ρ.


Section Properties.

  Section ProgressProperties.

    Global Instance tl_FLE: @FairLockExt tl_fair_model tl_FLP.
    esplit.
    3: by apply tl_active_exts_spec.
    - simpl. intros ? [] [] AU.  
      red. simpl. rewrite /does_unlock. inversion AU. subst.
      rewrite /has_lock_st /fair_lock.disabled_st /fair_lock.active_st. simpl.
      rewrite -!active_st_enabled. rewrite /active_st. simpl.
      rewrite !lookup_insert. rewrite LOCK. set_solver.
    - simpl. intros ? [] [] AU.  
      red. simpl. rewrite /does_lock. inversion AU. subst.
      rewrite /can_lock_st /fair_lock.disabled_st /fair_lock.active_st. simpl.
      rewrite -!active_st_enabled. rewrite /active_st. simpl.
      rewrite !lookup_insert. rewrite LOCK. set_solver.
    Defined. 
          
    Instance ExtTL: ExtModel tl_fair_model := 
      FL_EM tl_FLE. 
    
    Let ExtTL_FM := @ext_model_FM _ ExtTL. 

    Section ProgressPropertiesImpl.

      Context (tr: mtrace ExtTL_FM).
      Hypothesis (VALID: mtrace_valid tr).
      (* Hypothesis (FROM_INIT: forall st (INIT: tr S!! 0 = Some st), *)
      (*             exists n, st = tl_init_st n).  *)
      (* Hypothesis (FROM_INIT: forall st (INIT: tr S!! 0 = Some st), *)
      (*                tl_state_wf st).  *)
      Hypothesis (FAIR: set_fair_model_trace (fun (ρ: fmrole ExtTL_FM) => 
                                                exists r, ρ = inl r) tr).

      Local Ltac gd t := generalize dependent t.

      Let other_step ρ: option (fmrole ExtTL_FM) -> Prop :=
            fun oρ' => oρ' ≠ Some ρ. 

      Lemma lock_compete_kept_proj (ρ: tl_role) b:
        @label_kept_state ExtTL_FM 
          (fun st => role_map st !! ρ = Some (tl_L, b)) (other_proj ρ).
      Proof using. 
        red. intros.
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2]. simpl in *. 
        inversion STEP; subst.
        - assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; auto. 
          all: try by rewrite lookup_insert_ne; auto.
          subst st''. rewrite /advance_next. 
          destruct (role_of_dec _ _); simpl.
          2: { inversion H4. subst. 
               rewrite lookup_insert_ne; auto. }
          destruct s; simpl.
          inversion H4. subst. 
          rewrite lookup_insert_ne.
          { rewrite lookup_insert_ne; auto. }
          intros ->. subst st'0 st'1. simpl in *. 
          rewrite lookup_insert_ne in e; auto.
          rewrite Pst in e. congruence.
        - destruct ι; inversion REL; subst; simpl in *.
          all: rewrite lookup_insert_ne; auto; 
          intros ->; rewrite Pst in LOCK; try congruence.
      Qed.

      (* TODO: refactor, unify with above *)
      Lemma lock_compete_kept (ρ: tl_role):
        @label_kept_state ExtTL_FM 
          (fun st => role_map st !! ρ = Some (tl_L, true)) (other_step $ inl ρ).
      Proof using. 
        red. intros.
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2]. simpl in *. 
        inversion STEP; subst.
        - assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; auto. 
          all: try by rewrite lookup_insert_ne; auto.
          subst st''. rewrite /advance_next. 
          destruct (role_of_dec _ _); simpl.
          2: { inversion H4. subst. 
               rewrite lookup_insert_ne; auto. }
          destruct s; simpl.
          inversion H4. subst. 
          rewrite lookup_insert_ne.
          { rewrite lookup_insert_ne; auto. }
          intros ->. subst st'0 st'1. simpl in *. 
          rewrite lookup_insert_ne in e; auto.
          rewrite Pst in e. congruence.
        - destruct ι; inversion REL; subst; simpl in *.
          all: rewrite lookup_insert_ne; auto; 
          intros ->; rewrite Pst in LOCK; congruence.
      Qed.
      
      Lemma advance_next_owner st:
        fst $ fst (advance_next st ) = fst $ fst st.
      Proof using.
        destruct st as [[]]. 
        rewrite /advance_next. destruct role_of_dec as [[? ?] | ?]; auto.
      Qed. 
            
      Lemma advance_next_ticket st:
        snd $ fst (advance_next st ) = snd $ fst st.
      Proof using. 
        destruct st as [[]]. 
        rewrite /advance_next. destruct role_of_dec as [[? ?] | ?]; auto.
      Qed.

      Lemma advance_next_helper_L o t (rm: tl_role_map) ρo ρ:
        snd (advance_next (<{o + 1, t, <[ρo := (tl_L, false)]> rm}>)) !! ρ = Some (tl_L, false) <-> (rm !! ρ = Some (tl_L, false) \/ ρ = ρo).
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

      Lemma step_counters_mono st ℓ st' (STEP: fmtrans ExtTL_FM st ℓ st'):
        owner st <= owner st' /\ ticket st <= ticket st'.
      Proof using.
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2].
        inversion STEP; subst.
        - inversion STEP0; subst. 
          all: try by (simpl in *; lia).
          subst st'1 st'0 st''.
          pose proof (@f_equal _ _ (fst ∘ fst) _ _ H4) as O.
          unfold compose in O. rewrite advance_next_owner in O. 
          pose proof (@f_equal _ _ (snd ∘ fst) _ _ H4) as T.
          unfold compose in T. rewrite advance_next_ticket in T. 
          simpl in *. lia. 
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

      Let proj_role (eρ: fmrole ExtTL_FM): fmrole tl_fair_model :=
        match eρ with 
        | inr (env (flL ρ))
        | inr (env (flU ρ))
        | inl ρ => ρ
        end.

      Let other_proj ρ: option (fmrole ExtTL_FM) -> Prop :=
            fun oeρ' => match oeρ' with
                    | Some eρ' => proj_role eρ' ≠ ρ
                    | None => True
                     end. 

      Lemma ext_trans_others_kept st1 ι st2 ρ
        (STEP: ETs ι st1 st2)
        (OTHER: proj_role (inr $ env ι) ≠ ρ):
          role_map st2 !! ρ = role_map st1 !! ρ.
      Proof.
        destruct st1 as [o1 t1 rm1 wf1], st2 as [o2 t2 rm2 wf2].
        destruct ι; inversion STEP; subst; simpl in *.
        all: by apply lookup_insert_ne.
      Qed. 

      (* Lemma has_lock_kept_others (ρ: fmrole tl_fair_model) b: *)
      (*   label_kept_state *)
      (*     (fun st => does_unlock ρ st /\ fair_lock.disabled_st ρ st (FLP := tl_FLP)) *)
      (*     (* (other_proj ρ (FLE := FLE)) *) *)
      (*     (fun oℓ => oℓ ≠ Some (inr (env (flU ρ: @EI _ ExtTL)))) *)
      (*     (M := @ext_model_FM _ ExtTL) *)
      (*     .  *)
      (* Proof using.  *)
      (*   red. intros.  *)
      (*   destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2]. *)
      (*   rename Pst into OWNER. *)
      (*   inversion STEP; subst. *)
      (*   - rewrite /has_lock_st. assert (ρ0 ≠ ρ) as NEQ by (by intros ->).  *)
      (*     inversion STEP0; subst; simpl in *; eauto.  *)
      (*     { rewrite lookup_insert_ne; eauto. } *)
      (*     destruct NEQ. eapply wf1; eauto.  *)
      (*   - destruct ι; simpl in REL; inversion REL; subst; simpl in *. *)
      (*     + assert (ρ0 = ρ) as -> by (eapply wf1; eauto). *)
      (*       inversion STEP. subst. *)
      (*       eapply ext_trans_others_kept in REL0; eauto. congruence.  *)
      (*     + rewrite lookup_insert_ne; eauto. *)
      (* Qed. *)
      
      Lemma has_lock_kept_others (ρ: tl_role) b:
        @label_kept_state ExtTL_FM 
          (fun st => role_map st !! ρ = Some (tl_U (owner st), b)) (other_proj ρ).
      Proof using. 
        red. intros. 
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2].
        rename Pst into OWNER.
        inversion STEP; subst.
        - rewrite /has_lock_st. assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; eauto. 
          { rewrite lookup_insert_ne; eauto. }
          destruct NEQ. eapply wf1; eauto. 
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *.
          + assert (ρ0 = ρ) as -> by (eapply wf1; eauto).
            inversion STEP. subst.
            eapply ext_trans_others_kept in REL0; eauto. congruence. 
          + rewrite lookup_insert_ne; eauto.
      Qed.
      
      Lemma has_lock_kept (ρ: tl_role) (o: nat):
        @label_kept_state ExtTL_FM 
          (fun st => owner st = o /\ has_lock_st ρ st) (other_step $ inl ρ).
      Proof using.
        red. intros. 
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2].
        destruct Pst as (WF & OW & OWNER).
        inversion STEP; subst.
        - rewrite /has_lock_st. assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; eauto. 
          { split; auto. rewrite lookup_insert_ne; eauto. }
          destruct NEQ. eapply wf1; eauto.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *.
          all: split; [auto| red]. 
          + assert (ρ0 = ρ) as -> by (eapply wf1; eauto).
            rewrite lookup_insert. eauto.
          + rewrite lookup_insert_ne; eauto.
            intros ->. congruence.
      Qed.

      (* it turns out shorter to just repeat the previous proof *)
      Lemma has_lock_en_kept (ρ: tl_role) (o: nat):
        @label_kept_state ExtTL_FM 
          (fun st => owner st = o /\ role_map st !! ρ = Some (tl_U o, true)) (other_step $ inl ρ).
      Proof using. 
        red. intros. 
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2].        
        destruct Pst as (OW & OWNER).
        inversion STEP; subst.
        - rewrite /has_lock_st. assert (ρ0 ≠ ρ) as NEQ by (by intros ->). 
          inversion STEP0; subst; simpl in *; eauto. 
          { split; auto. rewrite lookup_insert_ne; eauto. }
          destruct NEQ. eapply wf1; eauto.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *.
          all: split; [auto| ]. 
          + assert (ρ0 = ρ) as -> by (eapply wf1; eauto).
            rewrite lookup_insert. eauto.
          + rewrite lookup_insert_ne; eauto.
            intros ->. congruence.
      Qed.

      Lemma lock_wait_kept (ρ ρo: tl_role) o n:
        @label_kept_state ExtTL_FM 
          (fun st => exists b bo, 
                   role_map st !! ρ = Some (tl_U n, b) /\ 
                   role_map st !! ρo = Some (tl_U o, bo) /\
                   owner st = o) (other_step $ inl ρo).
      Proof using.
        red. intros.
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2].        
        destruct Pst as (b & bo & TKn & OWNER & OWo).
        simpl in *. 
        forward eapply (has_lock_kept ρo o1 _ _ _ _ _ STEP). Unshelve.
        3: { eauto. }
        2: { repeat split; eauto. red. eauto. simpl in *. rewrite OWo. eauto. }
        intros (OWNER' & LOCK'). 

        destruct (decide (ρo = ρ)) as [-> | NEQ].
        { assert (n = o1 /\ bo = b) as [-> ->] by (split; congruence). 
          red in LOCK'. destruct LOCK' as [e LOCK']. 
          exists e, e. simpl in *. repeat split; eauto; congruence. }

        assert (o1 < n /\ b = true) as [LT ->].
        { 
          destruct wf1 as (LE & TKS & TKO & UNIQ).
          destruct (decide (n = o)) as [-> | NEQ'].
          { destruct NEQ. eapply UNIQ; eauto. }
          pose proof (TKS n) as TKS'. apply proj2 in TKS'. specialize_full TKS'; [eauto|]. 
          destruct b; [split; [lia|auto]| ].
          apply TKO in TKn. subst. done. }

        destruct LOCK' as [bo' LOCK'].
        exists true, bo'.
        simpl in *.
        repeat split; eauto; try congruence.  

        inversion STEP; subst.
        - inversion STEP0; subst.
          + simpl in *. rewrite lookup_insert_ne; auto.
            intros ->. congruence.
          + simpl in *. congruence.
          + subst st''.
            pose proof (advance_next_owner st') as O. rewrite H4 in O.
            subst st'0. simpl in *. lia.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *. 
          all: rewrite lookup_insert_ne; eauto; intros ->; congruence.
      Qed.

      Lemma lock_wait_active_kept (ρ ρo: tl_role) o n:
        @label_kept_state ExtTL_FM 
          (fun st => exists b, 
                   role_map st !! ρ = Some (tl_U n, b) /\ 
                   role_map st !! ρo = Some (tl_U o, true) /\
                   owner st = o) (other_step $ inl ρo).
      Proof using. 
        red. intros.
        destruct st as [o1 t1 rm1 wf1], st' as [o2 t2 rm2 wf2].        
        destruct Pst as (b & TKn & OWNER & OWo).
        forward eapply (has_lock_en_kept ρo o1 _ _ _ _ _ STEP). Unshelve.
        3: { eauto. }
        2: { simpl in *. repeat split; eauto. rewrite OWo. eauto. }
        intros (OWNER' & LOCK'). 
        
        destruct (decide (ρo = ρ)) as [-> | NEQ].
        { simpl in *. assert (n = o1) as -> by congruence.
          exists true. repeat split; eauto; congruence. } 

        assert (o1 < n /\ b = true) as [LT ->].
        { 
          destruct wf1 as (LE & TKS & TKO & UNIQ).
          destruct (decide (n = o)) as [-> | NEQ'].
          { destruct NEQ. eapply UNIQ; eauto. }
          pose proof (TKS n) as TKS'. apply proj2 in TKS'. specialize_full TKS'; [eauto|].
          simpl in *. 
          destruct b; [split; [lia|auto]| ].
          apply TKO in TKn. subst. lia. }

        simpl in *. subst.
        (* destruct LOCK' as [bo' LOCK']. *)
        exists true. split; eauto; try congruence.
        (* apply and_assoc. split; [| congruence]. *)

        inversion STEP; subst.
        - inversion STEP0.
          + subst; simpl in *.
            assert (ρ0 ≠ ρ) by congruence. 
            rewrite lookup_insert_ne; auto. 
            (* split; auto.  *)
            (* rewrite lookup_insert_ne; auto.  *)
            (* intros ->. congruence. *)
          + subst; simpl in *. done. 
          + subst st''.
            pose proof (advance_next_owner st') as O. rewrite H4 in O.
            simpl in *. subst. lia.
        - destruct ι; simpl in REL; inversion REL; subst; simpl in *.
          all: rewrite lookup_insert_ne; eauto; intros ->; congruence.
      Qed.

      Let tl_eventual_release := @eventual_release _ tl_FLP ExtTL.  

      Lemma has_lock_unique st ρ1 ρ2
        (LOCK1: has_lock_st ρ1 st) (LOCK2: has_lock_st ρ2 st):
        ρ1 = ρ2.
      Proof using.
        destruct LOCK1 as [? L1]. destruct LOCK2 as [? L2].
        eapply (tl_wf st); eauto.  
      Qed.

      Lemma not_active_disabled ρ st
        (DOM: ρ ∈ dom (role_map st)):
        ¬ active_st ρ st <-> disabled_st ρ st.
      Proof using.
        clear tr VALID FAIR. 
        rewrite /active_st /disabled_st.
        apply elem_of_dom in DOM as [[s e] R]. rewrite R.
        do 2 (rewrite ex_det_iff; [| intros ? [=]; subst; reflexivity]). 
        destruct e; set_solver.
      Qed. 

      Lemma disabled_equiv (ρ: fmrole tl_fair_model) st
        (DOM: ρ ∈ dom (role_map st)):
        disabled_st ρ st <-> fair_lock.disabled_st ρ st (FLP := tl_FLP). 
      Proof using.
        rewrite -not_active_disabled; auto.
        rewrite active_st_enabled. done. 
      Qed.

      Lemma has_lock_dom ρ st
        (LOCK: has_lock_st ρ st):
        ρ ∈ dom (role_map st). 
      Proof. 
        destruct LOCK as [? ?].
        eapply elem_of_dom; eauto. 
      Qed. 

      Lemma does_lock_dom ρ st
        (LOCK: does_lock ρ st):
        ρ ∈ dom (role_map st). 
      Proof.
        destruct LOCK; simpl_ρ ρ. 
        all: eapply elem_of_dom; eauto. 
      Qed. 

      Lemma lock_eventually_acquired_iteration o t rm wf ρ i d
        (ST: tr S!! i = Some (mkTlSt o t rm wf) )
        (R: rm !! ρ = Some (tl_U (S o + d), true))
        (EV_REL: tl_eventual_release tr ρ i):
        ∃ (n : nat) (st': tl_st),
          let e' := if (decide (d = 0)) then false else true in
          let a := if (decide (d = 0)) then 0 else 1 in
          i < n ∧ tr S!! n = Some st' ∧ owner st' = o + 1 /\
          role_map st' !! ρ = Some (tl_U (S o + d), e') /\
          forall k st_k, i <= k < n + a → tr S!! k = Some st_k → ¬ (has_lock_st ρ st_k).
      Proof using VALID FAIR.
        assert (exists ρo, has_lock_st ρo (mkTlSt o t rm wf)) as [ρo LOCK].
        {
          (* apply tl_valid_trace_states in ST as (LE & TKS & _). *)
          pose proof wf as (LE & TKS & ?).
          apply Lt.le_lt_or_eq_stt in LE as [LT | ->].
          2: { enough (S t + d < t); [lia| ]. apply TKS. eauto. }
          specialize (TKS o). apply proj1 in TKS. specialize_full TKS; auto. }
        assert (ρo ≠ ρ) as NEQ.
        { intros ->. red in LOCK. destruct LOCK as [? LOCK]. 
          rewrite R in LOCK. inversion LOCK. lia. }
        
        assert ( ∃ k : nat,
         ClassicalFacts.Minimal
           (λ k0 : nat,
              ∃ st'' : ext_model_FM,
                tr S!! k0 = Some st'' ∧ i ≤ k0 ∧ active_st ρo st'') k
) as HH.
        { destruct (decide (active_st ρo (mkTlSt o t rm wf))).
          { exists i. split; eauto.
            intros ? (?&?&?). lia. }
        
          forward eapply eventual_release_strenghten; eauto.
          { red. by rewrite -active_st_enabled. } 
          { intros. split; auto. intros.
            assert (k = i) as -> by lia.
            rewrite ST in KTH. inversion KTH. subst st_k.
            intros [? LOCK'].
            red in LOCK'. rewrite -active_st_enabled /active_st /= in LOCK'.
            rewrite R in LOCK'. simpl in LOCK'. destruct LOCK'. eauto. }
          by setoid_rewrite active_st_enabled. }
        
        rename HH into EV_REL'. specialize_full EV_REL'.
        destruct EV_REL' as (k & (st' & KTH & LEik & ENρo) & MINk).
        
        forward eapply steps_keep_state with (i := i) (j := k) (k := k) as LOCK'.
        3: { apply (lock_wait_kept ρ ρo). }
        all: eauto.
        { eexists. split; [apply ST|]. 
          red in LOCK. destruct LOCK as [? LOCK]. do 2 eexists.
          split; [| split]; [..|split]; eauto. }
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
        simpl in LOCK'. destruct LOCK' as (b & bo & R' & Ro' & OW').
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
        intros (j & st'' & [[LEkj STEPj] MINj] & JTH & b_ & RMρ'' & RMρo'' & OW'').
        pose proof (tl_wf st'') as WF''. 
        assert (b_ = true) as ->.
        { destruct b_; auto.
          pose proof (tl_wf st'') as (? & ? & TKo'' & _).
          destruct st''; simpl in *.
          apply TKo'' in RMρ''. lia. }

        forward eapply (proj1 (label_lookup_states tr j)) as [_ [st''' J'TH]]; eauto.
        exists (j + 1), st'''. split; [lia| ]. split; [auto| ].
        destruct st'', st'''. simpl in *.  
        forward eapply (trace_valid_steps' _ _ VALID j) as STEP; eauto.
        { eapply state_label_lookup; eauto. }
        inversion STEP; subst. inversion STEP0; subst.
        { simpl in *. congruence. }
        { simpl in *. rewrite RMρo'' in R0. inversion R0. lia. }
        pose proof (advance_next_owner st'0) as O. 
        pose proof (advance_next_ticket st'0) as T.
        (* pose proof (advance_next_helper_U st'0) as OU. *)
        fold st'' in O, T. rewrite H4 in O, T. simpl in *. 
        split.
        { lia. }

        assert (exists ρ', role_map0 !! ρ' = Some (tl_U (S (owner st')), true)) as [ρ' RM'].
        {
          destruct WF'' as (? & ? & ? & ?).
          pose proof (H0 (S (owner st') + d)) as B. apply proj2 in B. specialize_full B.
          { eauto. }
          pose proof (H0 (S (owner st'))) as RR. apply proj1 in RR. specialize_full RR.
          { lia. }
          destruct RR as (ρ' & b' & R'_).
          exists ρ'. destruct b'; auto.
          apply H1 in R'_. lia. }
        rewrite -Nat.add_1_r in RM'.
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
          (* assert (o' = o) as -> by lia. *)
          intros. intros LOCKρ'.
          forward eapply steps_keep_state with (i := i) (j := k0) (k := k0). 
          3: { apply has_lock_kept. }
          all: eauto. 
          (* { eexists. repeat split; eauto using tl_valid_trace_states. } *)
          { intros. intros ->.
            specialize (MINk k1). specialize_full MINk.
            { forward eapply (proj1 (label_lookup_states tr k1)) as [[? ?] [? ?]]; [eauto| ].
              eexists. split; eauto. split; [lia| ].
              apply active_st_enabled.
              red. enough (inl ρo ∈ live_roles ExtTL_FM x).
              { simpl in H5. rewrite /ext_live_roles in H5.
                apply elem_of_union in H5 as [? | ?].
                - apply elem_of_map_inj_gset in H5; [auto | congruence].
                - rewrite set_map_compose_gset in H5.
                  apply elem_of_map_1 in H5 as (? & ? & ?). congruence. }
              eapply fm_live_spec; eauto.
              pose proof (trace_valid_steps'' _ _ VALID k1). 
              eapply (trace_valid_steps'' _ _ VALID k1); eauto. }
            
            move MINj at bottom. specialize (MINj k1 (conj MINk H1)).
            lia. }
          { lia. }
          intros (? & ?). 
          destruct NEQ'''. eapply has_lock_unique; eauto. }

        subst st'' st'4 st'2. inversion H4. subst.  
        destruct (decide (ρ = ρ')) as [-> | ?].
        { subst. simpl in *.
          rewrite lookup_insert.
          rewrite RMρ'' in e. inversion e. 
          destruct (decide (d = 0)) as [-> | ?]; [| lia]; auto.
          rewrite !Nat.add_0_r. auto. }
        do 2 (rewrite lookup_insert_ne; auto).
        destruct (decide (d = 0)) as [-> | ?]; split; try rewrite !Nat.add_0_r; auto.
        { rewrite Nat.add_0_r -Nat.add_1_r in RMρ''.
          destruct n. eapply WF''; eauto. }
        intros. destruct (decide (k0 = j + 1)) as [? | ?].
        2: { eapply NOLOCKρ; eauto. lia. }
        subst. rewrite J'TH in H2. inversion H2. subst st_k. clear H2.
        rewrite /has_lock_st. 
        intros [e' LOCK'].  simpl in LOCK'. 
        do 2 (rewrite lookup_insert_ne in LOCK'; [| done]). 
        rewrite RMρ'' in LOCK'. inversion LOCK'. lia.
      Qed.

      Lemma lock_eventually_acquired
        (* o t rm wf ρ i wt  *)
        i st ρ
        (ST: tr S!! i = Some st)
        (* (WAIT: o ≠ wt) *)
        (* (R: rm !! ρ = Some (tl_U wt, true)) *)
        (COMP: waits_st ρ st)
        (EN: active_st ρ st)
        (EV_REL: tl_eventual_release tr ρ i):
        ∃ (n : nat) (st' : tl_st),
          i < n ∧ tr S!! n = Some st' ∧ has_lock_st ρ st' ∧ ¬ active_st ρ st'.
      Proof using VALID FAIR.
        destruct st as [o t rm wf].
        red in COMP. destruct COMP as (?&wt&COMP&WAIT). 
        red in EN. destruct EN as [? EN].
        simpl in EN. rewrite COMP in EN. inversion EN. subst. clear EN.

        assert (o < wt) as LT.
        { simpl in wf. pose proof wf as wf'%proj2%proj1.
          specialize (wf' wt). apply proj2 in wf'.
          specialize_full wf'; eauto. simpl in *. lia. }
        
        (* assert (o < wt) as LT. *)
        (* { apply PeanoNat.Nat.le_neq. split; auto. *)
        (*   apply wf. eauto. } *)
        apply Nat.le_succ_l in LT. apply Nat.le_sum in LT as [d ->]. clear WAIT.
        gd i. gd o. gd rm. gd t. induction d.
        { intros. eapply lock_eventually_acquired_iteration in ST; eauto.
          simpl in ST.
          (* desc. *)
          destruct ST as (n&st'&ST). 
          rewrite Nat.add_0_r -Nat.add_1_r in ST. 
          rewrite /has_lock_st /active_st. 
          exists n, st'.
          repeat split; try by apply ST.
          2: { intros [? ?]. intuition. congruence. }
          exists false. etransitivity; [apply ST| ]. 
          do 3 f_equal. lia. }
        intros. eapply lock_eventually_acquired_iteration in ST; eauto.
        simpl in ST. destruct ST as (n&st'&ST). 
        destruct st'. simpl in *.
        replace (S (o + S d)) with (S (S o) + d) in ST by lia.
        destruct ST as (ST&ST0&ST1&ST2&ST3).
        rewrite ST1 Nat.add_1_r in tl_wf0, ST0. 
        eapply IHd with (i := n) in ST2. 
        2: { apply ST0. }
        2: { do 2 red. intros. subst. simpl in *.
             rename ST3 into NOLOCKρ.
             do 2 red in EV_REL.
             eapply EV_REL; eauto.
             intros.
             destruct (Nat.le_gt_cases n j) as [LE | LT].
             { specialize (AFTER LE) as [? BETWEEN]. split; auto.
               intros.
               destruct (Nat.le_gt_cases k n) as [LE' | LT'].
               - simpl.
                 apply Classical_Prop.or_not_and. left.                  
                 eapply NOLOCKρ; [| apply KTH]. lia.
               - eapply BETWEEN; [| apply KTH]. lia. }
             assert (ρ' ≠ ρ) as NEQ.
             { intros ->. edestruct (NOLOCKρ j); eauto. lia. }
             split; auto. intros.
             apply Classical_Prop.or_not_and. left. 
             eapply NOLOCKρ; [| apply KTH]. lia. }
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
            simpl_ρ ρ. 
        - destruct AFTER as [NEQ NOLOCKρ]; [lia| ].
          eapply EV_REL; eauto. intros. split; auto.
          intros m st_m ? ? LOCKρ.  
          destruct (Nat.le_gt_cases m j) as [LEmj | LTjm].
          + specialize (KEEPρ m st_m). specialize_full KEEPρ; auto with lia.
            destruct LOCKρ. simpl_ρ ρ. 
          + edestruct NOLOCKρ; eauto. lia. 
      Qed.
        
      Theorem tl_progress ρ i st
        (ITH: tr S!! i = Some st)
        (CAN_LOCK: can_lock_st ρ st)
        (ACT: active_st ρ st)
        (EV_REL: tl_eventual_release tr ρ i):
        exists n st', i < n /\ tr S!! n = Some st' /\ has_lock_st ρ st' /\
                   disabled_st (ρ: fmrole tl_fair_model) st'.
      Proof using VALID FAIR.
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
        destruct st' as [o1 t1 rm1 wf1], st'' as [o2 t2 rm2 wf2]. 
        inversion TRANS'; subst.
        all: try by (simpl in *; rewrite RMρ' in R). 
        destruct (decide (o2 = t1)) as [<- | WAIT]. 
        { exists (i + d + 1). eexists.
          repeat split; [lia|..]; try by eauto.
          - red. eexists. simpl. rewrite lookup_insert. eauto. 
          - apply not_active_disabled.
            { simpl. set_solver. }
            rewrite /active_st. 
            rewrite lookup_insert. intros [? [=]]. }
        
        eapply lock_eventually_acquired in ST'''.
        - destruct ST''' as (?&?&?). do 2 eexists.
          rewrite -not_active_disabled.
          { repeat split; try by apply H. lia. }
          eapply has_lock_dom. apply H. 
        - simpl. red. simpl. rewrite lookup_insert. eauto. 
        - red. rewrite lookup_insert. eauto.
        - eapply (tl_ev_rel_extend i); eauto with lia. 
      Qed.

      Theorem tl_progress_full (ρ: fmrole tl_fair_model) i st
        (ITH: tr S!! i = Some st)
        (CAN_LOCK: does_lock ρ st)
        (ACT: active_st ρ st)
        (EV_REL: tl_eventual_release tr ρ i):
        exists n st', i < n /\ tr S!! n = Some st' /\ 
                   does_unlock ρ st' (FairLockPredicates := tl_FLP) /\
                   fair_lock.disabled_st ρ st' (FLP := tl_FLP).
      Proof using VALID FAIR.
        destruct CAN_LOCK.
        { forward eapply tl_progress; eauto.
          intros (?&?&?&?&?&?).
          do 2 eexists. repeat split; eauto.
          red. rewrite -active_st_enabled. eapply not_active_disabled; auto.
          simpl_ρ ρ. subst. by apply elem_of_dom. }
        forward eapply lock_eventually_acquired; eauto.
        intros (?&?&?&?&?&?).
        do 2 eexists. repeat split; eauto.
        red. by rewrite -active_st_enabled.
      Qed. 

      Lemma tl_unlock_term ρ i st
        (ITH: tr S!! i = Some st)
        (LOCK: has_lock_st ρ st)
        (ACT: active_st ρ st):
        exists n st', i < n /\ tr S!! n = Some st' /\ can_lock_st ρ st' /\
                   disabled_st (ρ: fmrole tl_fair_model) st'.
      Proof using VALID FAIR. 
        red in LOCK. destruct LOCK as [e RMρ].
        destruct st as [o t rm wf]. 
        assert (e = true) as -> by (destruct ACT; congruence). 

        forward eapply (kept_state_fair_step VALID (inl ρ)).
        { apply (has_lock_en_kept ρ o). }
        all: eauto.
        { simpl. 
          intros st [STρ ?].
          red. rewrite /ext_live_roles. simpl. rewrite /ext_live_roles.
          apply elem_of_union_l. apply elem_of_map_2.
          simpl. rewrite /tl_live_roles.
          apply elem_of_dom. eexists. apply map_filter_lookup_Some_2; done. }
        { simpl. done. }
        intros (j & [o' t' rm' wf'] & [[LEij ITH'] MIN] & STEP & RMρ').

        apply trace_label_lookup_simpl' in ITH' as (?&st'&ITH').
        forward eapply trace_state_lookup_simpl; eauto. intros ->.
        pose proof ITH' as TRANS. eapply trace_valid_steps' in TRANS; eauto.
        simpl in *. destruct RMρ' as [-> RMρ']. 
        inversion TRANS; subst. inversion STEP0; subst.
        1, 2: congruence.
        subst st'' st'0. destruct st'. simpl in *.
        assert (role_map0 !! ρ = Some (tl_L, false)) as RM'.
        { destruct role_of_dec; inversion H4; subst. 
          2: { apply lookup_insert. }
          destruct s. inversion H0.
          rewrite lookup_insert_ne.
          2: { intros ->. subst.
               rewrite lookup_insert in e. congruence. }
          by apply lookup_insert. }
        subst. exists (j + 1). eexists. repeat split.
        { lia. }
        { apply state_label_lookup in ITH' as (?&X&?). apply X. }
        { red. simpl. eauto. } 
        { red. simpl. eauto. }
      Qed. 

      Lemma active_disabled_incompat ρ st
        (EN: active_st ρ st) (DIS: disabled_st ρ st):
        False.
      Proof.
        destruct EN, DIS. congruence.
      Qed. 
      
      Lemma disabled_fmtrans_kept (ρ: tl_role):
        @label_kept_state ExtTL_FM 
          (disabled_st ρ) 
          (fun oℓ => match oℓ with | Some (inr _) => False | _ => True end).
      Proof using.
        red. intros * DIS L STEP. inversion STEP; subst; try done.
        assert (ρ ≠ ρ0).
        { intros <-. eapply active_disabled_incompat; eauto.
          apply active_st_enabled. eapply fm_live_spec; eauto. }
        red in DIS. destruct DIS as [? RMρ]. red. 
        destruct st, st'. 
        inversion STEP0; subst; simpl in *.
        - eexists. rewrite lookup_insert_ne; eauto.
        - eauto.
        - subst st'' st'. 
          destruct role_of_dec; [destruct s| ]; inversion H5; subst.
          2: { rewrite lookup_insert_ne; eauto. }
          eexists. rewrite lookup_insert_ne.
          { rewrite lookup_insert_ne; eauto. }
          intros ->. rewrite lookup_insert_ne in e; eauto.
          by rewrite RMρ in e.
      Qed.

      Lemma dom_rolemap_fmtrans_kept (D: gset (fmrole tl_fair_model)):
        @label_kept_state ExtTL_FM 
          (fun st => dom (role_map st) = D)
          (fun oℓ => match oℓ with | Some (inr _) => False | _ => True end).
      Proof using.
        clear dependent tr.
        red. intros * DIS L STEP. inversion STEP; subst; try done.
        destruct st, st'. 
        inversion STEP0; subst; simpl in *. 
        - rewrite !dom_insert_L.
          apply mk_is_Some, elem_of_dom in R. set_solver.
        - eauto.
        - subst st'' st'.
          apply mk_is_Some, elem_of_dom in R. 
          destruct role_of_dec; [destruct s| ]; inversion H4; subst.
          2: { set_solver. }
          rewrite lookup_insert_Some in e. destruct e as [|[? R']].
          { set_solver. }
          apply mk_is_Some, elem_of_dom in R'. set_solver.  
      Qed.

      (* TODO: move *)
      Lemma label_kept_state_and {M: FairModel} Ps1 Ps2 Pl1 Pl2:
        (* (Ps1 Ps2: fmstate M -> Prop) (Pl1 Pl2:  *)
        label_kept_state Ps1 Pl1 -> label_kept_state Ps2 Pl2 ->
        @label_kept_state M (fun st => Ps1 st /\ Ps2 st) (fun l => Pl1 l /\ Pl2 l).
      Proof using.
        clear dependent tr. 
        intros K1 K2. red. intros.
        split; [eapply K1 | eapply K2]; eauto.
        all: tauto.
      Qed. 

      (* Lemma tl_trans_dom st ρ *)
      (*   (LIVE: role_enabled_model ρ st): *)
      (*   ρ ∈ *)

      (* Lemma can_or_has_lock ρ st (DOM: ρ ∈ dom (role_map st)): *)
      (*   can_lock_st ρ st \/ has_lock_st ρ st. *)
      (* Proof. *)
      (*   apply elem_of_dom in DOM as [[d?] DOM]. *)
      (*   rewrite /can_lock_st /has_lock_st.  *)
      (*   destruct d; eauto.  *)

      (* Lemma role_st_trichotomy ρ st (DOM: ρ ∈ dom (role_map st)): *)
      (*   can_lock_st ρ st \/ competes_st ρ st \/ has_lock_st ρ st. *)
      (* Proof using. *)
      (*   clear dependent tr. *)
      (*   apply elem_of_dom in DOM as [[d?] DOM]. *)
      (*   rewrite /can_lock_st /has_lock_st /competes_st. *)
      (*   destruct st. simpl in *. rewrite !DOM.         *)
      (*   destruct d; eauto.  *)
      (*   destruct (decide (t = owner0)); subst; set_solver.  *)
      (* Qed. *)

      Lemma tl_live_dom ρ st
        (LIVE: ρ ∈ tl_live_roles st):
        ρ ∈ dom (role_map st).
      Proof. 
        apply active_st_enabled in LIVE as [??].
        eapply elem_of_dom; eauto.
      Qed.

      (* Lemma tl_trace_termination *)
      (*   (EXT_BOUND: ext_trans_bounded tr (EM := ExtTL)) *)
      (*   (EV_REL: forall ρ i, eventual_release tr ρ i (FL := tl_FLP)): *)
      (* terminating_trace tr. *)
      (* Proof using VALID FAIR. *)
      (*   do 2 red in EXT_BOUND. destruct EXT_BOUND as [n BOUND]. *)
      (*   destruct (after n tr) as [atr| ] eqn:An. *)
      (*   2: { red. eauto. } *)
      (*   forward eapply state_lookup_after'. intros NTH%proj1. *)
      (*   specialize_full NTH; [by eauto| ].  *)
      (*   remember (trfirst atr) as st eqn:X. clear X. *)
      (*   remember (size $ live_roles tl_fair_model st) as a.  *)
      (*   assert (exists i, n = i) as [i NI] by eauto. *)
      (*   rewrite NI in NTH. apply Nat.eq_le_incl in NI. *)
      (*   clear dependent atr.  *)
      (*   generalize dependent i. generalize dependent st. *)
      (*   pattern a. apply lt_wf_ind. simpl. *)
      (*   clear a. intros a IH st SIZE i LE ITH. *)

      (*   destruct (Nat.eq_0_gt_0_cases a) as [-> | NZ]. *)
      (*   { symmetry in SIZE. apply size_empty_inv, leibniz_equiv in SIZE.  *)
      (*     apply trace_state_lookup_simpl' in ITH as ([? step]&ITH&EQ). *)
      (*     simpl in EQ. subst. *)
      (*     destruct step as [[? oρ]|]. *)
      (*     2: { pose proof (trace_has_len tr) as [? LEN]. *)
      (*          eapply terminating_trace_equiv; eauto. *)
      (*          eapply trace_lookup_dom_eq, proj1 in LEN. *)
      (*          specialize_full LEN; eauto. } *)
      (*     pose proof ITH as STEP. eapply trace_valid_steps' in STEP; eauto.           *)
      (*     inversion STEP; subst. *)
      (*     { apply fm_live_spec in STEP. set_solver. } *)
      (*     apply state_label_lookup in ITH as (_&_&?). *)
      (*     edestruct BOUND; eauto. } *)

      (*   intros. apply PeanoNat.Nat.neq_0_lt_0 in NZ.  *)
      (*   forward eapply size_non_empty_iff as [NE _]. specialize_full NE. *)
      (*   { rewrite SIZE in NZ. apply NZ. } *)
      (*   Unshelve. all: try by apply _.  *)
      (*   apply set_choose in NE as [ρ LIVE]. *)
      (*   assert (exists j st', i <= j /\ tr S!! j = Some st' /\  *)
      (*                     disabled_st ρ st') as (j&st'&LE'&JTH&DIS). *)
      (*   { pose proof LIVE as ?%active_st_enabled.  *)
      (*     destruct (role_st_trichotomy ρ st) as [?|[?|?]]. *)
      (*     { eapply tl_live_dom; eauto. } *)
      (*     - forward eapply tl_progress; eauto. *)
      (*       { apply EV_REL. } *)
      (*       intros (j&?&?&?&?&?). *)
      (*       exists j. eexists. repeat split; eauto. lia. *)
      (*     - forward eapply lock_eventually_acquired; eauto. *)
      (*       { apply EV_REL. } *)
      (*       intros (j&?&?&?&?&?). *)
      (*       exists j. eexists. repeat split; eauto. *)
      (*       { lia. } *)
      (*       eapply not_active_disabled; eauto. *)
      (*       eapply has_lock_dom; eauto. *)
      (*     - forward eapply tl_unlock_term; eauto. *)
      (*       intros (j&?&?&?&?&?). *)
      (*       exists j. eexists. repeat split; eauto. lia. } *)
      (*   eapply IH.  *)
      (*   4: { apply JTH. } *)
      (*   3: lia. *)
      (*   2: reflexivity. *)
      (*   rewrite SIZE. *)
      (*   apply union_difference_singleton_L in LIVE. rewrite LIVE. *)
      (*   rewrite size_union_alt. rewrite size_singleton. *)
      (*   rewrite Nat.add_1_l. apply Nat.lt_succ_r. *)
      (*   rewrite difference_twice_L. *)
      (*   apply subseteq_size. apply subseteq_difference_r. *)
      (*   { apply disjoint_singleton_r. intros ?. *)
      (*     eapply active_disabled_incompat; eauto. *)
      (*     apply active_st_enabled; eauto. } *)
      (*   clear dependent ρ. apply elem_of_subseteq. intros ρ LIVE'. *)
      (*   destruct (decide (ρ ∈ tl_live_roles st)) as [?| DIS]; [done| ]. *)

      (*   forward eapply steps_keep_state_inf. *)
      (*   3: { apply dom_rolemap_fmtrans_kept. } *)
      (*   { eauto. } *)
      (*   { eexists. split; [apply ITH| ]. reflexivity. } *)
      (*   { intros. simpl. apply BOUND in H0; [| lia].  *)
      (*     destruct oℓ' as [[|]|]; try done. *)
      (*     eapply H0; eauto. } *)
      (*   2: { apply JTH. } *)
      (*   { lia. } *)
      (*   simpl. intros DOM_EQ.  *)
        
      (*   forward eapply steps_keep_state_inf. *)
      (*   3: { apply (disabled_fmtrans_kept ρ). } *)
      (*   { eauto. } *)
      (*   { eexists. split; [apply ITH| ]. *)
      (*     apply not_active_disabled. *)
      (*     { rewrite -DOM_EQ. by apply tl_live_dom. }   *)
      (*     intros ?%active_st_enabled. apply DIS. eauto. } *)
      (*   { intros. simpl. apply BOUND in H0; [| lia].  *)
      (*     destruct oℓ' as [[|]|]; try done. *)
      (*     eapply H0; eauto. } *)
      (*   2: { apply JTH. } *)
      (*   { lia. } *)
      (*   intros DIS'%not_active_disabled. *)
      (*   { destruct DIS'. by apply active_st_enabled. } *)
      (*   destruct DIS'. eapply elem_of_dom; eauto. *)
      (* Qed.  *)

    End ProgressPropertiesImpl.

    (* TODO: move *)
    Global Instance label_kept_state_Proper {M: FairModel}: 
      Proper ((eq ==> iff) ==> (eq ==> iff) ==> iff) (@label_kept_state M).
    Proof.
      intros ?? EQ1 ?? EQ2.
      rewrite /label_kept_state.
      repeat (apply forall_proper; intros).
      repeat (apply Morphisms_Prop.iff_iff_iff_impl_morphism; auto).
    Qed. 

    (* TODO: move *)
    Global Instance label_kept_state_Proper_impl {M: FairModel}: 
      Proper ((eq ==> iff) ==> (eq ==> flip impl) ==> impl) (@label_kept_state M).
    Proof.
      (* respectful (fun x y => x = y /\ x ≠ inl  *)
      intros ?? EQ1 ?? EQ2.
      red. rewrite /label_kept_state.
      intros. eapply EQ1; [reflexivity| ].
      eapply H; eauto.
      { eapply EQ1; eauto. }
      red in EQ2. eapply EQ2; eauto.   
    Qed.

    Lemma ext_trans_same_unused st1 (ρ: fmrole tl_fair_model) st2 e
      (STEP: fmtrans ExtTL_FM st1 e st2):
      is_unused ρ st1 <-> is_unused ρ st2.
    Proof.
      simpl. rewrite /is_unused. 
      destruct st1 as [o1 t1 rm1 wf1], st2 as [o2 t2 rm2 wf2]. simpl.
      apply not_iff_compat. 
      inversion STEP; subst.
      + inversion STEP0; subst; auto; try set_solver.
        { rewrite dom_insert_L. apply mk_is_Some, elem_of_dom in R. set_solver. }
        subst st'' st'0 st'. simpl in H4.
        apply mk_is_Some, elem_of_dom in R. 
        destruct role_of_dec as [[r ?]| ]; inversion H4; subst. 
        2: { set_solver. }
        rewrite lookup_insert_Some in e. destruct e; [set_solver| ].
        apply proj2, mk_is_Some, elem_of_dom in H. set_solver. 
      + destruct ι; simpl in REL; inversion REL; subst; simpl.
        all: apply mk_is_Some, elem_of_dom in LOCK; set_solver. 
    Qed.  
    
    Lemma unused_kept (ρ: fmrole tl_fair_model):
      @label_kept_state ExtTL_FM 
       (λ (st: fmstate tl_fair_model), is_unused ρ st)
      (fun _ => True).
    Proof.
      red. intros.
      forward eapply ext_trans_same_unused; eauto.
      intros X%proj1. eauto.
    Qed. 
    
    Definition allow_unlock_impl (ρ: fmrole tl_fair_model) (st: tl_st): tl_st.
      destruct st as [o t rm wf].
      destruct (decide (rm !! ρ = Some (tl_U o, false))) as [R|]. 
      2: { exact (mkTlSt o t rm wf). }
      pose proof (allows_unlock_step ρ o t rm R).
      pose proof (allows_unlock'_preserves_tl_state_wf _ _ _ H wf).
      esplit. apply H0. 
    Defined. 
      
    Lemma allows_unlock_impl_spec (ρ: fmrole tl_fair_model) st:
      forall st', allows_unlock ρ st st' <-> 
              (allow_unlock_impl ρ st = st' /\ (has_lock_st ρ st /\ fair_lock.disabled_st ρ st (FLP := tl_FLP))).
    Proof.
      intros st'.      
      destruct st as [o t rm]. destruct st' as [o' t' rm'].
      rewrite /allow_unlock_impl /has_lock_st /disabled_st. simpl.  
      destruct decide. 
      2: { simpl. trans False.
           - apply neg_false. intros AL. inversion AL. by subst.
           - symmetry. apply neg_false.
             intros ([=]&?&?). subst. destruct H4.
             destruct H3 as [? R]. rewrite R in n.
             destruct x; [| set_solver].
             apply active_st_enabled. red. simpl. eauto. }
      split.
      - intros AL. inversion AL. subst.
        repeat split; eauto.
        + f_equal. apply wf_PI.
        + red. rewrite -active_st_enabled. rewrite /active_st.
          simpl. set_solver. 
      - intros ([=]&[?[=]]&?). subst. econstructor.
        destruct x; [| done]. edestruct H5; eauto.
        apply active_st_enabled. red. eauto. 
    Qed.

    Definition allow_lock_impl (ρ: fmrole tl_fair_model) (st: tl_st): tl_st.
      destruct st as [o t rm wf]. 
      destruct (decide (rm !! ρ = Some (tl_L, false))) as [R|]. 
      2: { exact (mkTlSt o t rm wf). }
      pose proof (allows_lock_step ρ t o rm R).
      pose proof (allows_lock'_preserves_tl_state_wf _ _ _ H wf).
      esplit. apply H0. 
    Defined.

    (* Lemma disabled_equiv (ρ: fmrole tl_fair_model) st: *)
    (*   disabled_st ρ st <-> fair_lock.disabled_st ρ st (FLP := tl_FLP). *)
    (* Proof. *)
    (*   rewrite -not_active_disabled.  *)
          
    Lemma allows_lock_impl_spec (ρ: fmrole tl_fair_model) st:
      forall st', allows_lock ρ st st' <-> 
              (allow_lock_impl ρ st = st' /\ (does_lock ρ st /\ fair_lock.disabled_st ρ st (FLP := tl_FLP))).
    Proof.
      destruct st as [o t rm]. intros [o' t' rm'].
      rewrite /allow_unlock_impl /can_lock_st /active_st. simpl.  
      destruct decide. 
      2: { simpl. trans False.
           - apply neg_false. intros AL. inversion AL. by subst.
           - symmetry. apply neg_false.
             intros ([=]&?&?). subst. destruct H4.
             red in H3. destruct H3.
             + 
               destruct H as [? R]. rewrite R in n.
               destruct x; [| set_solver].
               apply active_st_enabled. red. eauto.
             + destruct H as [? (? & R & ?)]. rewrite R in n.
               destruct x; [| set_solver].
               apply active_st_enabled. red. eauto. }
      split.
      - intros AL. inversion AL. subst.
        repeat split; eauto.
        + f_equal. apply wf_PI.
        + red. left. red. eauto. 
        + red.
          rewrite -active_st_enabled. rewrite /active_st.
          simpl. set_solver.
      - intros ([=]&X&?). subst. econstructor.
        red in X. eauto.  
    Qed.

    (* TODO: simplify *)
    Lemma has_lock_kept_dis ρ:
    @label_kept_state
    (@ext_model_FM tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE))
    (λ st : tl_st,
       has_lock_st ρ st ∧ @fair_lock.disabled_st tl_fair_model tl_FLP ρ st)
    (λ oℓ : option (@ext_role tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE)),
       oℓ
       ≠ @Some
           (tl_role + @env_role tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE))
           (@inr tl_role
              (@env_role tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE))
              (@env tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE)
                 (@flU tl_fair_model ρ)))).
      Proof.
        red. intros.
        destruct (decide (oℓ' = Some $ inl ρ)).
        { subst. apply proj2 in Pst. destruct Pst.
          inversion STEP; subst. 
          eapply fm_live_spec; eauto. }
        enough (role_map st' !! ρ = Some (tl_U (owner st'), false)).
        { rewrite /has_lock_st /fair_lock.disabled_st -active_st_enabled /active_st.
          set_solver. }
        destruct Pst.
        red in H0. rewrite -active_st_enabled in H0. apply not_active_disabled in H0. 
        2: { by apply has_lock_dom. }
        simpl_ρ ρ. subst. 
        eapply (has_lock_kept_others ρ false); eauto.
        destruct oℓ'; [| done].
        destruct f.
        { set_solver. }
        destruct e, i.
        - by intros ->.
        - inversion STEP; subst. simpl in REL. inversion REL; subst.
          destruct st. simpl in *. 
          intros ->. congruence.
      Qed. 

    Lemma competes_kept_dis:
  ∀ ρ : fmrole tl_fair_model,
    @label_kept_state
      (@ext_model_FM tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE))
      (λ st : @ext_model_FM tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE),
         @fair_lock.does_lock tl_fair_model tl_FLP ρ st
         ∧ @fair_lock.disabled_st tl_fair_model tl_FLP ρ st)
      (λ oℓ : option
                (fmrole
                   (@ext_model_FM tl_fair_model
                      (@FL_EM tl_fair_model tl_FLP tl_FLE))),
         oℓ
         ≠ @Some
             (fmrole tl_fair_model +
              @env_role tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE))
             (@inr (fmrole tl_fair_model)
                (@env_role tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE))
                (@env tl_fair_model (@FL_EM tl_fair_model tl_FLP tl_FLE)
                   (@flL tl_fair_model ρ)))).
    Proof.
      red. intros.
      destruct (decide (oℓ' = Some $ inl ρ)).
      { subst. apply proj2 in Pst. destruct Pst.
        inversion STEP; subst. 
        eapply fm_live_spec; eauto. }
      destruct Pst.
      destruct H.
      2: { red in H0. rewrite -active_st_enabled in H0. apply not_active_disabled in H0.
           2: { simpl_ρ ρ. by eapply elem_of_dom. }
           simpl_ρ ρ. subst.
           pose proof (tl_wf st). red in H2. apply proj2, proj2, proj1 in H2.
           set_solver. }
      
      enough (role_map st' !! ρ = Some (tl_L, false)).
      { simpl.
        rewrite /does_lock /can_lock_st /fair_lock.disabled_st -active_st_enabled /active_st.
        set_solver. }
      red in H0. rewrite -active_st_enabled in H0. apply not_active_disabled in H0. 
      2: { simpl_ρ ρ. by eapply elem_of_dom. }
      simpl_ρ ρ. subst. 
      eapply (lock_compete_kept_proj ρ false); eauto.
      destruct oℓ'; [| done].
      destruct f.
      { set_solver. }
      destruct e, i.
      - inversion STEP; subst. simpl in REL. inversion REL; subst.
        destruct st. simpl in *. 
        intros ->. congruence.
      - simpl. by intros ->.
    Qed.      

    Instance TLFairLock: @FairLock _ tl_FLP tl_FLE inner_fair_ext_model_trace. 
    Proof.
      econstructor.
      - simpl. apply allows_unlock_impl_spec.
      - simpl. apply allows_lock_impl_spec.
      - apply has_lock_kept_dis. 
      - apply competes_kept_dis. 
      - apply unused_kept.  
      - simpl. intros ? ρ **. 
        red in H. apply not_elem_of_dom_1 in H. 
        destruct H0; simpl_ρ ρ; by rewrite H in H0.
      - simpl. rewrite /is_unused /has_lock_st.
        intros *. rewrite not_elem_of_dom.
        intros X [? Y]. by rewrite X in Y.
      - simpl. intros ? ρ **.
        apply active_st_enabled in H0. 
        red in H. apply not_elem_of_dom_1 in H. 
        simpl_ρ ρ. by rewrite H0 in H. 
      - simpl. done. 
      - simpl. intros **.
        red in H0. rewrite -active_st_enabled in H0. apply not_active_disabled in H0.
        2: { by apply has_lock_dom. }
        red in H2. rewrite -active_st_enabled in H2. apply not_active_disabled in H2.
        2: { by apply has_lock_dom. }
        simpl_ρ ρlg1. simpl_ρ ρlg2. subst.
        pose proof (tl_wf tl_st0) as wf. red in wf.
        eapply wf; eauto.  
      - simpl. intros. destruct H; simpl_ρ ρlg; subst; lia.   
      - simpl. rewrite /does_lock /can_lock_st /waits_st /has_lock_st /is_unused.
        intros st ρ. destruct (role_map st !! ρ) as [[rs ?]| ] eqn:R.
        2: { do 2 right. by eapply not_elem_of_dom. }
        destruct rs as [| m]; eauto.
        destruct (decide (m = owner st)); subst; set_solver.
      - red. intros. simpl. eapply tl_progress_full; eauto.
        by apply active_st_enabled. 
      - red. intros.
        forward eapply tl_unlock_term; eauto.
        { by apply active_st_enabled. }
        intros (?&?&?&?&?&?).
        do 2 eexists. repeat split; eauto.
        { simpl. red. tauto. }
        simpl_ρ ρ. subst. red. rewrite -active_st_enabled.
        rewrite /active_st. set_solver.  
    Qed. 

  End ProgressProperties. 

End Properties. 
