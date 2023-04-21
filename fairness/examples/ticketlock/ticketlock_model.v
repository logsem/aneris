From iris.proofmode Require Import tactics.
From hahn Require Import HahnBase.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
Import derived_laws_later.bi.
From trillium.fairness.examples.ticketlock Require Import lemmas trace_len set_map_properties ext_models trace_helpers fair_lock.


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
                      role_map: tl_role_map
                    }. 

  Notation "<{ o , t , rm }>" := (mkTlSt o t rm).

  #[global] Instance tl_role_eqdec: EqDecision tl_role.
  Proof using. solve_decision. Qed. 

  #[global] Instance tl_role_stage_eqdec: EqDecision tl_role_stage. 
  Proof using. solve_decision. Qed. 
  
  #[global] Instance tl_role_st_eqdec: EqDecision tl_role_st. 
  Proof using. solve_decision. Qed. 

  #[global] Instance tl_st_eqdec: EqDecision tl_st. 
  Proof using. solve_decision. Qed. 
    
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
    exists e, (role_map st) !! ρ = Some (tl_U (owner st), e). 

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


  Section TlExtTrans.

    Inductive allows_unlock : tl_st -> tl_st -> Prop :=
    | allows_unlock_step o t ρ rm (LOCK: rm !! ρ = Some (tl_U o, false)):
      allows_unlock (mkTlSt o t rm) (mkTlSt o t (<[ρ := (tl_U o, true)]> rm))
    .

    Inductive allows_lock ρ : tl_st -> tl_st -> Prop :=
    | allows_lock_step t o rm (LOCK: rm !! ρ = Some (tl_L, false)):
      allows_lock ρ (mkTlSt o t rm) (mkTlSt o t (<[ρ := (tl_L, true)]> rm))
    .

    Inductive tl_EI := eiU | eiL (ρ: tl_role).

    Definition tl_ETs (ι: tl_EI) := 
      match ι with
      | eiU => allows_unlock
      | eiL ρ => allows_lock ρ
      end. 

    Global Instance tl_EI_dec: EqDecision tl_EI. 
    Proof using. solve_decision. Qed. 

    Global Instance tl_EI_cnt: Countable tl_EI. 
    Proof using.
      eapply inj_countable' with 
        (f := fun ι => match ι with | eiU => 0 | eiL ρ => S (ρ: nat) end)
        (g := fun n => match n with | 0 => eiU | S n' => eiL (n': tl_role) end).
      intros. destruct x; auto.
    Qed.

    Lemma allows_unlock_ex_dec: 
      forall st, Decision (∃ st', allows_unlock st st'). 
    Proof using. 
      intros [o t rm]. 
      destruct (role_of_dec rm (tl_U o, false)) as [[r LOCK] | FREE].
      - left. eexists. econstructor. eauto.
      - right. intros [st' TRANS]. inversion TRANS. subst.
        edestruct FREE; eauto.
    Qed. 

    Instance allows_lock_ex_dec:
      forall st ρ, Decision (∃ st', allows_lock ρ st st'). 
    Proof using.
      intros [o t rm] ρ.
      destruct (decide (rm !! ρ = Some (tl_L, false))).
      - left. eexists. econstructor; eauto.
      - right. intros [st' L]. inversion L. congruence. 
    Qed. 

    Definition tl_active_exts st: gset tl_EI := 
      (if (allows_unlock_ex_dec st) then {[ eiU ]} else ∅) ∪
      set_map eiL (filter (fun ρ => exists st', allows_lock ρ st st')
                          (dom (role_map st))).
    

    Lemma tl_active_exts_spec st ι:
      ι ∈ tl_active_exts st <-> ∃ st', tl_ETs ι st st'.
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
        etransitivity.
        { symmetry. apply elem_of_map_inj_gset with (f := eiL).
          red. intros. congruence. }
        etransitivity; [apply elem_of_filter| ].
        simpl.  
        split; [intros [[? ?] ?] | intros [? [FF]]]; eauto. 
        simpl. split.
        + eexists. econstructor; eauto.
        + eapply elem_of_dom_2; eauto.  
    Qed. 

    Instance ExtTL: ExtModel := 
      Build_ExtModel tl_fair_model _ _ _ _ _ tl_active_exts_spec.       
    
  End TlExtTrans.  


  Section ProgressProperties.

    Let ExtTL_FM := ext_model_FM ExtTL. 

    Section ProgressPropertiesImpl.

      Context (tr: mtrace ExtTL_FM).
      Context (len: my_omega.nat_omega) (LEN: trace_len_is tr len).
      Hypothesis (VALID: mtrace_valid tr).
      Hypothesis (FROM_INIT: forall st (INIT: tr S!! 0 = Some st),
                  exists n, st = tl_init_st n). 
      Hypothesis (FAIR: set_fair_model_trace (fun (ρ: fmrole ExtTL_FM) => 
                                                exists r, ρ = inl r) tr).

      (* Let eventual_release ρ i :=  *)
      (*       forall ρ' j st' (JTH: tr S!! j = Some st') *)
      (*         (HAS_LOCK: has_lock_st ρ' st') *)
      (*         (PREVr: ρ' = ρ -> j < i), *)
      (*       exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''. *)

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
            - intros. desc. destruct H0; desc; subst; rewrite e in H; congruence. }
          rewrite lookup_insert_ne; auto.
          destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite lookup_insert. rewrite RMρo. split; intros; desc. 
            - congruence.
            - destruct H0; desc; subst.
              + inversion H. lia.
              + congruence. }
          rewrite lookup_insert_ne; auto. split; intros; desc.
          + exists b. split; auto. right. splits; auto; intros ->.
            * destruct NEQ''. eapply UNIQ; eauto.
            * destruct NEQ'. eapply UNIQ; eauto.
          + rewrite H. repeat f_equal. destruct H0; desc; subst; auto.
            destruct NEQ'. eapply UNIQ; eauto. 
        - destruct (decide (ρo = ρ)) as [-> | NEQ''].
          { rewrite /advance_next. rewrite lookup_insert.
            rewrite RMρo. split; intros; desc; try congruence.
            destruct H0; desc; subst.
            - inversion H. lia.
            - congruence. } 
          rewrite lookup_insert_ne; auto. split; intros; desc; auto.
          + exists b. split; auto. right. splits; auto. 
            * intros ->. destruct NEQ''; eapply UNIQ; eauto.
            * intros ->. destruct b.
              ** destruct (n ρ). rewrite lookup_insert_ne; auto.
              ** apply TKo in H. lia.
          + destruct H0; desc; subst; auto.
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

      Definition tl_state_wf '(mkTlSt o t rm) :=
        o <= t /\
        (forall k, o <= k < t <-> exists ρ e, rm !! ρ = Some (tl_U k, e)) /\
        (forall ρ k, rm !! ρ = Some (tl_U k, false) -> k = o) /\
        (forall ρ1 ρ2 k e1 e2 (R1: rm !! ρ1 = Some (tl_U k, e1))
           (R2: rm !! ρ2 = Some (tl_U k, e2)), ρ1 = ρ2).        
      
      Lemma step_preserves_tl_state_wf st ℓ st'
        (WF: tl_state_wf st) (STEP: fmtrans ExtTL_FM st ℓ st'):
        tl_state_wf st'.
      Proof using. 
        destruct st as [o t rm]. destruct st' as [o' t' rm'].
        red in WF. destruct WF as (LE & TKS & TKo & UNIQ).
        inversion STEP; subst.
        - inversion STEP0; subst; simpl in *; auto.
          + rename o' into o.
            splits; [lia| ..].
            * intros. specialize (TKS k).
              destruct (decide (k = t)) as [-> | NEQ].
              { split; [| lia]. intros T.
                exists ρ. eexists. rewrite lookup_insert. split; eauto. }
              etransitivity.
              { etransitivity; [| apply TKS]. lia. }
              split; intros; desc.
              ** do 2 eexists. rewrite lookup_insert_ne; eauto.
                 intros <-. congruence.
              ** do 2 eexists.
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
             rewrite H4. red. splits.
             * lia. 
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
                  *** intros. desc. 
                      destruct (decide (k = o + 1)).
                      **** subst. exists x, false. by rewrite lookup_insert.
                      **** exists ρ0, e0.
                           rewrite !lookup_insert_ne; [by apply H| ..].
                           { congruence. }
                           intros <-. rewrite e in H. congruence.
                  *** intros. desc.
                      destruct (decide (k = o + 1)).
                      **** subst. eauto.
                      **** destruct (decide (x = ρ0)).
                           all: subst; simpl_li; inversion H; subst.
                           { lia. }
                           destruct (decide (ρ = ρ0)). 
                           all: subst; simpl_li; inversion H; subst; eauto. 
               ** specialize (TKS k). 
                  split.
                  *** intros [GEk LTk].
                      apply proj1 in TKS.
                      specialize_full TKS; [lia| ]. desc.
                      do 2 eexists. rewrite lookup_insert_ne; eauto.
                      intros <-. rewrite R in TKS.
                      inversion TKS. lia.
                  *** intros. desc.
                      destruct (decide (ρ = ρ0)) as [-> | ?].
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
               eapply advance_next_helper_U in R1, R2; auto. desc.
               destruct R0, R3; desc; subst.
               all: lia || eapply UNIQ; eauto.
        - destruct ι; simpl in REL; inversion REL; subst o0 t0 rm0 o' t' rm'.
          + split; auto. splits.
            * intros. etransitivity; [etransitivity|]; [| apply TKS |]; [reflexivity|..].
              split; intros; desc.
              ** destruct (decide (ρ0 = ρ)) as [-> | NEQ].
                 *** exists ρ, true. rewrite lookup_insert. congruence.
                 *** exists ρ0, e. rewrite lookup_insert_ne; auto.
              ** destruct (decide (ρ0 = ρ)) as [-> | NEQ].
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
          + split; auto. splits.
            * intros. etransitivity; [etransitivity|]; [| apply TKS |]; [reflexivity|..].
              split; intros; desc.
              ** exists ρ0, e. destruct (decide (ρ0 = ρ)); 
                   subst; simpl_li; [congruence| auto]. 
              ** destruct (decide (ρ0 = ρ)); subst; simpl_li; inversion H; eauto.
            * intros. destruct (decide (ρ0 = ρ)); subst; simpl_li; try congruence.
              eapply TKo; eauto.
            * intros.
              destruct (decide (ρ1 = ρ)), (decide (ρ2 = ρ)).
              all: subst; simpl_li; inversion R1; inversion R2; subst; auto. 
              all: eapply UNIQ; eauto.
      Qed.


      Lemma tl_valid_trace_states i st (ITH: tr S!! i = Some st):
        tl_state_wf st. 
      Proof using LEN FROM_INIT VALID.
        gd st. induction i.
        { intros.
          destruct (FROM_INIT _ ITH) as [n ->].
          rewrite /tl_init_st. 
          red. splits; auto.
          - split; [lia| ]. intros [ρ RMρ]. desc.
            apply lookup_gset_to_gmap_Some in RMρ. desc. congruence.
          - intros. rewrite lookup_gset_to_gmap_Some in H. by desc.
          - intros. rewrite lookup_gset_to_gmap_Some in R1. by desc. }

        intros [rm' t' o']. rewrite -Nat.add_1_r. intros ITH'.
        forward eapply trace_lookup_dom_strong with (i := i) as [_ ITH]; eauto.
        specialize_full ITH; [eapply state_lookup_dom; eauto| ]. desc.
        forward eapply mtrace_valid_steps' as STEP; eauto.
        apply state_label_lookup in ITH. desc.
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
      Proof using LEN VALID.
        apply Nat.le_sum in LE as [d ->].
        gd i. gd st. gd st'. induction d.
        { intros. rewrite Nat.add_0_r in JTH.
          assert (st' = st) as -> by congruence. lia. }
        intros. rewrite Nat.add_succ_r -Nat.add_1_r in JTH.
        forward eapply trace_lookup_dom_strong with (i := (i + d)) as [_ J'TH]; eauto.
        specialize_full J'TH; [eapply state_lookup_dom; eauto| ]. desc.
        forward eapply mtrace_valid_steps' as STEP; eauto. 
        apply step_counters_mono in STEP; auto.  
        apply state_label_lookup in J'TH as (J'TH_ & JTH_ & LBL).
        assert (st'0 = st') as -> by congruence.
        specialize (IHd _ _ _ ITH J'TH_). lia. 
      Qed.
      
      Lemma has_lock_kept (ρ: tl_role) (o: nat):
        @label_kept_state ExtTL_FM 
          (fun st => tl_state_wf st /\ owner st = o /\ has_lock_st ρ st) (inl ρ).
      Proof using LEN FROM_INIT.
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
      Proof using LEN FROM_INIT.
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
      Proof using LEN FROM_INIT.
        red. intros. destruct Ps as (b & bo & WF & TKn & OWNER & OWo).
        forward eapply (has_lock_kept ρo (owner st) _ _ _ _ _ STEP). Unshelve.
        3: { eauto. }
        2: { splits; eauto. red. eauto. rewrite OWo. eauto. }
        intros (WF' & OWNER' & LOCK'). 
        
        destruct (decide (ρo = ρ)) as [-> | NEQ].
        { assert (n = owner st /\ bo = b) as [-> ->] by (split; congruence). 
          red in LOCK'. desc. 
          exists e, e. splits; eauto; congruence. }

        assert (owner st < n /\ b = true) as [LT ->].
        { destruct st as [o_ t rm]. simpl in *. subst o_.  
          destruct WF as (LE & TKS & TKO & UNIQ).
          destruct (decide (n = o)) as [-> | NEQ'].
          { destruct NEQ. eapply UNIQ; eauto. }
          specialize (TKS n). apply proj2 in TKS. specialize_full TKS; [eauto|]. 
          destruct b; [split; [lia|auto]| ].
          by apply TKO in TKn. }

        destruct LOCK' as [bo' LOCK'].
        exists true, bo'. splits; eauto; try congruence.  

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
      Proof using LEN FROM_INIT.
        red. intros. destruct Ps as (b & WF & TKn & OWNER & OWo).
        forward eapply (has_lock_active_kept ρo (owner st) _ _ _ _ _ STEP). Unshelve.
        3: { eauto. }
        2: { splits; eauto. rewrite OWo. eauto. }
        intros (WF' & OWNER' & LOCK'). 
        
        destruct (decide (ρo = ρ)) as [-> | NEQ].
        { assert (n = owner st) as -> by congruence.
          exists true. splits; eauto; congruence. } 

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

      
      Let tl_eventual_release := eventual_release ExtTL has_lock_st active_st.


      Lemma lock_eventually_released i ρ st ρ0 m
        (EV_REL: tl_eventual_release tr ρ0 m)
        (ITH: tr S!! i = Some st)
        (LOCK: has_lock_st ρ st)
        (R0: ρ = ρ0 -> i < m):
        ∃ n st', 
          i < n ∧ tr S!! n = Some st' ∧ owner st' = owner st + 1 /\
          can_lock_st ρ st' ∧ ¬ active_st ρ st'. 
      Proof using VALID LEN FROM_INIT FAIR.
        destruct st as [o t rm].
        (* pose proof (eventual_release_strenghten _ _ EV_REL _ _ _ ITH LOCK) as HH. *)
        forward eapply eventual_release_strenghten as HH; eauto.
        { apply active_st_dec. }
        rename HH into EV_REL'.
        (* specialize_full EV_REL'. *)
        (* { intros ->. auto. } *)
        destruct EV_REL' as (k & (st' & KTH & LEik & ENρo) & MIN).
        
        forward eapply steps_keep_state with (i := i) (j := k) (k := k) as LOCK'.
        3: { apply has_lock_kept. }
        all: eauto. 
        { eexists. split; [apply ITH|]. split; eauto.
          eapply tl_valid_trace_states; eauto. } 
        { intros. destruct IKJ as [[v ->]%Nat.le_sum KJ]. 
          intros ->. enough (k <= i + v); [lia| ]. apply MIN.
          forward eapply (proj1 (label_lookup_states tr (i + v))) as HH; eauto.
          destruct HH as [[st1 ST1] [st2 ST2]].
          eexists. splits; [eauto| lia|].
          forward eapply mtrace_valid_steps' as STEP; eauto.
          { eapply state_label_lookup; eauto. }
          inversion STEP; subst. 
          apply active_st_enabled.
          eapply fm_live_spec; eauto. }
        destruct LOCK' as (WF' & OW'o & LOCK'). simpl in *.
        
        forward eapply (kept_state_fair_step VALID).
        { apply (has_lock_active_kept ρ o). }
        all: eauto.
        { simpl. intros. red. simpl.
          rewrite /ext_live_roles. apply elem_of_union_l. apply elem_of_map_2.
          apply active_st_enabled. red. destruct Pst as (_ & _ & ?). eauto. }
        { splits; eauto. destruct LOCK', ENρo. congruence. }
        intros (j & st'' & HH & JTH & WF & OW''o & RM''ρo).
        destruct HH as [[LEkj STEP] MIN']. 
        
        forward eapply (proj1 (label_lookup_states tr j)) as [_ [st''' J'TH]]; eauto.
        forward eapply mtrace_valid_steps' as STEP''; eauto. 
        { eapply state_label_lookup; eauto. }

        exists (j + 1), st'''. split; [lia| ]. split; auto.
        inversion STEP''; subst. inversion STEP0; subst; simpl in *.
        { congruence. }
        { rewrite RM''ρo in R. inversion R. lia. }
        assert (role_map st''0 !! ρ = Some (tl_L, false)) as R'.
        { subst st'1 st'0 st''0. simpl in *.
          rewrite /advance_next. simpl.
          destruct role_of_dec as [[? ?] | ?]. 
          2: { simpl. by rewrite lookup_insert. }
          simpl. rewrite lookup_insert_ne.
          2: { intros ->. rewrite lookup_insert in e. congruence. }
          by rewrite lookup_insert. }
        rewrite /can_lock_st /active_st. rewrite R'. splits.
        { subst st'1 st'0 st''0. simpl in *.
          rewrite /advance_next. simpl.
          destruct role_of_dec as [[? ?] | ?]; simpl; lia. }
        { eauto. }
        intros [? ?]. congruence. 
      Qed.

      Lemma lock_eventually_acquired_iteration o t rm ρ i d
        (ST: tr S!! i = Some <{ o, t, rm }>)
        (R: rm !! ρ = Some (tl_U (S o + d), true))
        (EV_REL: tl_eventual_release tr ρ i):
        ∃ (n : nat) (st': tl_st),
          let e' := if (decide (d = 0)) then false else true in
          i < n ∧ tr S!! n = Some st' ∧ owner st' = o + 1 /\
          role_map st' !! ρ = Some (tl_U (S o + d), e'). 
      Proof using VALID LEN FROM_INIT FAIR.
        assert (exists ρo, has_lock_st ρo <{ o, t, rm }>) as [ρo LOCK].
        { apply tl_valid_trace_states in ST as (LE & TKS & _).
          apply Lt.le_lt_or_eq_stt in LE as [LT | ->].
          2: { enough (S t + d < t); [lia| ]. apply TKS. eauto. }
          specialize (TKS o). apply proj1 in TKS. specialize_full TKS; auto. }
        assert (ρo ≠ ρ) as NEQ.
        { intros ->. red in LOCK. desc. rewrite R in LOCK.
          inversion LOCK. lia. }
        
        (* pose proof (eventual_release_strenghten _ _ EV_REL _ _ _ ST LOCK) as HH. *)
        forward eapply eventual_release_strenghten as HH; eauto.
        { apply active_st_dec. }
        { congruence. }        

        rename HH into EV_REL'. specialize_full EV_REL'.
        (* { intros ->. rewrite /has_lock_st in LOCK. destruct LOCK. *)
        (*   simpl in H. rewrite R in H. inversion H. lia. } *)
        destruct EV_REL' as (k & (st' & KTH & LEik & ENρo) & MINk).
        
        forward eapply steps_keep_state with (i := i) (j := k) (k := k) as LOCK'.
        3: { apply (lock_wait_kept ρ ρo). }
        all: eauto.
        { eexists. split; [apply ST|]. 
          red in LOCK. desc. do 2 eexists. splits; eauto. 
          eapply tl_valid_trace_states; eauto. }
        { intros. destruct IKJ as [[v ->]%Nat.le_sum KJ].
          intros ->. enough (k <= i + v); [lia| ]. apply MINk.
          forward eapply (proj1 (label_lookup_states tr (i + v))) as HH; eauto.
          destruct HH as [[st1 ST1] [st2 ST2]].
          eexists. splits; [eauto| lia|].
          (* forward eapply (mtrace_valid_steps' tr (i + v)) as STEP; eauto. *)
          forward eapply mtrace_valid_steps' as STEP; eauto.
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
          apply active_st_enabled. red. desc. eauto. }
        { splits; eauto. }
        intros (j & st'' & [[LEkj STEPj] MINj] & JTH & b_ & WF'' & RMρ'' & RMρo'' & OW'').
        assert (b_ = true) as ->.
        { destruct b_; auto.
          destruct st''; simpl in *. destruct WF'' as (? & ? & TKo'' & _).
          apply TKo'' in RMρ''. lia. }

        forward eapply (proj1 (label_lookup_states tr j)) as [_ [st''' J'TH]]; eauto.
        exists (j + 1), st'''. split; [lia| ]. split; [auto| ].
        forward eapply (mtrace_valid_steps' VALID j) as STEP; eauto.
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
        destruct (decide (ρ = ρ')) as [-> | ?].
        { rewrite lookup_insert.
          rewrite RMρ'' in e. inversion e. 
          destruct (decide (d = 0)) as [-> | ?]; [| lia]; auto. }
        do 2 (rewrite lookup_insert_ne; auto).
        destruct (decide (d = 0)) as [-> | ?]; auto.
        rewrite Nat.add_0_r -Nat.add_1_r -OW'' in RMρ''.
        destruct n. eapply WF''; eauto.
      Qed.
        
      Lemma lock_eventually_acquired o t rm ρ i wt 
        (ST: tr S!! i = Some <{ o, t, rm }>)
        (WAIT: o ≠ wt)
        (R: rm !! ρ = Some (tl_U wt, true))
        (EV_REL: forall j (LE: i <= j), tl_eventual_release tr ρ j):
        ∃ (n : nat) (st' : tl_st),
          i < n ∧ tr S!! n = Some st' ∧ has_lock_st ρ st' ∧ ¬ active_st ρ st'.
      Proof using VALID LEN FROM_INIT FAIR.
        assert (o < wt) as LT.
        { apply PeanoNat.Nat.le_neq. split; auto. 
          apply tl_valid_trace_states in ST. apply ST. eauto. }
        apply Nat.le_succ_l in LT. apply Nat.le_sum in LT as [d ->]. clear WAIT.
        gd i. gd o. gd rm. gd t. induction d.
        { intros. eapply lock_eventually_acquired_iteration in ST; eauto.
          simpl in ST. desc. rewrite Nat.add_0_r -Nat.add_1_r in ST2. 
          rewrite /has_lock_st /active_st. 
          exists n, st'. rewrite ST1. splits; eauto.
          intros [? ?]. rewrite ST2 in H.
          rewrite decide_True in H; done. }
        intros. eapply lock_eventually_acquired_iteration in ST; eauto.
        simpl in ST. desc.
        destruct st'. simpl in *.
        replace (S (o + S d)) with (S (S o) + d) in ST2 by lia.
        rewrite decide_False in ST2; [| lia]. 
        eapply IHd in ST2.
        2: { rewrite -Nat.add_1_r -ST1. eauto. }
        2: { intros. apply EV_REL. lia. }
        desc. exists n0, st'. splits; eauto. lia. 
      Qed.


      Theorem tl_progress ρ i st
        (ITH: tr S!! i = Some st)
        (CAN_LOCK: can_lock_st ρ st)
        (ACT: active_st ρ st)
        (EV_REL: forall j (LE: i <= j), tl_eventual_release tr ρ j):
        exists n st', i < n /\ tr S!! n = Some st' /\ has_lock_st ρ st' /\
                   ¬ active_st ρ st'.
      Proof using VALID LEN FAIR FROM_INIT.
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
        forward eapply (mtrace_valid_steps' VALID (i + d)) as TRANS; auto. 
        { by eapply state_label_lookup. }
          
        simpl in TRANS. inversion TRANS as [? ? ? TRANS'| ]; subst.
        inversion TRANS'; subst; simpl in *.
        all: try by rewrite RMρ' in R.
        destruct (decide (o = t)) as [<- | WAIT]. 
        { exists (i + d + 1). eexists. splits; [lia|..]; try by eauto.
          - red. eexists. simpl. rewrite lookup_insert. eauto. 
          - rewrite /active_st. simpl. rewrite lookup_insert. intros [? [=]]. }

        eapply lock_eventually_acquired in ST'''.
        - desc. do 2 eexists. splits.
          2-4: by eauto. lia. 
        - apply WAIT.
        - rewrite lookup_insert. eauto.
        - intros. apply EV_REL. lia. 
      Qed. 

    End ProgressPropertiesImpl. 

    Let tl_is_init st := exists n, st = tl_init_st n. 
    
    Instance TLFairLock: 
      FairLock ExtTL can_lock_st has_lock_st active_st tl_is_init.
    Proof.
      constructor. red. intros.
      pose proof (trace_has_len tr) as [len LEN]. 
      eapply tl_progress; eauto.
    Qed.     

  End ProgressProperties. 

End Model.
                       
