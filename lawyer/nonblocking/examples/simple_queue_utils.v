From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From heap_lang Require Import lang. 
From fairness Require Import utils.


Close Scope Z.

Section MaxExact.

  Class MaxExactPreG Σ := {
    me_pre_in :: inG Σ (prodUR (excl_authUR nat) mono_natUR);
  }.

  Class MaxExactG Σ := {
    me_pre :: MaxExactPreG Σ;
    me_γ: gname;
  }.
  

  (** explicitly add ◯ None to justify me_auth_lb *)
  Definition me_auth `{MaxExactG Σ} (n: nat): iProp Σ := own me_γ (●E n ⋅ ◯ None, ●MN n). 
  Definition me_exact `{MaxExactG Σ} (n: nat): iProp Σ := own me_γ (◯E n, ◯MN n). 
  Definition me_lb `{MaxExactG Σ} (n: nat): iProp Σ := own me_γ (◯ None, ◯MN n).

  Lemma max_exact_init `{MaxExactPreG Σ} n:
    ⊢ |==> ∃ (_: MaxExactG Σ), me_auth n ∗ me_exact n ∗ me_lb n.
  Proof using.
    iMod (own_alloc (●E n ⋅ ◯E n, ●MN n ⋅ ◯MN n)) as (γ) "X".
    { apply pair_valid. split.
      - apply auth_both_valid_2; done.   
      - apply mono_nat_both_valid. done. }
    iModIntro. iExists {| me_γ := γ; |}.
    rewrite /me_auth /me_exact /me_lb. rewrite -!own_op.
    rewrite -!pair_op. simpl.
    rewrite !ucmra_unit_right_id.
    rewrite -mono_nat_lb_op Nat.max_id.
    done.
  Qed.    

  Context `{MaxExactG Σ}.

  Lemma me_auth_save n:
    me_auth n -∗ me_lb n.
  Proof using.
    rewrite /me_auth /me_lb. iIntros "AUTH".
    iApply own_mono; [| done].
    apply pair_included. split.
    - apply cmra_included_r.
    - rewrite mono_nat_auth_lb_op. apply cmra_included_r.
  Qed.

  Lemma me_auth_lb n m:
    me_auth n -∗ me_lb m -∗ ⌜ m <= n ⌝.
  Proof using.
    iIntros "X Y". iCombine "X Y" as "X".
    iDestruct (own_valid with "X") as %V. 
    rewrite pair_valid in V. apply proj2 in V.
    iPureIntro. by apply mono_nat_both_valid.
  Qed.

  Lemma me_auth_exact n m:
    me_auth n -∗ me_exact m -∗ ⌜ m = n ⌝.
  Proof using.
    iIntros "X Y". iCombine "X Y" as "X".
    iDestruct (own_valid with "X") as %V. 
    rewrite pair_valid in V. apply proj1 in V.
    iPureIntro.
    rewrite ucmra_unit_right_id in V.
    symmetry. eapply excl_auth_agree_L; eauto. 
  Qed.

  Lemma me_exact_excl n m:
    me_exact n -∗ me_exact m -∗ False.
  Proof using.
    rewrite /me_exact. 
    rewrite bi.wand_curry -own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    rewrite pair_valid in V. apply proj1 in V. simpl in V.
    by apply excl_auth_frag_op_valid in V.
  Qed.

  Lemma me_update n m k
    (LE: n <= k):
    me_auth n -∗ me_exact m ==∗ me_auth k ∗ me_exact k.
  Proof using.
    rewrite /me_auth /me_exact.
    rewrite bi.wand_curry -!own_op.
    iApply own_update. 
    rewrite !ucmra_unit_right_id.
    rewrite -!pair_op.
    etrans.
    - eapply (prod_update _ (_, _)); simpl; [| reflexivity]. 
      apply (excl_auth_update _ _ k).
    - eapply (prod_update _ (_, _)); simpl; [reflexivity| ].
      rewrite -mono_nat_auth_lb_op.
      etrans; [| apply cmra_update_op_l].
      apply cmra_update_op; [| reflexivity].
      by apply mono_nat_update.
  Qed. 

End MaxExact.


Section ListToIMap.
  Context {A: Type}.

  (* TODO: rename *)
  Definition list_to_imap: list A -> gmap nat A :=
    list_to_map ∘ imap pair.

  Local Lemma helper (l: list A) i k:
    l !! i = (list_to_map (imap (pair ∘ (plus k)) l): gmap nat A) !! (k + i).
  Proof using.
    generalize dependent i. generalize dependent k.
    induction l.
    { set_solver. }
    intros. simpl. destruct i.
    { simpl. by rewrite lookup_insert. }
    simpl. rewrite lookup_insert_ne; [| lia].
    rewrite -Nat.add_succ_comm. 
    erewrite IHl. do 2 f_equal. 
    apply imap_ext. simpl. intros. f_equal. lia.
  Qed.

  Lemma list_to_imap_spec l:
    forall i, list_to_imap l !! i = l !! i.
  Proof using.
    intros. rewrite /list_to_imap /compose.
    symmetry. by rewrite (helper _ _ 0).
  Qed.

  Lemma list_to_imap_dom l:
    dom (list_to_imap l) = set_seq 0 (length l).
  Proof using.
    apply set_eq. intros i.
    rewrite elem_of_set_seq elem_of_dom.
    rewrite list_to_imap_spec. rewrite lookup_lt_is_Some. lia.
  Qed.    

End ListToIMap.


Section HistQueue.

  Definition Node: Set := val * loc.
  Definition HistNode: Set := loc * Node. 
  Definition HistQueue := list HistNode.

  Class HistQueuePreG Σ := {
      hq_pre_map :: inG Σ (authUR (gmapUR nat (agreeR HistNode)));
  }.
  
  Class HistQueueG Σ := {
      hq_PreG :: HistQueuePreG Σ;
      hq_γ__map: gname;
  }.

  Context `{HistQueueG Σ}. 
  
  Definition ith_node (i: nat) (nd: HistNode): iProp Σ :=
    own hq_γ__map (◯ {[ i := to_agree nd ]}).

  Definition hq_auth (hq: HistQueue): iProp Σ := 
    own hq_γ__map (● (to_agree <$> (list_to_imap hq): gmapUR nat (agreeR HistNode))) ∗
    ([∗ list] i ↦ hn ∈ hq, ith_node i hn). 

  Definition hq_auth_get_ith i nd hq
    (ITH: hq !! i = Some nd):
    hq_auth hq -∗ ith_node i nd.
  Proof using.
    iIntros "[AUTH #FRAGS]". iFrame "#∗".
    rewrite big_sepL_lookup_acc; eauto.
    by iDestruct "FRAGS" as "[??]".
  Qed.

  Lemma hq_auth_lookup hq i hn:
    hq_auth hq -∗ ith_node i hn -∗ ⌜ hq !! i = Some hn ⌝.
  Proof using.
    iIntros "[AUTH _] #ITH".
    rewrite /ith_node. iCombine "AUTH ITH" as "OWN".
    iDestruct (own_valid with "OWN") as %V%auth_both_valid_discrete.
    iPureIntro.

    (* TODO: make a lemma, unify with similar proof in signal_map *)
    destruct V as [SUB V].
    apply singleton_included_l in SUB as (hn_ & ITH & LE).
    rewrite Some_included_total in LE.
    destruct (to_agree_uninj hn_) as [y X].
    { eapply lookup_valid_Some; eauto. done. }
    rewrite -X in LE. apply to_agree_included in LE. 
    rewrite -X in ITH.    
    eapply leibniz_equiv.       
    rewrite lookup_fmap in ITH.
    rewrite -LE in ITH.    
    apply fmap_Some_equiv in ITH as (?&ITH&EQ).
    apply to_agree_inj in EQ. rewrite EQ.
    apply leibniz_equiv_iff.
    erewrite list_to_imap_spec in ITH; eauto.
  Qed.

End HistQueue.


Section ReadProtocol.

  Inductive read_state_proc := rsp_going | rsp_completed | rsp_protected. 

  (* TODO: rename rs_canceled to rs_prevented *)
  Inductive read_state :=
    rs_init | rs_aborted | rs_canceled | rs_proc (orsp: option read_state_proc).

  Definition read_state_proc_cmra: cmra :=
    let au := agreeR unit in csumR (exclR unit) (csumR au au). 

  Definition read_state_cmra: cmra :=
    csumR (exclR unit) $
    csumR (agreeR unit) $
    csumR (agreeR unit) $
    optionR read_state_proc_cmra. 
    
  Definition rsp2cmra (rsp: read_state_proc): read_state_proc_cmra :=
    match rsp with 
    | rsp_going => Cinl $ Excl ()
    | rsp_completed => Cinr $ Cinl $ to_agree ()
    | rsp_protected => Cinr $ Cinr $ to_agree ()
    end.
    
  Definition rs_p0: read_state := rs_proc None. 

  Definition rs2cmra (rs: read_state): read_state_cmra :=
    match rs with
    | rs_init => Cinl $ Excl ()
    | rs_aborted => Cinr $ Cinl $ to_agree ()
    | rs_canceled => Cinr $ Cinr $ Cinl $  to_agree ()
    | rs_proc None => Cinr $ Cinr $ Cinr $ None
    | rs_proc (Some rsp) => Cinr $ Cinr $ Cinr $ Some (rsp2cmra rsp)
    end.

  Definition rs_wip p := p = rs_init \/ p = rs_proc (Some rsp_going). 
  Definition rs_fin p := 
    p = rs_aborted \/ p = rs_canceled \/ p = rs_proc (Some rsp_completed) \/ p = rs_proc (Some rsp_protected). 
  
  Lemma rsp_mut_excl rsp1 rsp2
    (NEQ: rsp1 ≠ rsp2):
    ¬ ✓ (rsp2cmra rsp1 ⋅ rsp2cmra rsp2).
  Proof using.
    destruct rsp1, rsp2; simpl; intros V; done.
  Qed.

  Global Instance rsp_dec: EqDecision read_state_proc.
  Proof. 
    red. intros [] []; (by right) || (by left). 
  Qed. 

  Global Instance rs_dec: EqDecision read_state.
  Proof. 
    red. intros [] []; try (by right) || (by left).
    solve_decision. 
  Qed.

  Lemma rsp0_proc rp:
    ✓ (rs2cmra rs_p0 ⋅ rs2cmra rp) -> exists orsp, rp = rs_proc orsp.
  Proof using.
    intros ?. destruct rp; try done. eauto.
  Qed.    

  Global Instance rsp2cmra_inj: Inj eq equiv rsp2cmra.
  Proof using.
    red. intros [] []; simpl.
    all: try by set_solver.
    all: try by (intros X; inversion X).
    all: try by (intros X; inversion X; subst; inversion H1).
  Qed.

  Local Ltac csum_option_inv_act H := inversion H; subst; clear H. 

  Ltac csum_option_inv := repeat (try intros ?; match goal with
      | [H : Cinl _ ≡ _ |- _  ] => csum_option_inv_act H
      | [H : Cinr _ ≡ _ |- _  ] => csum_option_inv_act H
      | [H : Some _ ≡ _ |- _  ] => csum_option_inv_act H
      | [H : None ≡ _ |- _  ] => csum_option_inv_act H
      (* | [H : Cinl _ = _ |- _  ] => csum_option_inv_act H *)
      (* | [H : Cinr _ = _ |- _  ] => csum_option_inv_act H *)
      (* | [H : Some _ = _ |- _  ] => csum_option_inv_act H *)
      (* | [H : None = _ |- _  ] => csum_option_inv_act H *)
  end). 

  Global Instance rs2cmra_inj: Inj eq equiv rs2cmra.
  Proof using.    
    clear. 
    red. intros [] []; simpl.
    all: try by csum_option_inv.
    all: destruct orsp; try by csum_option_inv. 
    all: destruct orsp0; try by csum_option_inv.
    csum_option_inv. repeat f_equal.
    eapply rsp2cmra_inj; eauto.
  Qed. 

  Inductive rs_le : read_state -> read_state -> Prop :=
  | rs_le_rsp_None rsp : rs_le (rs_proc None) (rs_proc (Some rsp))
  | rs_le_refl rs : rs_le rs rs
  .

  Lemma rs2cmra_inv_init rs x:
    rs2cmra rs = Cinl x -> rs = rs_init /\ x = Excl (). 
  Proof.
    destruct rs; simpl.
    all: intros [=]; subst; eauto.  
    destruct orsp; done. 
  Qed.

  Lemma rs2cmra_inv_abort rs x:
    rs2cmra rs = Cinr (Cinl x) -> rs = rs_aborted /\ x = to_agree (). 
  Proof.
    destruct rs; intros [=]; simpl; eauto.
    destruct orsp; done. 
  Qed.

  Lemma rs2cmra_inv_cancel rs x:
    rs2cmra rs = Cinr $ Cinr $ Cinl x -> rs = rs_canceled /\ x = to_agree (). 
  Proof.
    destruct rs; intros [=]; simpl; eauto.
    destruct orsp; done. 
  Qed.

  Lemma rs2cmra_inv_proc_None rs:
    rs2cmra rs = Cinr $ Cinr $ Cinr None -> rs = rs_p0. 
  Proof.
    destruct rs; simpl; eauto.
    all: intros [=].
    destruct orsp; try intros [=]; done. 
  Qed.

  Lemma rs2cmra_inv_proc_Some rs x:
    rs2cmra rs = Cinr $ Cinr $ Cinr $ Some x -> exists y, rs = rs_proc (Some y) /\ x = rsp2cmra y.
  Proof.
    destruct rs; simpl; eauto.
    all: intros [=].
    destruct orsp; try done.
    inversion H0. subst. eauto. 
  Qed.

  Lemma rsp2cmra_inv_going rsp x:
    rsp2cmra rsp = Cinl x -> rsp = rsp_going /\ x = Excl (). 
  Proof. destruct rsp; by intros [=]. Qed. 

  Lemma rsp2cmra_inv_completed rsp x:
    rsp2cmra rsp = Cinr $ Cinl x -> rsp = rsp_completed /\ x = to_agree (). 
  Proof. destruct rsp; try by intros [=]. Qed. 

  Lemma rsp2cmra_inv_protected rsp x:
    rsp2cmra rsp = Cinr $ Cinr x -> rsp = rsp_protected /\ x = to_agree (). 
  Proof. destruct rsp; try by intros [=]. Qed. 

  Lemma rsp_incl x y:
    Some (rsp2cmra x) ≼ Some (rsp2cmra y) <-> x = y.
  Proof using.
    rewrite Some_csum_included.
    repeat (setoid_rewrite Some_csum_included). 
    split.
    2: { intros ->. destruct y; simpl. 
         - right. left. eauto.
         - do 2 right. do 2 eexists.
           do 2 (split; eauto).
           right. left. eauto. 
         - do 2 right. do 2 eexists.
           do 2 (split; eauto).
           do 2 right. eauto. }
    intros [BOT | [L | R]].
    { destruct y; done. }
    { destruct L as (?&?&X&Y&INCL).
      apply rsp2cmra_inv_going in X as [-> ->], Y as [-> ->]. by subst. }
    destruct R as (?&?&X&Y&INCL).
    destruct INCL as [BOT | [L | R]].
    { subst. by destruct y. }
    - destruct L as (?&?&X'&Y'&INCL). subst. 
      apply rsp2cmra_inv_completed in X as [-> ->], Y as [-> ->]. by subst.
    - destruct R as (?&?&X'&Y'&INCL). subst. 
      apply rsp2cmra_inv_protected in X as [-> ->], Y as [-> ->]. by subst.
  Qed.

  Lemma rs_le_incl rs1 rs2:
    rs_le rs1 rs2 <-> Some (rs2cmra rs1) ≼ Some (rs2cmra rs2). 
  Proof using.
    destruct (decide (rs1 = rs2)) as [-> | NEQ].
    { split; intros.
      - reflexivity.
      - constructor. }
    repeat (setoid_rewrite Some_csum_included).
    repeat (setoid_rewrite Some_included).
    repeat (setoid_rewrite Excl_included).
    setoid_rewrite option_included.
    repeat (setoid_rewrite agree_included).
    
    split; intros.
    { inversion H; subst; [| done].
      simpl.
      do 2 right. do 2 eexists. repeat (split; eauto).
      do 2 right. do 2 eexists. repeat (split; eauto).
      do 2 right. do 2 eexists. repeat (split; eauto). }
    destruct H as [BOT | [L | R]].
    { (destruct rs2; simpl in BOT); try congruence.
      destruct orsp; congruence. }
    { destruct L as (?&?&?&?&?).
      apply rs2cmra_inv_init in H as [-> ->], H0 as [-> ->]. subst. done. }
    destruct R as (?&?&?&?&?).
    destruct H1 as [BOT | [L | R]].
    { subst. destruct rs2; simpl in H0; try set_solver.
      by destruct orsp. }
    { destruct L as (?&?&?&?&?). subst.
      apply rs2cmra_inv_abort in H as [-> ->], H0 as [-> ->]. subst. done. }
    destruct R as (?&?&?&?&?). subst.
    destruct H3 as [BOT | [L | R]].
    { subst. destruct rs2; simpl in H0; try set_solver.
      by destruct orsp. }
    { destruct L as (?&?&?&?&?). subst.
      apply rs2cmra_inv_cancel in H as [-> ->], H0 as [-> ->]. subst. done. }
    destruct R as (?&?&?&?&?). subst.
    destruct x.
    2: { apply rs2cmra_inv_proc_None in H. subst.
         destruct x0.
         - apply rs2cmra_inv_proc_Some in H0 as (?&->&->).
           constructor.
         - apply rs2cmra_inv_proc_None in H0. by subst. }
    apply rs2cmra_inv_proc_Some in H as (?&->&->).
    destruct x0.
    2: { apply rs2cmra_inv_proc_None in H0. subst.
         inversion H3 as [? | [? | ?]].
         1, 2: by inversion H.
         set_solver. }
    apply rs2cmra_inv_proc_Some in H0 as (?&->&->).
    inversion H3 as [? | [? | ?]].
    ** inversion H. subst. apply rsp2cmra_inj in H2. subst. constructor.
    ** inversion H.
    ** destruct H as (?&?&[=]&[=]&?). subst.
       destruct H4 as [H4 | RSP].
       *** apply rsp2cmra_inj in H4. by subst.
       *** apply Some_included_mono in RSP.
           apply rsp_incl in RSP. subst. constructor.
  Qed.

  Lemma rs_le_incl' x y:
    rs2cmra x ≼ rs2cmra y -> rs_le x y. 
  Proof using.
    intros. apply rs_le_incl. by apply Some_included_mono.
  Qed.

  (* Ltac csum_valid_simpl := *)
  (*   repeat (rewrite Cinl_valid || rewrite Cinr_valid || rewrite -Some_op Some_valid || rewrite op_None_right_id || rewrite op_None_left_id). *)
  Ltac csum_valid_simpl := repeat (rewrite
    ?Cinl_valid ?Cinr_valid 
    -?Some_op ?Some_valid
    ?op_None_right_id ?op_None_left_id
  ).

  Lemma rsp2cmra_valid rsp: ✓ rsp2cmra rsp.
  Proof using. destruct rsp; simpl; csum_valid_simpl; done. Qed. 

  Lemma rs2cmra_valid rs: ✓ rs2cmra rs.
  Proof using.
    destruct rs; simpl; csum_valid_simpl; try done.
    destruct orsp; csum_valid_simpl; try done.
    apply rsp2cmra_valid.
  Qed.

  Inductive rsp_step : read_state_proc -> read_state_proc -> Prop :=
  | rsp_refl rsp : rsp_step rsp rsp
  | rsp_going_protected : rsp_step rsp_going rsp_protected
  | rsp_going_completed : rsp_step rsp_going rsp_completed
  .

  Local Ltac contra_valid := 
    match goal with
    | H : forall mz, valid (?R1 ⋅? mz) → valid (?R2 ⋅? mz) |- _ =>
        specialize (H (Some R1))
    end. 

  Lemma rsp_step_update rsp1 rsp2:
    rsp_step rsp1 rsp2 <-> rsp2cmra rsp1 ~~> rsp2cmra rsp2.
  Proof using.
    split.
    { intros STEP. inversion STEP.
      - subst. reflexivity.
      - subst. simpl. apply cmra_update_exclusive. done.
      - subst. simpl. apply cmra_update_exclusive. done. }
    intros STEP. destruct rsp1, rsp2; try constructor || tauto.
    all: simpl in STEP; rewrite cmra_discrete_update in STEP;
      contra_valid; simpl in STEP;
      repeat (rewrite -?Cinr_op -?Cinl_op in STEP);
      ospecialize * STEP; [| by csum_valid_simpl];
      by destruct STEP.
  Qed. 

  Inductive rs_step : read_state -> read_state -> Prop :=
  | rs_refl rs : rs_step rs rs
  | rs_init_going : rs_step rs_init (rs_proc (Some rsp_going))
  | rs_init_abort : rs_step rs_init rs_aborted
  | rs_init_cancel : rs_step rs_init rs_canceled
  | rs_going_protected rsp1 rsp2 (RSP_STEP: rsp_step rsp1 rsp2) :
    rs_step (rs_proc (Some rsp1)) (rs_proc (Some rsp2))
  . 

  (* TODO: don't want to deal with updates to None rsp
     and arbitrary jumps from init to cancel/prot *)
  Lemma rs_step_update rs1 rs2:
    (* rs_step rs1 rs2 <-> rs2cmra rs1 ~~> rs2cmra rs2. *)
    rs_step rs1 rs2 -> rs2cmra rs1 ~~> rs2cmra rs2.
  Proof using.
    intros STEP. inversion STEP.
    - subst. reflexivity.
    - subst. simpl. apply cmra_update_exclusive. done.
    - subst. simpl. apply cmra_update_exclusive. done.
    - subst. simpl. apply cmra_update_exclusive. done.
    - subst. simpl.
      repeat (apply csum_update_r). apply option_update.
      by apply rsp_step_update.
  Qed. 

  Lemma rs_step_local_update rs1 rs2
    (RS_STEP: rs_step rs1 rs2):
    (Some (rs2cmra rs1), Some (rs2cmra rs1)) ~l~> (Some (rs2cmra rs2), Some (rs2cmra rs2)).
    Proof using. 
      inversion RS_STEP; subst; simpl.
      { reflexivity. }
      all: simpl; apply option_local_update; try by apply (exclusive_local_update).
      repeat apply csum_local_update_r. apply option_local_update.
      inversion RSP_STEP; subst; simpl.
      { reflexivity. }
      all: by apply (exclusive_local_update).
    Qed. 

  Inductive rsp_compat : read_state_proc -> read_state_proc -> Prop :=
  | rsp_cm_rsp_None : rsp_compat rsp_completed rsp_completed
  | rsp_cm_refl : rsp_compat rsp_protected rsp_protected
  .

  Lemma rsp_compat_valid rsp1 rsp2 :
    ✓ (rsp2cmra rsp1 ⋅ rsp2cmra rsp2) <-> rsp_compat rsp1 rsp2.
  Proof using.
    split. 
    - destruct rsp1, rsp2; csum_valid_simpl.
      all: done || constructor.
    - intros P. inversion P; subst; done.
  Qed.

  Inductive rs_compat : read_state -> read_state -> Prop :=
  | rs_cm_rsp_None_1 orsp : rs_compat (rs_proc None) (rs_proc orsp)
  | rs_cm_rsp_None_2 orsp : rs_compat (rs_proc orsp) (rs_proc None)
  | rs_cm_canc : rs_compat rs_canceled rs_canceled
  | rs_cm_abort : rs_compat rs_aborted rs_aborted
  | rs_cm_rsp_Some rsp1 rsp2 (RSP: rsp_compat rsp1 rsp2) :
    rs_compat (rs_proc (Some rsp1)) (rs_proc (Some rsp2))
  .

  Lemma rs_compat_valid rs1 rs2 :
    ✓ (rs2cmra rs1 ⋅ rs2cmra rs2) <-> rs_compat rs1 rs2.
  Proof using.
    split. 
    - destruct rs1, rs2; csum_valid_simpl.
      all: simpl; try done || constructor.
      all: destruct orsp; try destruct orsp0; try done || constructor.
      revert H. csum_valid_simpl. apply rsp_compat_valid.
    - intros P. inversion P; subst; simpl; try done.
      + destruct orsp; csum_valid_simpl; try done.
        apply rsp2cmra_valid.
      + destruct orsp; csum_valid_simpl; try done.
        apply rsp2cmra_valid.
      + csum_valid_simpl. by apply rsp_compat_valid. 
  Qed.

End ReadProtocol.


Section ReadsHistory.

  Class ReadHistPreG Σ := {
      rh_map_pre :: inG Σ (authUR (gmapUR nat (prodR
                                    (optionR $ prodR (agreeR nat) max_natUR)
                                    (optionR read_state_cmra)
                                    )))
  }.
  
  Class ReadHistG Σ := {
      rh_pre :: ReadHistPreG Σ;
      rh_γ__map: gname;
  }.

  Definition read_hist := gmap nat ((nat * nat) * read_state). 

  Definition read_hist_auth `{ReadHistG Σ} (hist: read_hist) :=
    let hist' := (((fun '(r, b, p) => (Some (to_agree r, MaxNat b), Some $ rs2cmra p)) <$> hist): gmapUR _ _) in
    let hist'' := (((fun '(r, b, p) => (Some (to_agree r, MaxNat b), None)) <$> hist): gmapUR _ _) in
    own rh_γ__map (● hist' ⋅ ◯ hist'').
  
  Definition ith_read `{ReadHistG Σ} i r b :=
    own rh_γ__map (◯ {[ i := (Some (to_agree r, MaxNat b), None) ]}).

  (* Lemma read_hist_init `{ReadHistPreG Σ} (hist: read_hist) *)
  (*   (RS_INIT: forall i op, hist !! i = Some op -> op.2 = rs_init): *)
  (*   ⊢ (|==> ∃ (_: ReadHistG Σ), read_hist_auth hist)%I. *)
  (* Proof using. *)
  (*   iMod (own_alloc (let hist' := (((fun '(r, b, p) => (Some (to_agree r, MaxNat b), Some p)) <$> hist): gmapUR _ _) in *)
  (*                    (● hist' ⋅ ◯ hist')) *)
  (*        ) as (γ) "X". *)
  (*   { simpl. apply auth_both_valid_2; [| done]. *)
  (*     (* HIDE: TODO: find/make lemma, fix similar thing in obligations_em *) *)
  (*     intros s. destruct lookup eqn:L; [| done]. *)
  (*     apply lookup_fmap_Some in L.  *)
  (*     destruct L as ([[l b] p]&<-&?). *)
  (*     apply Some_valid. split; apply Some_valid; try done. *)
  (*     apply RS_INIT in H0. simpl in H0. by subst. } *)
  (*   iModIntro. iExists {| rh_γ__map := γ; |}. done. *)
  (* Qed. *)

  Context `{ReadHistG Σ}. 

  Lemma ith_read_hist_compat hist i r b:
    read_hist_auth hist -∗ ith_read i r b -∗ ⌜ exists b' p, hist !! i = Some ((r, b'), p) /\ b <= b' ⌝.
  Proof using.
    (* TODO: can simplify this proof *)
    iIntros "[X _] Y". iCombine "X Y" as "X". iDestruct (own_valid with "X") as %V.
    iPureIntro.
    apply auth_both_valid_discrete in V as [SUB V].
    apply @singleton_included_l in SUB. destruct SUB as ([l' y]&SIG'&LE').
    
    (* TODO: make a lemma, unify with similar proof in signal_map and ?obligations_resources *)
    simpl in LE'. rewrite -SIG' in LE'.
    rewrite lookup_fmap in LE'.
    destruct (hist !! i) as [[[??]?]|] eqn:LL.
    all: rewrite LL in LE'; simpl in LE'.
    2: { apply option_included_total in LE' as [?|?]; set_solver. }
    rewrite Some_included_total in LE'.
    apply pair_included in LE' as [LE' _].
    rewrite Some_included_total in LE'.
    apply pair_included in LE' as [LE1 LE2].
    apply to_agree_included in LE1. rewrite leibniz_equiv_iff in LE1. subst.
    (****)

    do 2 eexists. split; [reflexivity| ].
    by rewrite max_nat_included /= in LE2. 
  Qed.

  Definition ith_rp i (rp: read_state) := 
    own rh_γ__map (◯ {[ i := (None, Some $ rs2cmra rp) ]}).

  Lemma ith_rp_hist_compat hist i rp:
    read_hist_auth hist -∗ ith_rp i rp -∗ ⌜ exists op, hist !! i = Some op /\ rs_le rp op.2 ⌝.
  Proof using.
    iIntros "[X _] Y". iCombine "X Y" as "X". iDestruct (own_valid with "X") as %V.
    iPureIntro.
    apply auth_both_valid_discrete in V as [SUB V].
    apply @singleton_included_l in SUB. destruct SUB as ([l' y]&SIG'&LE').

    (* TODO: make a lemma, unify with similar proof in signal_map and ?obligations_resources *)
    simpl in LE'. rewrite -SIG' in LE'.
    rewrite lookup_fmap in LE'.
    destruct (hist !! i) as [[[??]?]|] eqn:LL.
    all: rewrite LL in LE'; simpl in LE'.
    2: { apply option_included_total in LE' as [?|?]; set_solver. }
    rewrite Some_included_total in LE'.
    apply pair_included in LE' as [_ LE'].
    (****)
    eexists. split; [reflexivity| ]. simpl.     
    rewrite Some_included in LE'. destruct LE'.
    - apply rs2cmra_inj in H0. subst. econstructor. 
    - apply rs_le_incl'; eauto.
  Qed.

  Goal forall i r b, Persistent (ith_read i r b). apply _. Abort.

  Lemma read_hist_get hist i r b p
    (ITH: hist !! i = Some (r, b, p)):
    read_hist_auth hist -∗ ith_read i r b.
  Proof using.
    iIntros "AUTH". rewrite /read_hist_auth /ith_read.
    iApply (own_mono with "[$]").
    etrans; [| apply cmra_included_r].
    apply auth_frag_mono.
    apply singleton_included_l.
    rewrite lookup_fmap ITH. simpl.
    eexists. split; [reflexivity| ].
    rewrite Some_included_total.
    apply pair_included. split; auto.
  Qed.    

  Lemma ith_included i r b b'
    (LE: b' <= b):
  ith_read i r b -∗ ith_read i r b'.
  Proof using.
    iApply own_mono.
    apply auth_frag_mono.
    apply singleton_included_mono.
    apply pair_included. split; [| done].
    apply Some_included_total. apply pair_included.  
    split; [done| ].
    by apply max_nat_included.
  Qed.

  (** The ITH hypothesis (and in general not hiding the details of hist and hist')
      is needed, because the obtained hist' must satisfy read_hist_wf,
      proving which requires knowing the exact shape of hist'. *)
  (* TODO: try to make read_hist_wf part of read_hist? *)
  Lemma read_hist_update' hist i r ba pa b' p p'
    (RS_STEP: rs_step p p')
    (ITH: hist !! i = Some (r, ba, pa))
    (pb := if decide (p = rs_proc None) then pa else p')
    (hist' := <[i:=((r, max ba b'), pb)]> hist):
    read_hist_auth hist -∗ ith_rp i p ==∗
    read_hist_auth hist' ∗ ith_read i r (max ba b') ∗ ith_rp i p'.
  Proof using.
    iIntros "AUTH RP".
    iDestruct (ith_rp_hist_compat with "[$] [$]") as "(%x & %ITH' & %LE)".
    (* iDestruct (ith_read_hist_compat with "[$] [$]") as "(%ba & %pa & %ITH' & %_)". *)
    rewrite ITH in ITH'. inversion ITH'. subst. clear ITH'.    
    simpl in LE.

    assert ({pa = p /\ p ≠ rs_proc None} + {p = p' /\ p = rs_proc None}) as p_eq.
    { destruct p eqn:PP.
      1-3: by (left; inversion LE; inversion RS_STEP; subst; simpl; set_solver).
      destruct orsp.
      - left. inversion LE; inversion RS_STEP; subst; simpl; set_solver.
      - right. inversion LE; inversion RS_STEP; subst; simpl; set_solver. }

    iAssert (|==> read_hist_auth (<[i:=((r, max ba b'), pb)]> hist) ∗ ith_rp i p')%I with "[AUTH RP]" as "AUTH".
    2: { iMod "AUTH" as "[AUTH $]". 
         iDestruct (read_hist_get with "[$]") as "#FRAG".
         { apply lookup_insert. }
         by iFrame "#∗". }

    rewrite -own_op.
    iCombine "AUTH RP" as "X". 
    rewrite -!cmra_assoc -!auth_frag_op.    
    iApply (own_update with "[$]").

    apply auth_update.
    remember (λ '(r0, b0, p0), (Some (to_agree r0, MaxNat b0), Some (rs2cmra p0))) as f1.
    remember (λ '(r0, b0, _), (Some (to_agree r0, MaxNat b0), None)) as f2.
    rewrite fmap_insert.

    assert (((f2 <$> <[i:=(r, ba `max` b', pb)]> hist) ⋅ {[i := (None, Some (rs2cmra p'))]}) =  (<[i:=(Some (to_agree r, MaxNat (ba `max` b')), Some (rs2cmra p'))]> ((f2 <$> hist) ⋅ {[i := (None, Some (rs2cmra p))]}))).
    {
      rewrite (fmap_insert f2). rewrite -insert_op.
      rewrite {1}Heqf2. rewrite -pair_op. rewrite op_None_right_id op_None_left_id.
      rewrite gmap_disj_op_union.
      2: { apply map_disjoint_dom. rewrite dom_empty_L. set_solver. }
      rewrite map_union_empty.

      apply map_eq.
      intros k. destruct (decide (k = i)).
      - subst. by rewrite !lookup_insert.
      - rewrite !lookup_insert_ne; try done.
        rewrite lookup_op. rewrite lookup_singleton_ne; [| done].
        by rewrite op_None_right_id. }

    rewrite H0.
    rewrite Heqf1 Heqf2. 
    eapply insert_local_update.

    - rewrite lookup_fmap ITH. simpl. reflexivity.
    - rewrite lookup_op. rewrite lookup_singleton.
      rewrite lookup_fmap ITH /=.
      rewrite -Some_op.       
      rewrite -pair_op. rewrite op_None_right_id op_None_left_id.
      reflexivity. 
    - apply prod_local_update'; simpl.
      2: { subst pb. destruct p_eq as [[-> ? ] | [-> ->]].
           - rewrite decide_False; [| done]. 
             by apply rs_step_local_update.
           - rewrite decide_True; [| done]. reflexivity. }
      apply option_local_update.
      apply prod_local_update'; simpl; [reflexivity| ].
      eapply (max_nat_local_update (MaxNat _)). simpl.
      apply Nat.le_max_l.
  Qed.

  Lemma read_hist_alloc hist i r b rs
    (NOITH: i ∉ dom hist):
    read_hist_auth hist ==∗ read_hist_auth (<[ i := ((r, b), rs) ]> hist) ∗ ith_read i r b ∗ ith_rp i rs. 
  Proof using.
    iIntros "AUTH".
    iAssert (|==> read_hist_auth (<[i:=((r, b), rs)]> hist) ∗ ith_rp i rs)%I with "[AUTH]" as "X".
    2: { iMod "X" as "[AUTH $]".
         iDestruct (read_hist_get with "[$]") as "#FRAG".
         { apply lookup_insert. }
         by iFrame. }

    rewrite -own_op.
    iApply (own_update with "[$]").

    rewrite -cmra_assoc. rewrite -auth_frag_op.

    set (f1 := λ '(r0, b0, p0), (Some (to_agree r0, MaxNat b0), Some (rs2cmra p0))). 
    set (f2 := λ '(r0, b0, _), (Some (to_agree r0, MaxNat b0), None)). 
    rewrite !fmap_insert.

    rewrite -insert_op.
    rewrite {2}/f2. rewrite -pair_op. rewrite op_None_right_id op_None_left_id.
    rewrite gmap_disj_op_union.
    2: { apply map_disjoint_dom. rewrite dom_empty_L. set_solver. }
    rewrite map_union_empty.
    replace (Some _, Some _) with (f1 (r, b, rs)) by reflexivity. 

    apply auth_update. eapply alloc_local_update.
    { apply not_elem_of_dom. by rewrite dom_fmap. }
    subst f1. simpl.
    apply pair_valid. split; apply Some_valid.
    - done.
    - apply rs2cmra_valid.
  Qed.

  Lemma ith_read_agree i r1 r2 b1 b2:
    ith_read i r1 b1 -∗ ith_read i r2 b2 -∗ ⌜ r2 = r1  ⌝.
  Proof using.
    rewrite /ith_read.
    rewrite bi.wand_curry -own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    rewrite -auth_frag_op singleton_op in V.
    rewrite auth_frag_valid in V. apply singleton_valid in V.
    rewrite -pair_op in V. rewrite pair_valid in V. apply proj1 in V.
    rewrite -Some_op -pair_op in V. rewrite Some_valid in V.
    rewrite pair_valid in V. apply proj1 in V.
    by apply to_agree_op_inv_L in V. 
  Qed. 

  Lemma ith_rp_le i rp1 rp2:
    ith_rp i rp1 -∗ ith_rp i rp2 -∗ ⌜ rs_compat rp1 rp2 ⌝. 
  Proof using.
    rewrite bi.wand_curry -!own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    iPureIntro. revert V. 
    rewrite -auth_frag_op.
    rewrite gmap_op. simpl. erewrite @merge_singleton.
    2: by apply _.
    2: { rewrite -Some_op. rewrite -pair_op.
         rewrite op_None_left_id.
         rewrite -Some_op. reflexivity. }
    rewrite auth_frag_valid singleton_valid.
    rewrite pair_valid.
    intros [? V]. rewrite Some_valid in V.
    by apply rs_compat_valid.
  Qed.

End ReadsHistory.
