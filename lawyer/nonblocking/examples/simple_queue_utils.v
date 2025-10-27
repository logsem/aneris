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
  hq_auth hq -∗ ith_node i nd ∗ hq_auth hq.
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

  Inductive read_state := rs_init | rs_canceled | rs_going | rs_completed | rs_protected. 

  Definition read_state_cmra: cmra := csumR (exclR unit) (csumR (agreeR unit) (csumR (excl unit) (csumR (agreeR unit) (agreeR unit)))).

  Definition rs2cmra (rs: read_state) :=
    match rs with
    | rs_init => Cinl $ Excl ()
    | rs_canceled => Cinr $ Cinl $ to_agree ()
    | rs_going => Cinr $ Cinr $ Cinl $ Excl ()
    | rs_completed => Cinr $ Cinr $ Cinr $ Cinl $ to_agree ()
    | rs_protected => Cinr $ Cinr $ Cinr $ Cinr $ to_agree ()
    end.

  Definition rs_wip p := p = rs_init \/ p = rs_going. 
  Definition rs_fin p := p = rs_canceled \/ p = rs_completed \/ p = rs_protected. 
  
  Lemma rp_init_excl (rp: read_state_cmra):
    ¬ ✓ (rs2cmra rs_init ⋅ rp).  
  Proof using.
    intros ?. destruct rp; done.
  Qed.

  Lemma rp_going_excl (rp: read_state_cmra):
    ¬ ✓ (rs2cmra rs_going ⋅ rp). 
  Proof using.
    intros ?. 
    destruct rp; try done.
    destruct c; try done. destruct c; try done. 
  Qed.

  Lemma rp_canceled_not_protected:
    ¬ ✓ (rs2cmra rs_canceled ⋅ rs2cmra rs_protected). 
  Proof using. 
    intros ?. done. 
  Qed.

  Lemma rp_mut_excl rp1 rp2
    (NEQ: rp1 ≠ rp2):
    ¬ ✓ (rs2cmra rp1 ⋅ rs2cmra rp2).
  Proof using.
    destruct rp1, rp2; simpl; intros V; done.
  Qed.

  Global Instance rs_dec: EqDecision read_state.
  red. intros [] [].
  all: try by right.
  all: by left.
  Defined.


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

  Lemma rs2cmra_inj: Inj eq equiv rs2cmra.
  Proof using.
    clear. 
    red. intros [] []; simpl.
    all: try by set_solver.
    all: try by (intros X; inversion X).
    all: try by (intros X; inversion X; subst; inversion H1).
    all: try by (intros X; inversion X; subst; inversion H1; subst; inversion H2). 
    all: try by (intros X; inversion X; subst; inversion H1; subst; inversion H2; subst; inversion H3). 
  Qed.

  Lemma ith_rp_hist_compat hist i rp:
    read_hist_auth hist -∗ ith_rp i rp -∗ ⌜ exists op, hist !! i = Some op /\ op.2 = rp ⌝.
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
    - by apply rs2cmra_inj in H0.
    - admit.
  Admitted.

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

  Lemma ith_read_included i r b b'
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

  (* TODO: clean up unused update lemmas *)

  Lemma read_hist_update hist i r b b' p p'
    (ITH: hist !! i = Some ((r, b), p))
    (P_WIP: rs_wip p):
    read_hist_auth hist -∗ ith_rp i p ==∗ read_hist_auth (<[ i := ((r, max b b'), p') ]> hist) ∗ ith_read i r (max b b') ∗ ith_rp i p'. 
  Proof using.
    iIntros "AUTH RP".
    iAssert (|==> read_hist_auth (<[i:=((r, max b b'), p')]> hist) ∗ ith_rp i p')%I with "[AUTH RP]" as "AUTH".
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

    assert (((f2 <$> <[i:=(r, b `max` b', p')]> hist) ⋅ {[i := (None, Some (rs2cmra p'))]}) =  (<[i:=(Some (to_agree r, MaxNat (b `max` b')), Some (rs2cmra p'))]> ((f2 <$> hist) ⋅ {[i := (None, Some (rs2cmra p))]}))).
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
    3: { apply prod_local_update'; simpl.
         - apply option_local_update.
           apply prod_local_update'; simpl; [reflexivity| ].
           eapply (max_nat_local_update (MaxNat _)). simpl.
           apply Nat.le_max_l.
         - apply option_local_update.
           apply (@exclusive_local_update _ (rs2cmra p)).
           2: { by destruct p'. }
           red in P_WIP. 
           destruct P_WIP as [?|?]; subst; apply _. }
    - rewrite lookup_fmap ITH. simpl. reflexivity.
    - rewrite lookup_op. rewrite lookup_singleton.
      rewrite lookup_fmap ITH /=.
      rewrite -Some_op.       
      rewrite -pair_op. rewrite op_None_right_id op_None_left_id.
      reflexivity. 
  Qed.

  Lemma read_hist_update' hist i r b b' p p'
    (ITH: hist !! i = Some ((r, b), p))
    (P_WIP: rs_wip p \/ p = p'):
    read_hist_auth hist -∗ ith_rp i p ==∗ read_hist_auth (<[ i := ((r, max b b'), p') ]> hist) ∗ ith_read i r (max b b') ∗ ith_rp i p'. 
  Proof using.
    iIntros "AUTH RP".
    iAssert (|==> read_hist_auth (<[i:=((r, max b b'), p')]> hist) ∗ ith_rp i p')%I with "[AUTH RP]" as "AUTH".
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

    assert (((f2 <$> <[i:=(r, b `max` b', p')]> hist) ⋅ {[i := (None, Some (rs2cmra p'))]}) =  (<[i:=(Some (to_agree r, MaxNat (b `max` b')), Some (rs2cmra p'))]> ((f2 <$> hist) ⋅ {[i := (None, Some (rs2cmra p))]}))).
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
      + apply option_local_update.
        apply prod_local_update'; simpl; [reflexivity| ].
        eapply (max_nat_local_update (MaxNat _)). simpl.
        apply Nat.le_max_l.
      + apply option_local_update.
        destruct P_WIP as [P_WIP | <-]. 
        * apply (@exclusive_local_update _ (rs2cmra p)).
          2: { by destruct p'. }
          red in P_WIP. 
          destruct P_WIP as [?|?]; subst; apply _.
        * reflexivity.
  Qed.

  Lemma read_hist_update_weak hist i r b b' p
    (ITH: hist !! i = Some ((r, b), p)):
    read_hist_auth hist ==∗ read_hist_auth (<[ i := ((r, max b b'), p) ]> hist) ∗ ith_read i r (max b b'). 
  Proof using.
    iIntros "AUTH".
    iAssert (|==> read_hist_auth (<[i:=((r, max b b'), p)]> hist))%I with "[AUTH]" as "AUTH".
    2: { iMod "AUTH" as "AUTH". 
         iDestruct (read_hist_get with "[$]") as "#FRAG".
         { apply lookup_insert. }
         by iFrame "#∗". }

    iApply (own_update with "[$]").

    apply auth_update.
    remember (λ '(r0, b0, p0), (Some (to_agree r0, MaxNat b0), Some (rs2cmra p0))) as f1.
    remember (λ '(r0, b0, _), (Some (to_agree r0, MaxNat b0), None)) as f2.
    rewrite !fmap_insert.

    rewrite Heqf1 Heqf2. simpl. 
    eapply insert_local_update.
    3: { apply prod_local_update'; simpl.
         2: reflexivity. 
         apply option_local_update.
         apply prod_local_update'; simpl; [reflexivity| ].
         eapply (max_nat_local_update (MaxNat _)). simpl.
         apply Nat.le_max_l. }
    - rewrite lookup_fmap ITH. simpl. reflexivity.
    - rewrite lookup_fmap ITH /=. reflexivity. 
  Qed.

  Lemma read_hist_update_gen hist i r b b' p (op': option read_state)
    (ITH: hist !! i = Some ((r, b), p))
    (P_EXCL: is_Some op' -> rs_wip p):
    read_hist_auth hist -∗ (⌜ is_Some op' ⌝ -∗ ith_rp i p) ==∗ read_hist_auth (<[ i := ((r,  max b b'), default p op') ]> hist) ∗ ith_read i r (max b b') ∗ (from_option (ith_rp i) True op'). 
  Proof using.
    destruct op'.
    - simpl. iIntros "? RP". iSpecialize ("RP" with "[//]").
      iApply (read_hist_update with "[$] [$]"); try done.
      by apply P_EXCL.
    - simpl. iIntros "? RP".
      rewrite bi.sep_assoc -bupd_frame_r. iSplit; [| done].
      iApply (read_hist_update_weak with "[$]"); try done.
  Qed.

  Lemma read_hist_alloc hist i r b 
    (NOITH: i ∉ dom hist):
    read_hist_auth hist ==∗ read_hist_auth (<[ i := ((r, b), rs_init) ]> hist) ∗ ith_read i r b ∗ ith_rp i rs_init. 
  Proof using.
  (*   iIntros "AUTH". *)
  (*   iAssert (|==> read_hist_auth (<[i:=((r, b), rs_init)]> hist) ∗ ith_rp i rs_init)%I with "[AUTH]" as "X". *)
  (*   2: { iMod "X" as "[AUTH $]". *)
  (*        iDestruct (read_hist_get with "[$]") as "#FRAG". *)
  (*        { apply lookup_insert. } *)
  (*        iFrame. iModIntro. *)
  (*        iApply (ith_read_included with "[$]"). lia. } *)

  (*   rewrite -own_op.  *)
  (*   iApply (own_update with "[$]"). *)

  (*   rewrite -cmra_assoc. rewrite -auth_frag_op.   *)
  (*   apply auth_update.     *)
  (*   rewrite fmap_insert. *)
  (*   eapply alloc_local_update. *)
  (*   2: done.  *)
  (*   rewrite lookup_fmap. apply not_elem_of_dom in NOITH. by rewrite NOITH. *)
  (* Qed. *)
  Admitted. 

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

  Lemma ith_rp_mut_excl i rp1 rp2
    (NEQ: rp1 ≠ rp2):
    ith_rp i rp1 -∗ ith_rp i rp2 -∗ False.
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
    intros [? V]. revert V.
    rewrite Some_valid. 
    by apply rp_mut_excl.
  Qed.    

End ReadsHistory.
