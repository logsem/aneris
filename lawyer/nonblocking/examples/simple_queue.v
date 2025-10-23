From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


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

  (* Lemma list_to_imap_spec l: *)
  (*   forall i, l !! i = list_to_imap l !! i.  *)
  (* Proof using. *)
  (*   induction l. *)
  (*   { set_solver. } *)
  (*   intros. simpl. *)
  (*   rewrite lookup_cons. rewrite /list_to_imap. simpl. *)
  (*   destruct i. *)
  (*   { by rewrite lookup_insert. } *)
  (*   rewrite lookup_insert_ne; [| done]. *)

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


Class QueuePreG Σ := {
  q_pre_max :: MaxExactPreG Σ;
  q_pre_tok :: inG Σ (exclR unitO);
  q_pre_hq :: HistQueueG Σ;
  q_pre_dangle_rop :: inG Σ (excl_authUR (option nat));
}.


Class QueueG Σ := {
    q_pre :: QueuePreG Σ; 
    
    Head: loc; Tail: loc; BeingRead: loc; 
    FreeLater: loc; OldHeadVal: loc;

    q_hq :: HistQueueG Σ;

    q_γ_tok_rh: gname;
    q_γ_tok_dq: gname;
    q_γ_tok_cc: gname;
    q_γ_tok_rop: gname;

    q_γ_dangle: gname;
    q_γ_rop: gname;

    q_me_h :: MaxExactG Σ;
    q_me_t :: MaxExactG Σ;
    q_me_br :: MaxExactG Σ;
    q_me_fl :: MaxExactG Σ;
}.


Section SimpleQueue.

  Definition loc_head: val := λ: "q", Fst "q".
  Definition loc_tail: val := λ: "q", Fst $ Snd "q".
  Definition loc_BR: val := λ: "q", Fst $ Snd $ Snd "q".
  Definition loc_FL: val := λ: "q", Fst $ Snd $ Snd $ Snd "q".
  Definition loc_OHV: val := λ: "q", Snd $ Snd $ Snd $ Snd "q".

  Definition get_val: val := λ: "nd", ! ("nd" +ₗ #0).
  Definition get_next: val := λ: "nd", ! ("nd" +ₗ #1).

  Definition free_el: val. Admitted.

  Definition dequeue: val :=
    λ: "q",
      let: "c" := ! (loc_head "q") in
      if: ("c" = ! (loc_tail "q"))
        then NONE
        else
          let: "v" := get_val "c" in
          (loc_OHV "q") <- "v" ;;
          (loc_head "q") <- (get_next "c") ;;
          let: "to_free" :=
            if: ("c" = ! (loc_BR "q"))
            then
              let: "old_br" := ! (loc_FL "q") in
              (loc_FL "q") <- "c" ;;
              "old_vr"
            else "c"
          in free_el "to_free" ;;
          (SOME "v")
  .

  Section QueueResources. 

    Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.
  
    Context {QL: QueueG Σ}.
    (* Let H := Head. QL. *)
    (* Let T := Tail QL. *)
    (* Let BR := BeingRead QL. *)
    (* Let FL := FreeLater QL. *)
    (* Let OHV := OldHeadVal QL. *)

    Definition hn_interp (hn: HistNode): iProp Σ :=
      let '(l, (v, nxt)) := hn in
      l ↦ v ∗ (l +ₗ 1) ↦ #nxt.

    Definition dummy_node: Node := (#0, Loc 0).

    Fixpoint is_LL_into (hq: HistQueue) (pt: loc) := 
      match hq with 
      | [] => True
      | [ (_, (_, nxt)) ] => nxt = pt
      (*   | (_, (_, nxt1)) :: ((l2, (_, _)) as hn2) :: hq' => nxt1 = l2 /\ is_LL (hn2 :: hq') *)
      (** to avoid introducing Function *)
      | (_, (_, nxt1)) :: hq' =>
          match hq' with
          | [] => True
          | (l2, (_, _)) :: _ => nxt1 = l2 /\ is_LL_into hq' pt
          end
      end.

    (** tail always points to a dummy node
        which doesn NOT belong to the logical queue hq.
        Upon enqueuing, this dummy note is updated and appended to hq.
     *)
    (* TODO: enforce it explicitly? *)
    (* TODO: add other components *)
    Definition queue_interp (hq: HistQueue) (h t br fl: nat): iProp Σ :=
      ⌜ t = length hq ⌝ ∗ 
      ([∗ list] nd ∈ drop h hq, hn_interp nd) ∗
      ∃ (pt: loc), Tail ↦ #pt ∗ hn_interp (pt, dummy_node) ∗ ⌜ is_LL_into hq pt ⌝ ∗
      let ph: loc := (from_option (fun hn => hn.1) pt (hq !! h)) in
      Head ↦{1/2} #ph ∗
      (∃ (nbr: HistNode), ⌜ hq !! br = Some nbr ⌝ ∗ BeingRead ↦#(nbr.1)) ∗
      (∃ (nfl: HistNode), ⌜ hq !! fl = Some nfl ⌝ ∗ FreeLater ↦#(nfl.1) ∗ hn_interp nfl)
    .

    Lemma queue_interp_cur_empty (hq: HistQueue) (h br fl: nat):
      queue_interp hq h h br fl -∗ ⌜ forall d, hq !! (h + d)%nat = None ⌝.
    Proof using.
      iIntros "(%&_)". subst. iPureIntro.
      intros. apply lookup_ge_None_2. lia.
    Qed.

    (* TODO: try to get rid of if *)
    Global Instance hni_tl hn: Timeless (hn_interp hn).
    Proof using.
      destruct hn as [? [??]]. apply _.
    Defined. 

    (* TODO: try to get rid of if *)
    Global Instance qi_tl: forall hq h t br fl, Timeless (queue_interp hq h t br fl).
    Proof using. 
      intros. rewrite /queue_interp.
      apply _. 
    Defined.
  
    Definition dangle_auth (od: option nat): iProp Σ := own q_γ_dangle (●E od).
    Definition dangle_frag (od: option nat): iProp Σ := own q_γ_dangle (◯E od).

    Definition rop_auth (rop: option nat): iProp Σ := own q_γ_rop (●E rop).
    Definition rop_frag (rop: option nat): iProp Σ := own q_γ_rop (◯E rop).
      
    Definition dangle_interp (od: option nat) (h: nat) (hq: HistQueue): iProp Σ :=
      dangle_auth od ∗ (⌜ od = None ⌝ ∨ ⌜ od = Some (h - 1) ⌝ ∗ from_option hn_interp (⌜ False ⌝)%I (hq !! (h - 1)))
    . 
  
    Definition auths (h t br fl: nat): iProp Σ :=
      @me_auth _ q_me_h h ∗ @me_auth _ q_me_t t ∗ @me_auth _ q_me_br br ∗
      @me_auth _ q_me_fl fl
    .

    Definition snapshot (h t br fl: nat): iProp Σ :=
      @me_lb _ q_me_h h ∗ @me_lb _ q_me_t t ∗ @me_lb _ q_me_br br ∗
      @me_lb _ q_me_fl fl
    .

    Lemma take_snapshot (h t br fl: nat): 
      auths h t br fl -∗ snapshot h t br fl.
    Proof using.
      iIntros "(?&?&?&?)".
      rewrite /snapshot. repeat iSplit; by iApply @me_auth_save.
    Qed.

    Lemma snapshot_lb (h t br fl: nat) (h' t' br' fl': nat):
      snapshot h t br fl -∗ auths h' t' br' fl' -∗
      ⌜ h <= h' /\ t <= t' /\ br <= br' /\ fl <= fl'⌝.
    Proof using.
      iIntros "#(X&?&?&?) (Y&?&?&?)".
      repeat iSplit.
      all: iApply (@me_auth_lb with "[-]"); eauto.
    Qed.

    Definition can_cancel: iProp Σ := own q_γ_tok_cc (Excl ()).
    Definition rop_token: iProp Σ := own q_γ_tok_rop (Excl ()).
    Definition cancelled (r: nat): iProp Σ :=
      ∃ r', ⌜ r < r' ⌝ ∗ @me_lb _ q_me_h r'. 

    Definition safe_read (r: nat) (h br fl: nat) (od: option nat): iProp Σ :=
      ⌜ r = h ⌝ ∗ (can_cancel ∨ ⌜ r = br ⌝ ∗ rop_token) ∨
      ⌜ r = h - 1 /\ r = br /\ is_Some od ⌝ ∗ rop_token ∨
      ⌜ r = br /\ r = fl ⌝
    .

    Definition rop_interp (rop: option nat) (h br fl: nat) (od: option nat): iProp Σ :=
      ∀ r, ⌜ rop = Some r  ⌝ -∗ 
            (safe_read r h br fl od ∨ can_cancel ∗ cancelled r). 
  
    Definition read_head_resources (t br: nat): iProp Σ :=
      @me_exact _ q_me_t t ∗ @me_exact _ q_me_br br ∗ rop_frag None ∗ can_cancel ∗ rop_token.

    Definition dequeue_resources (h fl: nat) (ph: loc) (od: option nat): iProp Σ :=
      @me_exact _ q_me_h h ∗ @me_exact _ q_me_fl fl ∗
      Head ↦{1/2} #ph ∗ dangle_frag od. 
  
    Definition read_head_token: iProp Σ := own q_γ_tok_rh (Excl ()).
    Definition dequeue_token: iProp Σ := own q_γ_tok_dq (Excl ()).

    Definition hq_state_wf h t br fl: Prop :=
      fl <= br /\ br <= h /\ fl < h /\ h <= t.
      (* THIS IS FALSE: br can fall behind arbitrarily *)
      (* (br = h \/ br = fl \/ od = Some (h - 1) /\ br = h - 1).  *)
  
    Definition queue_inv_inner (hq: HistQueue) (h t br fl: nat)
      (rop od: option nat) (ohv: val): iProp Σ :=
      hq_auth hq ∗ 
      queue_interp hq h t br fl ∗ dangle_interp od h hq ∗ OldHeadVal ↦ ohv ∗
      ⌜ hq_state_wf h t br fl ⌝ ∗
      auths h t br fl ∗
      rop_interp rop h br fl od  ∗
      (read_head_resources t br ∨ read_head_token) ∗ 
      ((∃ ph, dequeue_resources h fl ph None) ∨ dequeue_token)
    .
  
    Definition queue_ns := nroot .@ "queue".

    (* Definition queue_at (q: loc): iProp Σ := *)
      (* pointsto q DfracDiscarded (#Head, #Tail, #BeingRead, #FreeLater, #OldHeadVal)%V.  *)
    Definition queue_at (q: val): iProp Σ :=
      ⌜ q = (#Head, (#Tail, (#BeingRead, (#FreeLater, #OldHeadVal))))%V ⌝. 
  
    (* Definition queue_inv (q: loc): iProp Σ := *)
    Definition queue_inv (q: val): iProp Σ :=
      queue_at q ∗ inv queue_ns 
        (∃ hq h t br fl rop od ohv, queue_inv_inner hq h t br fl rop od ohv)
    .
  
  End QueueResources.


  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)
  Context {QL: QueueG Σ}.

  Context (d: Degree).

  Definition get_loc_fuel := 5. 

  Lemma get_head_spec l τ π q:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_at l) ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      loc_head l @ τ
    {{{ RET #Head; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "(#QAT & PH & CPS) POST". rewrite /loc_head.
    rewrite /queue_at. iDestruct "QAT" as %->.
    pure_steps. by iApply "POST".
  Qed.

  Lemma get_tail_spec l τ π q:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_at l) ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      loc_tail l @ τ
    {{{ RET #Tail; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "(#QAT & PH & CPS) POST". rewrite /loc_tail.
    rewrite /queue_at. iDestruct "QAT" as %->.
    pure_steps.
    wp_bind (Snd _)%E. pure_steps. 
    by iApply "POST".
  Qed.

  Lemma get_BR_spec l τ π q:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_at l) ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      loc_BR l @ τ
    {{{ RET #BeingRead; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "(#QAT & PH & CPS) POST". rewrite /loc_BR.
    rewrite /queue_at. iDestruct "QAT" as %->.
    pure_steps.
    repeat (wp_bind (Snd (#_, _)%V)%E; pure_steps). 
    by iApply "POST".
  Qed.

  Lemma get_FL_spec l τ π q:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_at l) ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      loc_FL l @ τ
    {{{ RET #FreeLater; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "(#QAT & PH & CPS) POST". rewrite /loc_FL.
    rewrite /queue_at. iDestruct "QAT" as %->.
    pure_steps.
    repeat (wp_bind (Snd (#_, _)%V)%E; pure_steps). 
    by iApply "POST".
  Qed.

  Lemma get_OHV_spec l τ π q:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_at l) ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      loc_OHV l @ τ
    {{{ RET #OldHeadVal; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "(#QAT & PH & CPS) POST". rewrite /loc_OHV.
    rewrite /queue_at. iDestruct "QAT" as %->.
    pure_steps.
    repeat (wp_bind (Snd (#_, _)%V)%E; pure_steps). 
    by iApply "POST".
  Qed.

  Lemma dequeue_token_excl:
    let _: heap1GS Σ := iem_phys _ EM in 
    dequeue_token -∗ dequeue_token -∗ False.
  Proof using.
    simpl. 
    rewrite bi.wand_curry -own_op.
    iIntros "X". by iDestruct (own_valid with "[$]") as %V.
  Qed. 

  Lemma dequeue_resources_excl h1 fl1 ph1 od1 h2 fl2 ph2 od2:
    let _: heap1GS Σ := iem_phys _ EM in 
    dequeue_resources h1 fl1 ph1 od1 -∗ dequeue_resources h2 fl2 ph2 od2 -∗ False.
  Proof using.
    simpl. rewrite /dequeue_resources.
    iIntros "(X&_) (Y&_)".
    by iApply (me_exact_excl with "X [$]"). 
  Qed.

  (* Lemma access_head hq h t br fl: *)
  (*   let _: heap1GS Σ := iem_phys _ EM in *)
  (*   hq_auth hq -∗ queue_interp hq h t br fl -∗ *)
  (*     ∃ nd, ith_node h nd ∗ Head ↦ #nd.1 ∗ *)
  (*            (Head ↦ #nd.1 -∗ hq_auth hq ∗ queue_interp hq h t br fl). *)
  (* Proof using. *)
  (*   simpl. iIntros "HQ QI". *)
  (*   rewrite /queue_interp. iDestruct "QI" as "(? & (%nd & %HEAD & BR) & ?)". *)
  (*   iFrame "BR". *)
  (*   iDestruct (hq_auth_get_ith with "[$]") as "[ITH HQ]"; eauto. iFrame. *)
  (*   by iIntros "$". *)
  (* Qed. *)

  (* Lemma access_tail hq h t br fl: *)
  (*   let _: heap1GS Σ := iem_phys _ EM in *)
  (*   hq_auth hq -∗ queue_interp hq h t br fl -∗ *)
  (*   ∃ (l: loc), Tail ↦ #l ∗ *)
  (*                (Tail ↦ #l -∗ hq_auth hq ∗ queue_interp hq h t br fl). *)
  (* Proof using. *)
  (*   simpl. iIntros "HQ QI". *)
  (*   rewrite /queue_interp. iDestruct "QI" as "(? & ? & (%l & TAIL & DUMMY))". *)
  (*   iFrame "TAIL". iIntros "$". iFrame.   *)
  (* Qed. *)

  Lemma access_queue_ends hq h t br fl:
    let _: heap1GS Σ := iem_phys _ EM in
    hq_auth hq -∗ queue_interp hq h t br fl -∗
      ∃ (ph pt: loc), Head ↦{1/2} #ph ∗ Tail ↦ #pt ∗
        (⌜ h >= t /\ ph = pt ⌝ ∨ ⌜ h < t /\ ph ≠ pt ⌝ ∗ ∃ (nd: Node), ith_node h (ph, nd)) ∗
        (Head ↦{1/2} #ph -∗ Tail ↦ #pt -∗ hq_auth hq ∗ queue_interp hq h t br fl).
  Proof using.
    simpl. iIntros "[AUTH #FRAGS] QI".
    rewrite /queue_interp.
    iDestruct "QI" as "(%T_LEN & Q & (%pt & TAIL & DUMMY & %LL & HEAD & BR))".
    iFrame "HEAD TAIL".    
    destruct (Nat.lt_ge_cases h t) as [LT | GE]; subst t.     
    - 
      pose proof LT as [[ph [??]] HTH]%lookup_lt_is_Some_2.
      rewrite HTH. simpl.
      iDestruct (big_sepL_lookup_acc with "FRAGS") as "[ITH _]"; [by eauto| ].
      iFrame "ITH BR". 

      iDestruct (big_sepL_lookup_acc with "Q") as "[HNI CLOS]".
      { erewrite lookup_drop. by erewrite Nat.add_0_r. }
      iAssert (⌜ ph ≠ pt ⌝)%I as %NEQ.
      { iIntros (<-). rewrite {1}/hn_interp.
        iDestruct "DUMMY" as "[X _]". iDestruct "HNI" as "[Y _]".
        iDestruct (pointsto_valid_2 with "[$] [$]") as %V. set_solver. }
      iSplit; [iRight; done| ].
      iSpecialize ("CLOS" with "[$]"). 
      iIntros "??". by iFrame "#∗". 
    - iSplit. 
      2: { iIntros "??". by iFrame "#∗". }
      iLeft. iSplit; [done| ].
      rewrite (lookup_ge_None_2 _ h) /=; done.      
  Qed.

  Lemma dequeue_resources_auth_agree h' fl' ph od h t br fl:
    let _: heap1GS Σ := iem_phys _ EM in 
    dequeue_resources h' fl' ph od -∗ auths h t br fl -∗ ⌜ h' = h /\ fl' = fl ⌝.
  Proof using.
    simpl. iIntros "(H&FL&?&?) (H'&?&?&FL')".
    iDestruct (me_auth_exact with "H' H") as %?. 
    iDestruct (me_auth_exact with "FL' FL") as %?.
    done. 
  Qed. 

  Lemma dangle_auth_frag_agree od1 od2:
    let _: heap1GS Σ := iem_phys _ EM in 
    dangle_auth od1 -∗ dangle_frag od2 -∗ ⌜ od2 = od1 ⌝. 
  Proof using.
    simpl. rewrite /dangle_auth /dangle_frag.
    rewrite bi.wand_curry -own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    iPureIntro. symmetry. by apply excl_auth_agree_L.
  Qed.  

  Lemma dangle_update od1 od2 od':
    let _: heap1GS Σ := iem_phys _ EM in 
    dangle_auth od1 -∗ dangle_frag od2 ==∗ dangle_auth od' ∗ dangle_frag od'. 
  Proof using.
    simpl. rewrite /dangle_auth /dangle_frag.
    rewrite bi.wand_curry -!own_op.
    iApply own_update. apply excl_auth_update. 
  Qed.  

  Lemma dequeue_resources_dangle_agree h fl ph od od' h' hq':
    let _: heap1GS Σ := iem_phys _ EM in 
    dequeue_resources h fl ph od -∗ dangle_interp od' h' hq' -∗ ⌜ od' = od ⌝.
  Proof using.
    simpl. iIntros "(?&?&?&FRAG) (AUTH&?)".
    by iDestruct (dangle_auth_frag_agree with "[$] [$]") as %?. 
  Qed.

  Lemma access_queue hq h t br fl i hn
    (IN: h <= i < t):
    let _: heap1GS Σ := iem_phys _ EM in 
    hq_auth hq -∗ queue_interp hq h t br fl -∗ ith_node i hn -∗
    hn_interp hn ∗ (hn_interp hn -∗ queue_interp hq h t br fl ∗ hq_auth hq).
  Proof using.
    simpl. rewrite /queue_interp. iIntros "AUTH (% & Q & $) #ITH".
    iDestruct (hq_auth_lookup with "[$] [$]") as %ITH.
    apply proj1, Nat.le_sum in IN as [? ->].
    iDestruct (big_sepL_lookup_acc with "Q") as "[HNI CLOS]".
    { erewrite lookup_drop; eauto. }
    iFrame. iIntros. iSplit; [done| ]. by iApply "CLOS".     
  Qed. 

  Lemma get_head_val_spec Q τ π q h nd fl ph od:
    let _: heap1GS Σ := iem_phys _ EM in
    {{{ queue_inv Q ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      get_val #ph @τ
    {{{ RET (nd.1); th_phase_frag τ π q ∗ dequeue_resources h fl ph od }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & #HEADhn & DR & PH & CPS) POST".
    rewrite /get_val.
    destruct nd as [v nxt]. simpl.
    pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. rewrite loc_add_0. iApply wp_value.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >ROP & RH & DQ)".
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct "DR" as "[HEAD FL]".
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
      specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. } 
    iDestruct (access_queue with "[$] [$] [$]") as "[HNI CLOS']".
    { red in ORDER. lia. }
    rewrite {1}/hn_interp. iDestruct "HNI" as "[VAL NXT]".
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "VAL"). iIntros "!> VAL". 
    MU_by_burn_cp. iApply wp_value.
    iDestruct ("CLOS'" with "[$VAL $NXT]") as "[??]".
    iMod ("CLOS" with "[-POST PH HEAD FL]") as "_".
    { by iFrame. }
    iModIntro. iApply "POST". iFrame.
  Qed.

  (* TODO: unify with the proof above *)
  Lemma get_head_next_spec Q τ π q h nd fl ph od:
    let _: heap1GS Σ := iem_phys _ EM in
    {{{ queue_inv Q ∗ ith_node h (ph, nd) ∗ dequeue_resources h fl ph od ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      get_next #ph @τ
    {{{ RET #(nd.2); th_phase_frag τ π q ∗ dequeue_resources h fl ph od }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & #HEADhn & DR & PH & CPS) POST".
    rewrite /get_next.
    destruct nd as [v nxt]. simpl.
    pure_steps.
    wp_bind (_ +ₗ _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step; [done| ].
    MU_by_burn_cp. iApply wp_value.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od' & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >ROP & RH & DQ)".
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-].
    iDestruct "DR" as "[HEAD FL]".
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
      specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. } 
    iDestruct (access_queue with "[$] [$] [$]") as "[HNI CLOS']".
    { red in ORDER. lia. }
    rewrite {1}/hn_interp. iDestruct "HNI" as "[VAL NXT]".
    iApply sswp_MU_wp; [done| ].
    iApply (wp_load with "NXT"). iIntros "!> NXT". 
    MU_by_burn_cp. iApply wp_value.
    iDestruct ("CLOS'" with "[$VAL $NXT]") as "[??]".
    iMod ("CLOS" with "[-POST PH HEAD FL]") as "_".
    { by iFrame. }
    iModIntro. iApply "POST". iFrame.
  Qed.

  Lemma dequeue_res_head_agree h fl (ph ph': loc) od:
    let _: heap1GS Σ := iem_phys _ EM in 
    dequeue_resources h fl ph od -∗ Head ↦{1 / 2} #ph' -∗ ⌜ ph' = ph ⌝.
  Proof using.
    simpl. rewrite /dequeue_resources. iIntros "(_&_&H'&?) H".
    iDestruct (pointsto_agree with "[$] [$]") as %?. set_solver.
  Qed.

  Lemma update_ohv_spec τ π q (v: val) l:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
          th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      #OldHeadVal <- v @τ
    {{{ RET #(); th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & PH & CPS) POST".
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >ROP & RH & DQ)".
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> ?".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST PH]") as "_". 
    { by iFrame. }
    by iApply "POST".
  Qed.

  Lemma is_LL_into_drop hq pt k
    (LL: is_LL_into hq pt):
    is_LL_into (drop k hq) pt.
  Proof using.
    revert k. induction hq.
    { intros. by rewrite drop_nil. }
    intros. destruct k.
    { by rewrite drop_0. }
    simpl. apply IHhq.
    simpl in LL. destruct a as [? [? ?]].
    destruct hq; try done.
    destruct h as [? [? ?]]. tauto.
  Qed.

  Lemma cancel_rop h t br fl h'
    (LT: h' < h):
    auths h t br fl -∗ cancelled h'.
  Proof using.
    iIntros "(H&?&?&?)".
    rewrite /cancelled.
    iDestruct (me_auth_save with "H") as "LB".
    iExists _. by iFrame.
  Qed.    

  Lemma dequeue_upd_head_spec l τ π q h ph vh (nxh: loc) fl:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in ith_node h (ph, (vh, nxh))) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources h fl ph None) }}}
      #Head <- #nxh @τ
    {{{ RET #(); th_phase_frag τ π q ∗ (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources (h + 1) fl nxh (Some h)) }}}.
  Proof using.
    simpl.
    iIntros (Φ) "([#QAT #INV] & #HTH & PH & CPS & DR) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & >DANGLE & >OHV & >%ORDER & >AUTHS & >ROP & RH & >DQ)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->.

    iClear "INV QAT".

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). iDestruct (queue_interp_cur_empty with "[$]") as %NO.
      specialize (NO 0). rewrite Nat.add_0_r in NO. congruence. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [_ | (% & ?)])"; [| done].
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN &  HNIS & %pt & TAIL & TLI & %LL & HEAD & BR & FL)".
    rewrite HTH. iEval (simpl) in "HEAD".

    iCombine "HEAD HEAD'" as "HEAD". 
    iApply sswp_MU_wp; [done| ].
    iApply (wp_store with "[$]"). iIntros "!> [HEAD HEAD']".
    MU_by_burn_cp. iApply wp_value.

    iMod (dangle_update _ _ (Some h) with "[$] [$]") as "[DAUTH DFRAG]".

    iAssert (|==> auths (h + 1) t br fl ∗ @me_exact _ q_me_h (h + 1))%I with "[CH AUTHS]" as "UPD".
    { rewrite /auths. iDestruct "AUTHS" as "(AUTH&?&?&?)". iFrame.
      iApply (me_update with "AUTH CH"). lia. }
    iMod "UPD" as "[AUTHS CH]".

    iApply "POST". iFrame.

    iAssert (queue_interp hq (h + 1) t br fl ∗ hn_interp (ph, (vh, nxh)))%I
      with "[HNIS TAIL TLI HEAD BR FL]" as "[QI HNI]".
    { iFrame. rewrite -!bi.sep_assoc.
      iSplit; [done| ].
      iFrame "%".
      pose proof (take_drop_middle _ _ _ HTH) as SPLIT.
      rewrite -SPLIT.
      assert (length (take h hq) = h) as H_LEN. 
      { apply length_take_le. apply lookup_lt_Some in HTH. lia. }
      rewrite drop_app_length'; [| done]. simpl.
      rewrite cons_middle app_assoc.
      rewrite drop_app_length'.
      2: { rewrite length_app /=. lia. }
      iDestruct "HNIS" as "[$ $]".
      rewrite lookup_app_r.
      2: { rewrite length_app /=. rewrite H_LEN. lia. }
      rewrite length_app /=. rewrite H_LEN Nat.sub_diag. 
      rewrite -SPLIT in LL. 
      apply is_LL_into_drop with (k := h) in LL.
      rewrite drop_app_length' in LL; [| done].
      simpl in LL. destruct (drop (S h) hq) eqn:REST.
      - by subst.
      - simpl. destruct h0 as [? [??]]. simpl.
        by destruct LL as [-> ?]. }

    iDestruct (cancel_rop with "[$]") as "#CNC".
    { red. rewrite Nat.add_1_r. reflexivity. } 

    iClear "HTH CPS".
    iMod ("CLOS" with "[-]") as "_"; [| done].
    iFrame "QI AUTHS OHV HQ RH DAUTH TOK". iNext.
    iExists _. rewrite Nat.add_sub. rewrite HTH /=.

    iSplitL "HNI". 
    { iRight. by iFrame. }
    iSplit.
    { iPureIntro. red. red in ORDER. repeat split; try lia. }
    rewrite /rop_interp. iIntros (r ->).
    iSpecialize ("ROP" with "[//]"). rewrite /safe_read.

    iDestruct "ROP" as "[[HEAD | [DANGLE | FL]] | CANCELLED]".
    - iDestruct "HEAD" as "(-> & [CC | (-> & TOK)])".
      + iRight. iFrame "#∗". 
      + iLeft. iRight. iLeft. iFrame.
        iPureIntro. split; [lia | done]. 
    - iDestruct "DANGLE" as "((_ & _ & %) & _)". by destruct H.
    - set_solver.
    - iFrame. 
  Qed.

  Definition dequeue_fuel := 100.    

  (* Lemma wf_queue_head_br hq h t br fl od *)
  (*   (ORDER: hq_state_wf h t br fl od): *)
  (*     (let _: heap1GS Σ := iem_phys _ EM in queue_interp hq (h + 1) t br fl) -∗  *)
  (*     ⌜ forall hn hbr, hq !! h = Some hn  -> hq !! br = Some hbr -> h ≠ br -> hn.1 ≠ hbr.1 ⌝ . *)
  (* Proof using. *)
  (*   simpl. iIntros "(%T_LEN &  HNIS & %pt & TAIL & TLI & %LL & HEAD & BR)". *)
  (*   red in ORDER. destruct ORDER as (?&?&?&?&BR_EQ). *)

  Lemma check_BR_spec l τ π q h (* t *) (* br *) fl ph ndh:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in ith_node h (ph, ndh)) ∗
        (* (let _: heap1GS Σ := iem_phys _ EM in snapshot h t br fl) ∗  *)
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources (h + 1) fl ndh.2 (Some h)) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      ! #BeingRead @τ
    {{{ (pbr: loc), RET #pbr; th_phase_frag τ π q ∗
            (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources (h + 1) fl ndh.2 (if (decide (pbr = ph)) then Some h else None)) ∗
            (⌜ pbr = ph ⌝ ∗ @me_lb _ q_me_br h ∨ 
             ⌜ pbr ≠ ph ⌝ ∗ (let _: heap1GS Σ := iem_phys _ EM in  hn_interp (ph, ndh)))
    }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & #HTH & DR& PH & CPS) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & >DANGLE & >OHV & >%ORDER & >AUTHS & >ROP & RH & >DQ)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->.

    iClear "INV QAT".

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] [$]") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). red in ORDER. lia. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [% | (_ & HNI)])"; [done| ].
    rewrite Nat.add_sub HTH /=. 
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN &  HNIS & %pt & TAIL & TLI & %LL & HEAD & BR & FL)".
    iDestruct "BR" as "(%nbr & %BRTH & BR)". destruct nbr as [pbr nbr].
    iAssert (⌜ pbr = ph -> br = h ⌝)%I as %EQ_PTR.
    { iIntros (->). simpl.
      red in ORDER.
      (* relied on wrong br assumption *)
      
      (* rewrite !and_assoc in ORDER. destruct ORDER as [ORDER [BR_NEXT | [BR_FL | [? ?]]]]. *)
      (* - subst br. rewrite BRTH /=. *)
      (*   iCombine "HEAD HEAD'" as "HEAD". *)
      (*   subst t. iDestruct (big_sepL_lookup_acc _ _ 0 with "HNIS") as "[HNI' CLOS']". *)
      (*   { etrans; [| etrans]; [| apply BRTH| reflexivity]. *)
      (*     rewrite lookup_drop. f_equal. lia. } *)
      (*   simpl. destruct nbr, ndh. *)
      (*   iDestruct "HNI" as "[HNI _]". iDestruct "HNI'" as "[HNI' _]". *)
      (*   iCombine "HNI HNI'" as "X". *)
      (*   by iDestruct (pointsto_valid with "X") as %V. *)
      (* - subst br. *)
      (*   iDestruct "FL" as "(%nfl & %FLTH & FL & FLI)". *)
      (*   rewrite BRTH in FLTH. inversion FLTH. subst nfl.  *)
      (*   simpl. destruct nbr, ndh.         *)
      (*   iDestruct "HNI" as "[HNI _]". iDestruct "FLI" as "[HNI' _]". *)
      (*   iCombine "HNI HNI'" as "X". *)
      (*   by iDestruct (pointsto_valid with "X") as %V. *)
      (* - done.  *)

      destruct (decide (br = h)) as [| NEQ]; [done| ].
      assert (br < h \/ br = h + 1) as [LT | NEXT] by lia.
      2: { subst br.
           (* conflict of new head and dangle *)
           admit. }
      destruct (decide (br = fl)) as [-> | NEQ'].
      { (* conflict of head and fl *)
        admit. }
      assert (fl < br) as GT by lia.
      clear NEQ NEQ'.
      admit. }
    clear EQ_PTR. 

    (* iCombine "HEAD HEAD'" as "HEAD".  *)
    iApply sswp_MU_wp; [done| ]. 
    iApply (wp_load with "BR"). iIntros "!> BR".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame.

    iAssert (queue_interp hq (h + 1) t br fl)%I
      with "[HNIS TAIL TLI HEAD BR FL]" as "QI".
    { by iFrame. }


    simpl.
    destruct (decide (pbr = ph)) as [-> | NEQ].
    -
      (* rewrite HTH in BRTH. inversion BRTH. subst. *)
      (* rewrite decide_True; [| done]. iFrame.   *)
      iFrame. 
      iDestruct (take_snapshot with "[$]") as "#SHT".
      iMod ("CLOS" with "[-]") as "_".
      { iFrame. iNext.
        rewrite Nat.add_sub HTH /=.
        iSplit; [| done].
        iRight. by iFrame. }
      iModIntro. iLeft. iSplit. 
      { set_solver. }
      iDestruct "SHT" as "(?&?&?&?)".
      (* Set Printing Implicit. *)
      admit. (* can we do the subsequent proof without it? *)
    -      
      iMod (dangle_update _ _ None with "[$] [$]") as "[DAUTH DFRAG]".
      iFrame.      
      iApply fupd_or. iRight. iFrame "HNI".
      rewrite -(bi.sep_True' ⌜ _ ⌝%I). iApply fupd_frame_l. iSplit; [done| ].
      iMod ("CLOS" with "[-]") as "_"; [| done]. 
      iFrame. iExists _. iNext. iSplitR.
      { by iLeft. }
      iSplit; [done| ]. 
      rewrite /rop_interp.
      iIntros (r ->). iSpecialize ("ROP" with "[//]").
      iDestruct "ROP" as "[SAFE | ?]"; [| by iFrame]. 
      rewrite /safe_read.
      rewrite Nat.add_sub. 
      iDestruct "SAFE" as "[X | Y]".
      * iFrame.
      * iDestruct "Y" as "[X | Y]".
        2: { iFrame. }
        iDestruct "X" as "((->&->&?) & ?)".
        congruence. 
    
    foobar. 
    (* done with assumption of br = h <-> pbr = ph *)
    simpl.
    destruct (decide (br = h)) as [-> | NEQ].
    - rewrite HTH in BRTH. inversion BRTH. subst.
      rewrite decide_True; [| done]. iFrame.  
      iLeft.
      iDestruct (take_snapshot with "[$]") as "#SHT".
      iMod ("CLOS" with "[-]") as "_".
      { iFrame. iNext.
        rewrite Nat.add_sub HTH /=.
        iSplit; [| done].
        iRight. by iFrame. }
      iModIntro. iSplit.
      { set_solver. }
      iDestruct "SHT" as "(?&?&?&?)". done.
    - destruct (decide (pbr = ph)) as [-> | NEQ_PTR].
      2: { iMod (dangle_update _ _ None with "[$] [$]") as "[DAUTH DFRAG]".
           iFrame.      
           iApply fupd_or. iRight. iFrame "HNI".
           rewrite -(bi.sep_True' ⌜ _ ⌝%I). iApply fupd_frame_l. iSplit; [done| ].
           iMod ("CLOS" with "[-]") as "_"; [| done]. 
           iFrame. iExists _. iNext. iSplitR.
           { by iLeft. }
           iSplit.
           + iPureIntro. red. red in ORDER.
             repeat split; lia.
           + rewrite /rop_interp.
             iIntros (r ->). iSpecialize ("ROP" with "[//]").
             iDestruct "ROP" as "[SAFE | ?]"; [| by iFrame]. 
             rewrite /safe_read. iDestruct "SAFE" as "[X | Y]".
             * iFrame.
             * rewrite Nat.add_sub. iDestruct "Y" as "[X | Y]".
                2: { iFrame. }
                iDestruct "X" as "((->&->&?) & ?)". lia. }

      iMod (dangle_update _ _ None with "[$] [$]") as "[DAUTH DFRAG]".      
  Qed.

  Lemma dequeue_spec l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_token) ∗ 
          th_phase_frag τ π q ∗ cp_mul π d dequeue_fuel }}}
      dequeue l @ τ
    {{{ (v: val), RET v; th_phase_frag τ π q ∗ (let _: heap1GS Σ := iem_phys _ EM in dequeue_token) }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST". rewrite /dequeue.
    pure_steps.

    split_cps "CPS" get_loc_fuel.
    { cbv. lia. } 
    iApply (get_head_spec with "[$QAT $CPS' $PH]").
    iIntros "!> PH".

    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %hob & %od & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >%SAFE_BR & RH & DQ)".
    
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph & %pt & HEAD & TAIL & HT & CLOS')".
    iApply (wp_load with "HEAD"). iIntros "!> HEAD".
    iDestruct "DQ" as "[[%ph_ DR] | TOK']".
    2: { by iDestruct (dequeue_token_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_res_head_agree with "DR [$]") as %<-. 
    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.

    iMod ("CLOS" with "[-POST CPS PH DR]") as "_".
    { by iFrame. }
    iModIntro.
    (* TODO: do we need to keep track of previous values at this point? *)
    clear t br hob od ohv ORDER SAFE_BR hq.
    clear pt.

    wp_bind (Rec _ _ _)%E. pure_steps. 
    
    split_cps "CPS" get_loc_fuel.
    { cbv. lia. } 
    iApply (get_tail_spec with "[$QAT $CPS' $PH]").
    iIntros "!> PH".

    wp_bind (! _)%E.
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %hob & %od & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & AUTHS & >%SAFE_BR & RH & DQ)".
    iApply sswp_MU_wp; [done| ].
    iDestruct (access_queue_ends with "[$] [$]") as "(%ph_ & %pt & HEAD & TAIL & #HT & CLOS')".
    iApply (wp_load with "[$]"). iIntros "!> TAIL".
    iDestruct (dequeue_res_head_agree with "DR [$]") as %->. 
    iDestruct (dequeue_resources_auth_agree with "DR [$]") as %[<- <-].
    iDestruct (take_snapshot with "[$]") as "#SHT".

    iDestruct ("CLOS'" with "[$] [$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST CPS PH DR]") as "_".
    { by iFrame. }
    iModIntro.

    (* TODO: do we need to keep track of previous values at this point? *)
    (* clear br hob od ohv ORDER SAFE_BR hq. *)
    clear od ohv
      (* ORDER *)
      SAFE_BR
      hq
    .

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    (* destruct bool_decide. *)
    iDestruct "HT" as "[[%GE <-] | (%NEMPTY & %ndh & #HTH)]". 
    { assert (t = h) as -> by lia.
      rewrite bool_decide_true; [| done]. 
      iApply sswp_MU_wp_fupd; [done| ]. 
      iInv "INV" as "(%hq & %h_ & %t' & %br' & %fl_ & %hob' & %od & %ohv & inv)" "CLOS".
      iEval (rewrite /queue_inv_inner) in "inv".
      iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER' & AUTHS & >%SAFE_BR & RH & DQ)".
      iModIntro.
      iApply sswp_pure_step; [done| ].
      do 2 iNext. MU_by_burn_cp.
      iDestruct "DQ" as "[(% & DR') | TOK]".
      { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
      iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[-> ->]. 
      iMod ("CLOS" with "[-POST CPS PH TOK]") as "_".
      { by iFrame. }
      iModIntro. pure_steps.
      iApply "POST". iFrame. }

    rewrite bool_decide_false; [| set_solver]. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].  
    iApply (get_head_val_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> [PH DR]".
    wp_bind (Rec _ _ _)%E. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ]. 
    iApply (get_OHV_spec with "[$PH $CPS' $QAT]").
    iIntros "!> PH".

    destruct ndh as [vh nxh]. simpl.
    wp_bind (_ <- _)%E.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].     
    iApply (update_ohv_spec with "[$QAT $PH $CPS' $INV]").
    iIntros "!> PH".
    wp_bind (Rec _ _ _)%E. pure_steps.

    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (get_head_next_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> [PH DR]". simpl.

    wp_bind (loc_head l)%E. 
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (get_head_spec with "[$QAT $CPS' $PH]").
    iIntros "!> PH".

    wp_bind (_ <- _)%E.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (dequeue_upd_head_spec with "[$QAT $CPS' $PH $INV $HTH $DR]").
    iIntros "!> (PH & DR)".

    wp_bind (Rec _ _ _)%E. pure_steps.
    split_cps "CPS" get_loc_fuel; [cbv; lia| ].
    iApply (get_BR_spec with "[$QAT $CPS' $PH]").
    iIntros "!> PH".

    wp_bind (! _)%E.
    
    
    

    
End SimpleQueue.
