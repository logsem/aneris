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
  
  Context `{MaxExactG Σ}.

  Definition me_auth (n: nat): iProp Σ := own me_γ (●E n, ●MN n). 
  Definition me_exact (n: nat): iProp Σ := own me_γ (◯E n, ◯MN n). 
  Definition me_lb (n: nat): iProp Σ := own me_γ (◯ None, ◯MN n). 

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
      hq_map :: inG Σ (authUR (gmapUR nat (agreeR HistNode)));
      hq_me :: MaxExactPreG Σ;
  }.
  
  Class HistQueueG Σ := {
      hq_PreG :: HistQueuePreG Σ;
      hq_γ__map: gname;

      hq_me_h :: MaxExactG Σ;
      hq_me_t :: MaxExactG Σ;
      hq_me_br :: MaxExactG Σ;
      hq_me_fl :: MaxExactG Σ;
      hq_me_hob :: MaxExactG Σ;
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


Class QueueG Σ := {
    Head: loc; Tail: loc; BeingRead: loc; 
    FreeLater: loc; OldHeadVal: loc;
    (* γHead: gname; γTail: gname; γBeingRead: gname;  *)
    (* γFreeLater: gname; γOldHeadVal: gname; *)

    γHob: gname;
    q_hq :: HistQueueG Σ;
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

    (** tail always points to a dummy node
        which doesn NOT belong to the logical queue hq.
        Upon enqueuing, this dummy note is updated and appended to hq.
     *)
    (* TODO: enforce it explicitly? *)
    (* TODO: add other components *)
    Definition queue_interp (hq: HistQueue) (h t br fl: nat): iProp Σ :=
      ⌜ t = length hq ⌝ ∗ 
      ([∗ list] nd ∈ drop h hq, hn_interp nd) ∗
      ∃ (pt: loc), Tail ↦ #pt ∗ hn_interp (pt, dummy_node) ∗ 
      Head ↦ #(from_option (fun hn => hn.1) pt (hq !! h))
    .

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
  
    Definition dangle (od: option loc): iProp Σ. Admitted.
  
    Definition auths (h t br fl hob: nat): iProp Σ :=
      @me_auth _ hq_me_h h ∗ @me_auth _ hq_me_t t ∗ @me_auth _ hq_me_br br ∗
      @me_auth _ hq_me_fl fl ∗ @me_auth _ hq_me_hob hob
    .
  
    Definition safe_BR (h br fl hob: nat) (od: option loc): Prop :=
      br = h \/ (* reading the current queue head *)
      br = h - 1 /\ is_Some od \/ (* reading the dangling head *)
      br <= h - 1 /\ ( (* read of some old node that: *)
        fl = br \/ (* is protected by FreeLater *)
        hob > br (* won't actually be read, since a newer head has   been observed *)
      ).
  
    Definition read_head_resources (t br hob: nat): iProp Σ :=
      @me_exact _ hq_me_t t ∗ @me_exact _ hq_me_br br ∗ @me_exact _ hq_me_hob hob. 
  
    Definition dequeue_resources (h fl: nat): iProp Σ :=
      @me_exact _ hq_me_h h ∗ @me_exact _ hq_me_fl fl.
  
    Definition read_head_token: iProp Σ. Admitted. 
    Definition dequeue_token: iProp Σ. Admitted. 
  
    Definition queue_inv_inner (hq: HistQueue) (h t br fl hob: nat)
      (od: option loc) (ohv: val): iProp Σ :=
      hq_auth hq ∗ 
      queue_interp hq h t br fl ∗ dangle od ∗ OldHeadVal ↦ ohv ∗
      ⌜ fl <= br <= hob /\ hob <= h /\ fl < h /\ h <= t⌝ ∗
      auths h t br fl hob ∗
      ⌜ safe_BR h br fl hob od ⌝ ∗
      (read_head_resources t br hob ∨ read_head_token) ∗ 
      (dequeue_resources h fl ∨ dequeue_token)
    .
  
    Definition queue_ns := nroot .@ "queue".

    (* Definition queue_at (q: loc): iProp Σ := *)
      (* pointsto q DfracDiscarded (#Head, #Tail, #BeingRead, #FreeLater, #OldHeadVal)%V.  *)
    Definition queue_at (q: val): iProp Σ :=
      ⌜ q = (#Head, (#Tail, (#BeingRead, (#FreeLater, #OldHeadVal))))%V ⌝. 
  
    (* Definition queue_inv (q: loc): iProp Σ := *)
    Definition queue_inv (q: val): iProp Σ :=
      queue_at q ∗ inv queue_ns 
        (∃ hq h t br fl hob od ohv, queue_inv_inner hq h t br fl hob od ohv)
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

  Lemma dequeue_token_excl:
    let _: heap1GS Σ := iem_phys _ EM in 
    dequeue_token -∗ dequeue_token -∗ False.
  Proof. Admitted.

  Lemma dequeue_resources_excl h1 fl1 h2 fl2:
    let _: heap1GS Σ := iem_phys _ EM in 
    dequeue_resources h1 fl1 -∗ dequeue_resources h2 fl2 -∗ False.
  Proof. Admitted.

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
    (* ∃ ndh (pt: loc), ith_node h ndh ∗ Head ↦ #ndh.1 ∗ Tail ↦ #pt ∗ *)
    (*            ⌜ h = t <-> ndh.1 = pt ⌝ ∗  *)
    (*            (Head ↦ #ndh.1 -∗ Tail ↦ #pt -∗ hq_auth hq ∗ queue_interp hq h t br fl). *)
      ∃ (ph pt: loc), Head ↦ #ph ∗ Tail ↦ #pt ∗
        (⌜ h = t /\ ph = pt ⌝ ∨ ⌜ h < t /\ ph ≠ pt ⌝ ∗ ∃ ndh, ith_node h ndh) ∗
        (Head ↦ #ph -∗ Tail ↦ #pt -∗ hq_auth hq -∗ queue_interp hq h t br fl).
  Proof using.
    simpl. iIntros "HQ QI".
    rewrite /queue_interp.
    iDestruct "QI" as "(Q & (%nd & %HEAD & BR) & (%pt & TAIL & DUMMY))".
    iDestruct (hq_auth_get_ith with "[$]") as "[ITH HQ]"; eauto.
    iFrame "BR TAIL".
    rewrite bi.sep_comm -bi.sep_assoc. iSplit.
    { destruct nd as [ph [vh ?]]. simpl.

      assert (length hq = t) by admit. subst t.
      
      iDestruct (big_sepL_lookup_acc with "Q") as "[HNI CLOS]".
      { erewrite lookup_drop. by erewrite Nat.add_0_r. }
      rewrite {1}/hn_interp.

      
      
      
    iFrame.
    
    by iIntros "$".
  Qed.

  Lemma dequeue_resources_auth_agree h' fl' h t br fl hob:
    dequeue_resources h' fl' -∗ auths h t br fl hob -∗ ⌜ h' = h /\ fl' = fl ⌝.
  Proof using. Admitted. 

  Lemma access_queue hq h t br fl i hn
    (IN: h <= i < t):
    let _: heap1GS Σ := iem_phys _ EM in 
    hq_auth hq -∗ queue_interp hq h t br fl -∗ ith_node i hn -∗
    hn_interp hn ∗ (hn_interp hn -∗ queue_interp hq h t br fl ∗ hq_auth hq).
  Proof using.
    simpl. rewrite /queue_interp. iIntros "AUTH (Q & $ & $) #ITH".
    iDestruct (hq_auth_lookup with "[$] [$]") as %ITH.
    apply proj1, Nat.le_sum in IN as [? ->].
    iDestruct (big_sepL_lookup_acc with "Q") as "[HNI CLOS]".
    { erewrite lookup_drop; eauto. }
    repeat iFrame.
  Qed.

  (* Lemma get_val_spec Q τ π q h hn fl: *)
  (*   let _: heap1GS Σ := iem_phys _ EM in  *)
  (*   {{{ queue_inv Q ∗ ith_node h hn ∗ dequeue_resources h fl ∗ *)
  (*       th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}} *)
  (*     get_val #(hn.1) @τ *)
  (*   {{{ RET (hn.2.1); th_phase_frag τ π q ∗ dequeue_resources h fl }}}. *)
  (* Proof using.  *)
  (*   simpl. iIntros (Φ) "([#QAT #INV] & #HEADhn & DR & PH & CPS) POST". *)
  (*   rewrite /get_val. *)
  (*   destruct hn as [l [v nxt]]. simpl. *)
  (*   pure_steps. *)
  (*   wp_bind (_ +ₗ _)%E. *)
  (*   iApply sswp_MU_wp; [done| ]. *)
  (*   iApply sswp_pure_step; [done| ]. *)
  (*   MU_by_burn_cp. rewrite loc_add_0. iApply wp_value. *)
  (*   iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %hob & %od & %ohv & inv)" "CLOS". *)
  (*   iEval (rewrite /queue_inv_inner) in "inv". *)
  (*   iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >%SAFE_BR & RH & DQ)". *)
  (*   iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. *)
  (*   iDestruct "DR" as "[HEAD FL]". *)
  (*   iDestruct (access_queue with "[$] [$] [$]") as "[HNI CLOS']". *)
  (*   { lia.  *)
  (*   iDestruct (hq_auth_lookup with "[$] [$]") as  *)

  Lemma dequeue_spec l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_token) ∗ 
          th_phase_frag τ π q ∗ cp_mul π d 50 }}}
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
    iDestruct (access_head with "[$] [$]") as "(%ch & #HEADch & HEAD & CLOS')".
    iApply (wp_load with "[$]"). iIntros "!> HEAD".
    iDestruct ("CLOS'" with "[$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.

    iDestruct "DQ" as "[DR | TOK']".
    2: { by iDestruct (dequeue_token_excl with "[$] [$]") as "?". }

    iMod ("CLOS" with "[-POST CPS PH DR]") as "_".
    { by iFrame. }
    iModIntro.
    (* TODO: do we need to keep track of previous values at this point? *)
    clear t br hob od ohv ORDER SAFE_BR hq.

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
    iDestruct (access_tail with "[$] [$]") as "(%ct & #TAILct & TAIL & CLOS')".
    iApply (wp_load with "[$]"). iIntros "!> TAIL".
    iDestruct ("CLOS'" with "[$]") as "(HQ & QI)".
    MU_by_burn_cp. iApply wp_value.
    iMod ("CLOS" with "[-POST CPS PH DR]") as "_".
    { by iFrame. }
    iModIntro.
    (* TODO: do we need to keep track of previous values at this point? *)
    clear h_ fl_ br hob od ohv ORDER SAFE_BR hq.

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { destruct ch, ct. simpl. tauto. }
    MU_by_burn_cp. iApply wp_value.

    destruct bool_decide.
    {
      iApply sswp_MU_wp_fupd; [done| ]. 
      iInv "INV" as "(%hq & %h_ & %t' & %br & %fl_ & %hob & %od & %ohv & inv)" "CLOS".
      iEval (rewrite /queue_inv_inner) in "inv".
      iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & AUTHS & >%SAFE_BR & RH & DQ)".
      iModIntro.
      iApply sswp_pure_step; [done| ].
      do 2 iNext. MU_by_burn_cp.
      iDestruct "DQ" as "[DR' | TOK]".
      { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
      iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[-> ->]. 
      iMod ("CLOS" with "[-POST CPS PH TOK]") as "_".
      { by iFrame. }
      iModIntro. pure_steps.
      iApply "POST". iFrame. }

    (* TODO: can we just forget about the tail from now on? *)
    iClear "TAILct". clear t ct.
    pure_steps.

    destruct ch as [lh [vh nxh]]. simpl.

  
      pure_steps. iApply 
      
      Unset Printing Notations.
      wp_bind (
          



    

    
End SimpleQueue.
