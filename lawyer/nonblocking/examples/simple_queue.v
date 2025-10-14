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
  Context {Σ: gFunctors}.
  Context (γ: gname). 

  Definition me_auth (n: nat): iProp Σ. Admitted. 
  Definition me_exact (n: nat): iProp Σ. Admitted. 
  Definition me_lb (n: nat): iProp Σ. Admitted. 

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

End HistQueue.


Class QueueG Σ := {
    Head: loc; Tail: loc; BeingRead: loc; 
    FreeLater: loc; OldHeadVal: loc;
    γHead: gname; γTail: gname; γBeingRead: gname; 
    γFreeLater: gname; γOldHeadVal: gname;

    γHob: gname;
    q_hq :: HistQueueG Σ;
}.


Section SimpleQueue.

  Definition loc_head: val := λ: "q", Fst "q".
  Definition loc_tail: val := λ: "q", Fst $ Snd "q".
  Definition loc_BR: val := λ: "q", Fst $ Snd $ Snd "q".
  Definition loc_FL: val := λ: "q", Fst $ Snd $ Snd $ Snd "q".
  Definition loc_OHV: val := λ: "q", Snd $ Snd $ Snd $ Snd "q".

  Definition get_val: val := λ: "nd", ! (Fst "nd").
  Definition get_next: val := λ: "nd", ! (Snd "nd").

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

    Definition queue_interp (hq: HistQueue) (h t br fl: nat): iProp Σ :=
      (* TODO: add other components *)
      (∃ (nd: HistNode), ⌜ hq !! h = Some nd ⌝ ∗ Head ↦ #(nd.1)) ∗
      (∃ (nd: HistNode), ⌜ hq !! t = Some nd ⌝ ∗ Tail ↦ #(nd.1))
    .
  
    Definition dangle (od: option loc): iProp Σ. Admitted.
  
    Definition auths (h t br fl hob: nat): iProp Σ :=
      me_exact γHead h ∗ me_exact γTail t ∗ me_exact γBeingRead br ∗
      me_exact γFreeLater fl ∗ me_exact γHob hob.
  
    Definition safe_BR (h br fl hob: nat) (od: option loc): Prop :=
      br = h \/ (* reading the current queue head *)
      br = h - 1 /\ is_Some od \/ (* reading the dangling head *)
      br <= h - 1 /\ ( (* read of some old node that: *)
        fl = br \/ (* is protected by FreeLater *)
        hob > br (* won't actually be read, since a newer head has   been observed *)
      ).
  
    Definition read_head_resources (t br hob: nat): iProp Σ :=
      me_exact γTail t ∗ me_exact γBeingRead br ∗ me_exact γHob hob. 
  
    Definition dequeue_resources (h fl: nat): iProp Σ :=
      me_exact γHead h ∗ me_exact γFreeLater fl.
  
    Definition read_head_token: iProp Σ. Admitted. 
    Definition dequeue_token: iProp Σ. Admitted. 
  
    Definition queue_inv_inner (hq: HistQueue) (h t br fl hob: nat)
      (od: option loc) (ohv: val): iProp Σ :=
      hq_auth hq ∗ 
      queue_interp hq h t br fl ∗ dangle od ∗ OldHeadVal ↦ ohv ∗
      ⌜ fl <= br <= hob /\ hob <= h /\ (fl < h) ⌝ ∗
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

  Lemma access_head hq h t br fl:
    let _: heap1GS Σ := iem_phys _ EM in
    hq_auth hq -∗ queue_interp hq h t br fl -∗
      ∃ nd, ith_node h nd ∗ Head ↦ #nd.1 ∗
             (Head ↦ #nd.1 -∗ hq_auth hq ∗ queue_interp hq h t br fl).
  Proof using.
    simpl. iIntros "HQ QI".
    rewrite /queue_interp. iDestruct "QI" as "((%nd & %HEAD & BR) & ?)".
    iFrame "BR".
    iDestruct (hq_auth_get_ith with "[$]") as "[ITH HQ]"; eauto. iFrame.
    by iIntros "$".
  Qed.

  Lemma access_tail hq h t br fl:
    let _: heap1GS Σ := iem_phys _ EM in
    hq_auth hq -∗ queue_interp hq h t br fl -∗
      ∃ nd, ith_node t nd ∗ Tail ↦ #nd.1 ∗
             (Tail ↦ #nd.1 -∗ hq_auth hq ∗ queue_interp hq h t br fl).
  Proof using.
    simpl. iIntros "HQ QI".
    rewrite /queue_interp. iDestruct "QI" as "(? & (%nd & %TAIL & BR))".
    iFrame "BR".
    iDestruct (hq_auth_get_ith with "[$]") as "[ITH HQ]"; eauto. iFrame.
    by iIntros "$".
  Qed.

  Lemma dequeue_resources_auth_agree h' fl' h t br fl hob:
    dequeue_resources h' fl' -∗ auths h t br fl hob -∗ ⌜ h' = h /\ fl' = fl ⌝.
  Proof using. Admitted. 

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
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & AUTHS & >%SAFE_BR & RH & DQ)".
    
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

  
      pure_steps. iApply 
      
      Unset Printing Notations.
      wp_bind (
          



    

    
End SimpleQueue.
