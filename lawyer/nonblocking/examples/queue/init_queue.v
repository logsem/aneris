From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
From heap_lang Require Import heap_lang_defs lang notation.
From lawyer.nonblocking.tokens Require Import tokens_ra.

Close Scope Z. 


Section InitQueue.

  (* TODO: move *)
  Lemma list_to_imap_ext {A: Type} (l: list A) (a: A):
    list_to_imap (l ++ [a]) = <[ length l := a ]> (list_to_imap l).
  Proof using.
    rewrite /list_to_imap. simpl.
    rewrite imap_app /=.
    rewrite Nat.add_0_r.
    rewrite list_to_map_snoc; [done| ].
    apply not_elem_of_list_to_map.
    erewrite imap_ext with (g := pair ∘ (plus 0)).
    2: { intros. f_equal. }
    rewrite -(Nat.add_0_l (length l)). 
    rewrite -simple_queue_utils.helper.
    apply lookup_ge_None_2. lia.
  Qed.

  Lemma hq_auth_alloc `{HistQueuePreG Σ} hq:
    ⊢ |==> ∃ (_: HistQueueG Σ), hq_auth hq.
  Proof using.
    iStartProof.
    iMod (own_alloc ((● (to_agree <$> (list_to_imap hq): gmapUR nat (agreeR HistNode))) ⋅ ◯ _)) as "(%γ & AUTH & FRAG)".
    { apply auth_both_valid_2.      
      { (* TODO: make a lemma *)
        red. intros k.
        destruct lookup eqn:LL; [| done].
        apply lookup_fmap_Some in LL. 
        destruct LL as (a&<-&?). 
        done. }
      reflexivity. }
    iModIntro. iExists {| hq_γ__map := γ |}. iFrame.
    rewrite /ith_node.
    iRevert "FRAG". iStopProof. 
    pattern hq. apply rev_ind.
    { set_solver. }
    intros nd hq' IH. iIntros "_ OWN".
    rewrite list_to_imap_ext.
    rewrite fmap_insert.
    rewrite insert_singleton_op.
    2: { apply not_elem_of_dom. rewrite dom_fmap.
         rewrite list_to_imap_dom.
         intros ?%elem_of_set_seq. simpl in *.
         by apply proj2, Nat.lt_irrefl in H0. }
    rewrite auth_frag_op.
    rewrite big_sepL_app big_sepL_singleton.
    rewrite Nat.add_0_r.
    iDestruct "OWN" as "[$ X]".
    by iApply IH.
  Qed.

  Lemma dangle_init `{inG Σ (excl_authUR (option nat))}:
    ⊢ |==> ∃ γ, own γ (●E None) ∗ own γ (◯E None).
  Proof using.
    setoid_rewrite <- own_op. iApply own_alloc.
    by apply auth_both_valid_2. 
  Qed. 

  Lemma rop_init `{inG Σ (excl_authUR (option nat))}:
    ⊢ |==> ∃ γ, own γ (●E None) ∗ own γ (◯E None).
  Proof using.
    setoid_rewrite <- own_op. iApply own_alloc.
    by apply auth_both_valid_2. 
  Qed.

  Lemma rop_token_init `{inG Σ (exclR unitO)}:
    ⊢ |==> ∃ γ, own γ (Excl ()).
  Proof using. by iApply own_alloc. Qed. 

  Lemma auths_exacts_init `{MaxExactPreG Σ} (ns: list nat):
    ⊢ |==> ∃ (MES: list (MaxExactG Σ)),
        ([∗ list] _ ↦ n;ME ∈ ns; MES, @me_auth _ ME n) ∗ 
        ([∗ list] _ ↦ n;ME ∈ ns; MES, @me_exact _ ME n).
  Proof using.
    iInduction ns as [| n ns] "IH".
    { set_solver. }
    simpl.
    iMod (max_exact_init n) as "(%ME & AUTH & EX & _)".
    iMod "IH" as "(%MES & AUTHS & EXS)".
    iModIntro. iExists (ME :: MES). iFrame.
  Qed.    
                                
  Definition hist0: read_hist := {[ 0 := ((0, 0), rs_proc $ Some rsp_completed )]}.
  
  Lemma read_hist_init `{ReadHistPreG Σ}:
    ⊢ |==> ∃ (_: ReadHistG Σ), read_hist_auth hist0
                                 ∗ ith_rp 0 (rs_proc $ Some rsp_completed)
  .
  Proof using.
    iMod (own_alloc (● ∅ ⋅ ◯ _)) as "(%γ & HIST)".
    { apply auth_both_valid_2; done. }
    set (RH :=  {| rh_γ__map := γ |}). iExists RH. 
    iMod (@read_hist_alloc _ RH ∅ with "[HIST]") as "(x&y&z)".
    2: { iFrame. }
    { done. }
    iModIntro. iFrame.
  Qed.

  Context `{QueuePreG Σ, heap1GS Σ, invGS_gen HasNoLc Σ, MethodTokenPre Σ}.
  Context (PE: val -> iProp Σ) {PE_PERS: forall v, Persistent (PE v)}. 

  (* TODO: move/upstream *)
  Lemma bi_exist_pair {A B: Type} (P: A -> B -> iProp Σ):
    (∃ (a: A) (b: B), P a b) ⊣⊢ ∃ (ab: A * B), P ab.1 ab.2.
  Proof using.
    iSplit.
    - iIntros "(%&%&?)". by iExists (_, _).
    - iIntros "(%ab&?)". destruct ab. iFrame.
  Qed.

  (* TODO: a better way would be to relax restrictions
     on initial nodes pointed by pfl and ph *)
  Definition is_init_queue_cfg (c: cfg heap_lang) sq (pfl ph: loc) (v: val): Prop :=
    let '(SQ H T BR FL OHV) := sq in
    NoDup [H; T; BR; FL; OHV; ph; ph +ₗ 1; pfl; pfl +ₗ 1] /\
    let pto (ptr: loc) (v: val) :=  c.2.(heap) !! ptr = Some $ Some v in
    pto BR #pfl /\ pto FL #pfl /\
    pto H #ph /\ pto T #ph /\
    pto OHV v /\
    pto ph #0 /\ pto (loc_add ph 1%Z) #(Loc 0) /\
    pto pfl v /\ pto (loc_add pfl 1%Z) #ph
  . 
      
  Definition queue_init_resource sq (pfl ph: loc) (v: val): iProp Σ :=
    let '(SQ H T BR FL OHV) := sq in
    ([∗ list] ptr ∈ [BR; FL], ptr ↦ #pfl) ∗
    ([∗ list] ptr ∈ [H; T], ptr ↦ #ph) ∗
    OHV ↦ v ∗ 
    hn_interp (ph, dummy_node) ∗ hn_interp (pfl, (v, ph)).

  (* TODO: move *)
  Local Lemma heap_ptrs_helper (h: gmap loc (option val)) (ptrs: list loc)
    (vals: list val)
    (ND: NoDup ptrs)
    (PTRS_VALS: Forall2 (fun ptr v => h !! ptr = Some (Some v)) ptrs vals):
    ⊢ ([∗ map] l↦v ∈ h, gen_heap.pointsto l (DfracOwn 1) v) -∗
    [∗ list] _↦ ptr;v ∈ ptrs;vals, gen_heap.pointsto ptr (DfracOwn 1) (Some v).
  Proof using.
    clear -ND PTRS_VALS. 
    generalize dependent vals. generalize dependent h.
    induction ptrs.
    { intros. inversion PTRS_VALS. subst. set_solver. }
    intros. inversion PTRS_VALS. subst.
    iIntros "HEAP".
    simpl. iDestruct (big_sepM_delete with "HEAP") as "[$ HEAP]".
    { eauto. }
    iDestruct (IHptrs with "HEAP") as "$".
    { eapply NoDup_cons_1_2; eauto. }
    apply Forall2_same_length_lookup in H4 as [LEN ALL]. 
    apply Forall2_same_length_lookup. split; [done| ].
    intros. erewrite lookup_delete_ne; eauto.
    intros <-. apply NoDup_cons_1_1 in ND.
    destruct ND. eapply elem_of_list_lookup; eauto.
  Qed.

  Lemma obtain_queue_init_resource c sq pfl ph v
    (INIT: is_init_queue_cfg c sq pfl ph v):
    hl_phys_init_resource c -∗ queue_init_resource sq pfl ph v.
  Proof using.
    rewrite /hl_phys_init_resource.
    destruct sq. red in INIT. simpl.
    iIntros "HEAP".
    rewrite !bi.sep_emp.
    destruct INIT as [ND PTRS].
    rewrite !heap_lang_defs.pointsto_unseal.

    iDestruct (heap_ptrs_helper with "HEAP") as "X".
    { eauto. }
    { repeat (constructor; [apply PTRS| ]). constructor. }
    simpl. iDestruct "X" as "($&$&$&$&$&$&$&$&$&?)".
  Qed.    
  
  Lemma queue_init sq (pfl ph: loc) (v: val):
    queue_init_resource sq pfl ph (v: val) -∗ PE v ={⊤}=∗
    ∃ qv (_: QueueG Σ), queue_inv PE qv ∗ read_head_token ∗ dequeue_token. 
  Proof using All.
    destruct sq eqn:SQ. simpl.
    rewrite /queue_init_resource. 
    iIntros "((BR & FL & _) & (H & T & _) & OHV & HNh & HNfl) #PEv".

    iAssert (|={⊤}=> ∃ (qv : val) (H3 : QueueG Σ), queue_at qv ∗
               (∃ hq (h t br fl : nat) (rop od : option nat) (hist : read_hist), 
               queue_inv_inner PE hq h t br fl rop od hist) ∗ read_head_token ∗ dequeue_token)%I with "[-]" as "INV".
    2: { iMod "INV" as "(%&%&$&?&$&$)".
         by iApply inv_alloc. }    
    rewrite /queue_inv_inner.

    set (hq0 := [(pfl, (v, ph))]). 
    iMod (hq_auth_alloc hq0) as "(%HQ & HQ)".
    iMod dangle_init as "(%γ_d & DAUTH & DFRAG)". 
    iMod rop_init as "(%γ_r & RAUTH & RFRAG)".
    iMod rop_token_init as "(%γ_rtok & RTOK)". 
    iMod read_hist_init as "(%RHIST & HIST & #RP0)".
    iMod sqt_pre_init as "(%SQT & DTOK & ETOK)".

    iMod (auths_exacts_init [1; 1; 0; 0]) as "(%MES & AUTHS & EXS)".
    iDestruct (big_sepL2_length with "AUTHS") as %ME_LEN. simpl in ME_LEN.
    do 5 (destruct MES; simpl in ME_LEN; try lia). 
    
    iModIntro. iExists _.
    iExists (Build_QueueG _ sq _ m m0 m1 m2 _ _ _ _ _ _).
    iSplitR.
    { rewrite /queue_at. simpl. iPureIntro. reflexivity. }
    iSplitR "ETOK DTOK".
    2: by iFrame. 
    
    iFrame "HQ". 
    simpl. rewrite !bi.sep_emp.
    
    iDestruct "AUTHS" as "($&$&MA_BR&$)".
    iDestruct (me_auth_save with "MA_BR") as "#BR0". 
    iFrame "MA_BR".
    
    iExists None, None, hist0.
    iSplitR.
    { iPureIntro. red. lia. }
    iDestruct "H" as "[H H']". iDestruct "T" as "[T T']".
    
    iSplitL "H' T' HNh BR FL HNfl".
    { rewrite /queue_interp /phys_queue_interp.
      rewrite SQ. simpl. iFrame.
      iSplit; [done| ].
      iSplitL "BR".
      - iExists _. iSplit; [done| ]. iFrame.
      - iExists _. iSplit; [done| ]. iFrame. }
    
    iSplitL "DAUTH".
    { iFrame. by iLeft. }
    
    iSplitL "OHV".
    { rewrite SQ /=. iFrame "#∗". }
    
    iSplitL "HIST RAUTH".
    { iFrame. iSplit; [| iSplit]. 
      - by iIntros (? [=]).
      - iPureIntro. red.
        exists 0. split; [set_solver| ].
        split; [set_solver| ].
        split.
        + rewrite /hist0. intros ??? [[??]?] ?.
          rewrite !lookup_singleton_Some. lia.
        + rewrite /hist0. intros ? [[??]?].
          rewrite !lookup_singleton_Some.
          set_solver.
      - rewrite /old_rps. rewrite /hist0.
        simpl. rewrite big_sepM_singleton.
        iFrame "#∗". iPureIntro.
        red. tauto. }
    
    iDestruct "EXS" as "(EX_H & EX_T & EX_BR & EX_FL)".
    iSplitL "EX_BR EX_T RTOK RFRAG T".
    { iLeft. rewrite SQ /=. iFrame. }
    iSplitL "EX_H EX_FL H DFRAG".
    { iLeft. rewrite SQ /=. iFrame. }
    
    rewrite /queue_elems_interp.
    subst hq0. rewrite big_sepL_singleton. simpl.
    done.
  Qed.                                     
  
End InitQueue.


  (* Lemma dequeue_token_excl: *)
  (*   dequeue_token -∗ dequeue_token -∗ False. *)
  (* Proof using. *)
  (*   clear.  *)
  (*   simpl. rewrite /dequeue_token. *)
  (*   rewrite bi.wand_curry. rewrite -methods_toks_split. *)
  (*   iIntros "X". iDestruct (methods_toks_sub with "[$]") as %V. *)
  (*   pose proof dequeuer_neq_enqueuer. multiset_solver.  *)
  (* Qed.  *)
    

  (* (* TODO: add bupd to mt_init *) *)
  (* Lemma queue_methods_tokens_init `{MethodTokenPre Σ}: *)
  (*   ⊢ |==> ∃ (MT: MethodToken queue_MS Σ),  *)
  (*       method_tok enqueuer ∗ method_tok dequeuer. *)
  (* Proof using. *)
  (*   iDestruct (mt_init queue_MS) as "(%MT & TOKS)". *)
  (*   setoid_rewrite <- methods_toks_split.   *)
  (*   iExists MT. iFrame. *)
  (*   rewrite /queue_MS. iModIntro. *)
  (*   iApply "TOKS". *)
  (* Qed. *)

  (* Definition queue_MS: gmultiset val := {[+ enqueuer; dequeuer +]}. *)
