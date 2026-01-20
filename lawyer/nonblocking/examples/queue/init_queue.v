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

  (* TODO: move *)
  Definition enqueuer: val. Admitted. 
  Definition dequeuer: val. Admitted. 

  Definition queue_MS: gmultiset val := {[+ enqueuer; dequeuer +]}.

  (* TODO: add bupd to mt_init *)
  Lemma queue_methods_tokens_init `{MethodTokenPre Σ}:
    ⊢ |==> ∃ (MT: MethodToken queue_MS Σ), 
        method_tok enqueuer ∗ method_tok dequeuer.
  Proof using.
    iDestruct (mt_init queue_MS) as "(%MT & TOKS)".
    setoid_rewrite <- methods_toks_split.  
    iExists MT. iFrame.
    rewrite /queue_MS. iModIntro.
    iApply "TOKS".
  Qed.

  (* Lemma auths_exacts_init `{MaxExactPreG Σ} (n0 n1 n2 n3 n4: nat): *)
  (*   ⊢ |==> ∃ (ME0 ME1 ME2 ME3 ME4: MaxExactG Σ), *)
  (*       let ns := [n0; n1; n2; n3; n4] in *)
  (*       let MES := [ME0; ME1; ME2; ME3; ME4] in *)
  (*       ([∗ list] _ ↦ n;ME ∈ ns; MES, @me_auth _ ME n) ∗  *)
  (*       ([∗ list] _ ↦ n;ME ∈ ns; MES, @me_exact _ ME n). *)
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
                                
  (* Lemma read_hist_init `{ReadHistPreG Σ} (hist: read_hist) *)
  (*   (RS_INIT: forall i op, hist !! i = Some op -> op.2 = rs_init): *)
  (*   ⊢ (|==> ∃ (_: ReadHistG Σ), read_hist_auth hist)%I. *)

  Definition hist0: read_hist := {[ 0 := ((0, 0), rs_proc $ Some rsp_completed )]}.
  
  Lemma read_hist_init `{ReadHistPreG Σ}:
    ⊢ |==> ∃ (_: ReadHistG Σ), read_hist_auth hist0
                                 ∗ ith_rp 0 (rs_proc $ Some rsp_completed)
  .
  Proof using.
    




    iMod (let hist' := (((fun '(r, b, p) => (Some (to_agree r, MaxNat b), Some $ rs2cmra p)) <$> hist0): gmapUR _ _) in
          let hist'' := (((fun '(r, b, p) => (Some (to_agree r, MaxNat b), None)) <$> hist0): gmapUR _ _) in
          own_alloc (● hist' ⋅ ◯ hist'')) as "(%γ & HIST)".
    { apply auth_both_valid_2.
      - unfold hist0. rewrite map_fmap_singleton.
        apply singleton_valid. done.
      - unfold hist0. rewrite !map_fmap_singleton. simpl.
        apply singleton_included. apply Some_included_total.
        apply pair_included. split; [done| ].
        apply option_included. tauto. }
        
    iModIntro. iExists {| rh_γ__map := γ |}.
    iFrame. 
  Qed.

  Context `{QueuePreG Σ, heap1GS Σ, invGS_gen HasNoLc Σ, MethodTokenPre Σ}.
  Context (PE: val -> iProp Σ). 

  (* TODO: move/upstream *)
  Lemma bi_exist_pair {A B: Type} (P: A -> B -> iProp Σ):
    (∃ (a: A) (b: B), P a b) ⊣⊢ ∃ (ab: A * B), P ab.1 ab.2.
  Proof using.
    iSplit.
    - iIntros "(%&%&?)". by iExists (_, _).
    - iIntros "(%ab&?)". destruct ab. iFrame.
  Qed.

  Lemma queue_init sq (pfl ph: loc) (v: val):
    let '(SQ H T BR FL OHV) := sq in
    (* hn_interp (ptr, dummy_node) *)
    ([∗ list] ptr ∈ [BR; FL], ptr ↦ #pfl) -∗
    ([∗ list] ptr ∈ [H; T], ptr ↦ #ph) -∗
    OHV ↦ v -∗ 
    hn_interp (ph, dummy_node) -∗
    hn_interp (pfl, (v, ph)) -∗
    PE v
    ={⊤}=∗
    ∃ qv (_: QueueG Σ), queue_inv PE qv ∗ read_head_token ∗ dequeue_token. 
  Proof using.
    destruct sq eqn:SQ. simpl.
    iIntros "(BR & FL & _) (H & T & _) OHV HNh HNfl PEv".

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
    iMod read_hist_init as "(%RHIST & HIST)".
    iMod queue_methods_tokens_init as "(%MT & ETOK & DTOK)".

    iMod (auths_exacts_init [1; 1; 0; 0]) as "(%MES & AUTHS & EXS)".
    iDestruct (big_sepL2_length with "AUTHS") as %ME_LEN. simpl in ME_LEN.
    do 5 (destruct MES; simpl in ME_LEN; try lia). 
    
    iModIntro. iExists _.
    iExists (Build_QueueG _ _ _ _ sq _ _ _ _ _ _ m m0 m1 m2).
    iSplitR.
    { rewrite /queue_at. simpl. iPureIntro. reflexivity. }
    iSplitR "ETOK DTOK".
    { iFrame "HQ". 
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

      iSplitL "OHV PEv".
      { rewrite SQ /=. iFrame. }

      iSplitL "HIST RAUTH".
      { iDestruct (read_hist_update' with "HIST") as k
        iFrame. iSplit; [| iSplit]. 
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
          iExists
          
            
        iSplit. 
          
      
      iFrame. 
      rewrite bi.sep_exist_r. 
      
    
    
    (*     q_hq :: HistQueueG Σ; *)
    (* q_rh :: ReadHistG Σ; *)

    q_sq := _;

    (* q_γ_tok_rh : gname; *)
    (* q_γ_tok_dq: gname; *)
    (* TODO: remove it *)
    q_γ_tok_cc := γ_rop;
    q_γ_tok_rop := γ_rop;

    q_γ_dangle := γ_d; 
    q_γ_rop := γ_rtok;

    q_me_h :: MaxExactG Σ;
    q_me_t :: MaxExactG Σ;
    q_me_br :: MaxExactG Σ;
    q_me_fl :: MaxExactG Σ;
}
    
                                     
  
End InitQueue.
