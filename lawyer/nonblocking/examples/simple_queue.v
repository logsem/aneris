From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.nonblocking.examples Require Import simple_queue_utils.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From heap_lang Require Import heap_lang_defs lang notation.


Close Scope Z. 

Class QueuePreG Σ := {
  q_pre_max :: MaxExactPreG Σ;
  q_pre_tok :: inG Σ (exclR unitO);
  q_pre_hq :: HistQueuePreG Σ;
  q_pre_rh :: ReadHistPreG Σ;
  q_pre_rprot :: inG Σ (gmapUR nat read_state_cmra);
  q_pre_dangle_rop :: inG Σ (excl_authUR (option nat));
}.


Record SimpleQueue := SQ {     
    Head: loc; Tail: loc; BeingRead: loc; 
    FreeLater: loc; OldHeadVal: loc;
}.

Class QueueG Σ := {
    q_pre :: QueuePreG Σ; 
    
    q_hq :: HistQueueG Σ;
    q_rh :: ReadHistG Σ;

    q_sq: SimpleQueue;

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


Definition get_val: val := λ: "nd", ! ("nd" +ₗ #0).
Definition get_next: val := λ: "nd", ! ("nd" +ₗ #1).

Definition free_el: val. Admitted.

Definition get_to_free '(SQ _ _ BR FL _): val :=
  λ: "ph",
    if: ("ph" = !#BR)
    then
      let: "old_fl" := !#FL in
      #FL <- "ph" ;;
      "old_fl"
    else "ph"
.

Definition dequeue '(SQ H T BR FL OHV as sq): val :=
  λ: "q",
    let: "c" := !#H in
    if: ("c" = !#T)
    then NONE
    else
      let: "v" := get_val "c" in
      #OHV <- "v" ;;
      #H <- (get_next "c") ;;
      let: "to_free" := get_to_free sq "c" in
      free_el "to_free" ;;
      (SOME "v")
.


Section QueueResources. 

  Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.
  
  Context {QL: QueueG Σ}.
  
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
  Definition phys_queue_interp (pq: HistQueue): iProp Σ :=
    ([∗ list] nd ∈ pq, hn_interp nd) ∗
    ∃ (pt: loc), Tail q_sq ↦{1/2} #pt ∗ hn_interp (pt, dummy_node) ∗ ⌜ is_LL_into pq pt ⌝ ∗
    let ph: loc := (from_option (fun hn => hn.1) pt (pq !! 0)) in
    Head q_sq ↦{1/2} #ph
  . 
      
  
  Definition queue_interp (hq: HistQueue) (h t br fl: nat): iProp Σ :=
    let pq := drop h hq in
    ⌜ t = length hq ⌝ ∗ 
    (* ([∗ list] nd ∈ pq, hn_interp nd) ∗ *)
    (* ∃ (pt: loc), Tail q_sq ↦ #pt ∗ hn_interp (pt, dummy_node) ∗ ⌜ is_LL_into pq pt ⌝ ∗ *)
    (* let ph: loc := (from_option (fun hn => hn.1) pt (hq !! h)) in *)
    (* Head q_sq ↦{1/2} #ph ∗ *)
    phys_queue_interp pq ∗ 
    (∃ (nbr: HistNode), ⌜ hq !! br = Some nbr ⌝ ∗ BeingRead q_sq ↦#(nbr.1)) ∗
    (∃ (nfl: HistNode), ⌜ hq !! fl = Some nfl ⌝ ∗ FreeLater q_sq ↦#(nfl.1) ∗ hn_interp nfl)
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
    
  Definition cancel_witness (r: nat): iProp Σ :=
    ∃ r', ⌜ r < r' ⌝ ∗ @me_lb _ q_me_h r'.

  Definition safe_read (r: nat) (h br fl: nat) (od: option nat) rp: iProp Σ :=
    ⌜ r = h ⌝ ∗ (⌜ rp = rs_init ⌝ ∨ ⌜ r = br ⌝ ∗ ⌜ rp = rs_proc (Some rsp_going) ⌝) ∨
    ⌜ r = h - 1 /\ r = br /\ is_Some od ⌝ ∗ ⌜ rp = rs_proc (Some rsp_protected) ⌝ ∨
    ⌜ r = br /\ r = fl ⌝ ∗  ⌜ rp = rs_proc (Some rsp_protected) ⌝
  .

  Definition rop_interp (rop: option nat) (h br fl: nat) (od: option nat): iProp Σ :=
    ∀ i, ⌜ rop = Some i  ⌝ -∗ ∃ r rp, ith_read i r 0 ∗ ith_rp i rp ∗
        (safe_read r h br fl od rp ∨ ⌜ rp = rs_canceled ⌝ ∗ cancel_witness r).
  
  Definition read_head_resources (t br: nat) (pt: loc) (rop: option nat): iProp Σ :=
    @me_exact _ q_me_t t ∗ @me_exact _ q_me_br br ∗ 
    Tail q_sq ↦{1/2} #pt ∗ rop_frag rop.

  Definition dequeue_resources (h fl: nat) (ph: loc) (od: option nat): iProp Σ :=
    @me_exact _ q_me_h h ∗ @me_exact _ q_me_fl fl ∗
    Head q_sq ↦{1/2} #ph ∗ dangle_frag od. 
  
  Definition read_head_token: iProp Σ := own q_γ_tok_rh (Excl ()).
  Definition dequeue_token: iProp Σ := own q_γ_tok_dq (Excl ()).

  Definition hq_state_wf h t br fl: Prop :=
    (* fl <= br /\ *) (* see runs.org for a counterexample *)
    br <= h /\ fl < h /\ h <= t.
    (* THIS IS FALSE: br can fall behind arbitrarily *)
    (* (br = h \/ br = fl \/ od = Some (h - 1) /\ br = h - 1).  *)

  Definition br_lb (b: nat) := @me_lb _ q_me_br b.

  Definition read_hist_wf (hist: read_hist) (rop: option nat) (h: nat) :=
    exists n, dom hist = set_seq 0 (S n) /\ (rop = None \/ rop = Some n) /\ 
           (forall i j opi opj, i < j -> hist !! i = Some opi -> hist !! j = Some opj ->
                           opi.1.2 <= opj.1.1) /\
           (forall i opi, hist !! i = Some opi -> opi.1.1 <= h /\ opi.1.2 <= h).

  Definition old_rps (hist: read_hist) (rop: option nat): iProp Σ :=
    (* [∗ set] i ∈ (dom hist) ∖ (from_option (fun n => {[ n ]}) ∅ rop), *)
    [∗ map] i ↦ '((r, b), rp) ∈ (from_option (fun n => delete n hist) hist rop),
      (* (dom hist) ∖ (from_option (fun n => {[ n ]}) ∅ rop), *)
      ∃ rp, ith_rp i rp ∗ ⌜ rs_fin rp ⌝ ∗
              (* (⌜ rp ≠ rs_canceled ⌝ -∗ br_lb b) *)
              (br_lb r ∨ ⌜ rp = rs_aborted \/ rp = rs_canceled ⌝)
  . 

  (* TODO: upstream, find existing? *)
  Global Instance Persistent_pure_helper P (R: iProp Σ) `{Decision P}:
    (P -> Persistent R) -> Persistent (R ∗ ⌜ P ⌝).
  Proof using.
    intros PR. destruct (decide P).
    - apply bi.sep_persistent; try by apply _. by apply PR.
    - unshelve eapply bi.Persistent_proper. 1: exact (False)%I.
      2: apply _. 
      iSplit.
      + by iIntros "(_&%)".
      + by iIntros "?".
  Qed.

  Global Instance old_rps_pers: forall hist rop, Persistent (old_rps hist rop).
  Proof using.
    intros. rewrite /old_rps. apply big_sepM_persistent.
    intros ? [[??] ?] ITH. simpl. 
    apply bi.exist_persistent. intros rp.
    rewrite bi.sep_assoc bi.sep_comm bi.sep_assoc. 
    apply Persistent_pure_helper; [apply _| ]. 
    intros. destruct H as [-> | [-> | [-> | ->]]]; apply _.
  Qed.

  Definition ohv_interp: iProp Σ := ∃ ohv, OldHeadVal q_sq↦ ohv.

  Definition read_hist_interp hist rop h br fl od: iProp Σ :=
    rop_auth rop ∗
    rop_interp rop h br fl od ∗ read_hist_auth hist ∗
    ⌜ read_hist_wf hist rop h ⌝ ∗ old_rps hist rop
  . 
  
  Definition queue_inv_inner (hq: HistQueue) (h t br fl: nat)
    (rop od: option nat) (hist: read_hist): iProp Σ :=
    hq_auth hq ∗ auths h t br fl ∗ ⌜ hq_state_wf h t br fl ⌝ ∗
    queue_interp hq h t br fl ∗ dangle_interp od h hq ∗ ohv_interp ∗
    read_hist_interp hist rop h br fl od ∗ 
    ((∃ pt, read_head_resources t br pt None) ∨ read_head_token) ∗ 
    ((∃ ph, dequeue_resources h fl ph None) ∨ dequeue_token)
  .
  
  Definition queue_ns := nroot .@ "queue".

  Definition queue_at (q: val): iProp Σ :=
    ⌜ q = (#(Head q_sq), (#(Tail q_sq), (#(BeingRead q_sq), (#(FreeLater q_sq), #(OldHeadVal q_sq)))))%V ⌝. 
  
  (* Definition queue_inv (q: loc): iProp Σ := *)
  Definition queue_inv (q: val): iProp Σ :=
    queue_at q ∗ inv queue_ns 
      (∃ hq h t br fl rop od hist, queue_inv_inner hq h t br fl rop od hist)
  .
  
  Lemma dequeue_token_excl:
    dequeue_token -∗ dequeue_token -∗ False.
  Proof using.
    simpl. 
    rewrite bi.wand_curry -own_op.
    iIntros "X". by iDestruct (own_valid with "[$]") as %V.
  Qed. 
    
  Lemma dequeue_resources_excl h1 fl1 ph1 od1 h2 fl2 ph2 od2:
    dequeue_resources h1 fl1 ph1 od1 -∗ dequeue_resources h2 fl2 ph2 od2 -∗ False.
  Proof using.
    simpl. rewrite /dequeue_resources.
    iIntros "(X&_) (Y&_)".
    by iApply (me_exact_excl with "X [$]"). 
  Qed.

  Lemma dequeue_resources_auth_agree h' fl' ph od h t br fl:
    dequeue_resources h' fl' ph od -∗ auths h t br fl -∗ ⌜ h' = h /\ fl' = fl ⌝.
  Proof using.
    simpl. iIntros "(H&FL&?&?) (H'&?&?&FL')".
    iDestruct (me_auth_exact with "H' H") as %?. 
    iDestruct (me_auth_exact with "FL' FL") as %?.
    done. 
  Qed. 
    
  Lemma dangle_auth_frag_agree od1 od2:
    dangle_auth od1 -∗ dangle_frag od2 -∗ ⌜ od2 = od1 ⌝. 
  Proof using.
    simpl. rewrite /dangle_auth /dangle_frag.
    rewrite bi.wand_curry -own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    iPureIntro. symmetry. by apply excl_auth_agree_L.
  Qed.  
    
  Lemma dangle_update od1 od2 od':
    dangle_auth od1 -∗ dangle_frag od2 ==∗ dangle_auth od' ∗ dangle_frag od'. 
  Proof using.
    simpl. rewrite /dangle_auth /dangle_frag.
    rewrite bi.wand_curry -!own_op.
    iApply own_update. apply excl_auth_update. 
  Qed.  
    
  Lemma dequeue_resources_dangle_agree h fl ph od od' h' hq':
    dequeue_resources h fl ph od -∗ dangle_interp od' h' hq' -∗ ⌜ od' = od ⌝.
  Proof using.
    simpl. iIntros "(?&?&?&FRAG) (AUTH&?)".
    by iDestruct (dangle_auth_frag_agree with "[$] [$]") as %?. 
  Qed.
    
  Lemma dequeue_res_head_agree h fl (ph ph': loc) od:
    dequeue_resources h fl ph od -∗ Head q_sq ↦{1 / 2} #ph' -∗ ⌜ ph' = ph ⌝.
  Proof using.
    simpl. rewrite /dequeue_resources. iIntros "(_&_&H'&?) H".
    iDestruct (pointsto_agree with "[$] [$]") as %?. set_solver.
  Qed.
    
  Lemma cancel_rop h t br fl h'
    (LT: h' < h):
    auths h t br fl -∗ cancel_witness h'.
  Proof using.
    iIntros "(H&?&?&?)".
    rewrite /cancel_witness.
    iDestruct (me_auth_save with "H") as "LB".
    iExists _. by iFrame.
  Qed.
    
  Lemma old_rps_olds hist n:
    old_rps hist (Some n) ⊣⊢ old_rps (delete n hist) None.
  Proof using.
    rewrite /old_rps. simpl. done. 
  Qed.
    
  Lemma br_lb_bound b h t br fl:
    br_lb b -∗ auths h t br fl -∗ ⌜ b <= br ⌝.
  Proof using.
    iIntros "LB (?&?&BR&?)".
    iApply (me_auth_lb with "BR LB").
  Qed.  

  Lemma hn_interp_ptr_excl ptr nd1 nd2:
    hn_interp (ptr, nd1) -∗ hn_interp (ptr, nd2) -∗ False.
  Proof using.
    simpl. destruct nd1, nd2. iIntros "[P1 ?] [P2 ?]".
    iCombine "P1 P2" as "P". iDestruct (pointsto_valid with "P") as %V.
    done.
  Qed.

  Lemma access_queue_ends hq h t br fl:
    hq_auth hq -∗ queue_interp hq h t br fl -∗
      ∃ (ph pt: loc), Head q_sq ↦{1/2} #ph ∗ (Tail q_sq) ↦{1/2} #pt ∗
        (⌜ h >= t /\ ph = pt ⌝ ∨ ⌜ h < t /\ ph ≠ pt ⌝ ∗ ∃ (nd: Node), ith_node h (ph, nd)) ∗
        (Head q_sq ↦{1/2} #ph -∗ (Tail q_sq) ↦{1/2} #pt -∗ hq_auth hq ∗ queue_interp hq h t br fl).
  Proof using.
    simpl. iIntros "[AUTH #FRAGS] QI".
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))".
    
    iFrame "HEAD TAIL".
    rewrite lookup_drop Nat.add_0_r. 
    destruct (Nat.lt_ge_cases h t) as [LT | GE]; subst t.     
    - pose proof LT as [[ph [??]] HTH]%lookup_lt_is_Some_2.
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

  Lemma access_queue hq h t br fl i hn
    (IN: h <= i < t):
    hq_auth hq -∗ queue_interp hq h t br fl -∗ ith_node i hn -∗
    hn_interp hn ∗ (hn_interp hn -∗ queue_interp hq h t br fl ∗ hq_auth hq).
  Proof using.
    simpl. rewrite /queue_interp. iIntros "AUTH (% & PQI & $) #ITH".
    rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))".
    iDestruct (hq_auth_lookup with "[$] [$]") as %ITH.
    apply proj1, Nat.le_sum in IN as [? ->].
    iDestruct (big_sepL_lookup_acc with "Q") as "[HNI CLOS]".
    { erewrite lookup_drop; eauto. }
    iFrame. iIntros. iFrame. repeat iSplit; try done. by iApply "CLOS".     
  Qed. 

  (* (* TODO: also holds if h is not in the hist queue (e.g. initially) *) *)
  (* Lemma queue_interp_ph_neq_pfl' (hq: HistQueue) h t br fl (ptr: loc): *)
  (*   queue_interp hq h t br fl -∗ ⌜ exists nd, hq !! h = Some (ptr, nd) ⌝ -∗ *)
  (*   ⌜ exists nd, hq !! fl = Some (ptr, nd) ⌝ -∗ *)
  (*     False. *)
  (* Proof using. *)
  (*   simpl.  *)
  (*   iIntros "QI (%ndh & %HTH) (%ndfl & %FLTH)". rewrite /queue_interp. *)
  (*   rewrite /queue_interp. iDestruct "QI" as "(%T_LEN &  HNIS & %pt & TAIL & TLI & %LL & HEAD & BR & FL)". *)
  (*   iDestruct "FL" as "(% & %FLTH_ & FL & HNI_FL)". *)
  (*   rewrite FLTH in FLTH_. inversion FLTH_. subst. simpl. *)
  (*   rewrite HTH. simpl. *)
  (*   iDestruct (big_sepL_elem_of with "HNIS") as "II". *)
  (*   { apply elem_of_list_lookup. eexists. *)
  (*     erewrite lookup_drop with (i := 0). *)
  (*     by rewrite Nat.add_0_r. } *)
  (*   simpl. by iDestruct (hn_interp_ptr_excl with "[$] [$]") as "?". *)
  (* Qed.     *)

  Lemma queue_interp_dangle_neq_pfl' (hq: HistQueue) h t br fl (ptr: loc):
    queue_interp hq h t br fl -∗
     dangle_interp (Some (h - 1)) h hq -∗
    ⌜ exists nd, hq !! fl = Some (ptr, nd) ⌝ -∗
    ⌜ exists nd, hq !! (h - 1) = Some (ptr, nd) ⌝ -∗
      False.
  Proof using.
    simpl. 
    iIntros "QI DI (%ndfl & %FLTH) (% & %DTH)".
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN & PQI & BR & FL)".
    rewrite /phys_queue_interp. iDestruct "PQI" as "(Q & (%pt & TAIL & DUMMY & %LL & HEAD))".
    iDestruct "FL" as "(% & %FLTH_ & FL & HNI_FL)".
    rewrite FLTH in FLTH_. inversion FLTH_. subst. simpl.
    rewrite /dangle_interp.
    iDestruct "DI" as "(AUTH & [% | (_ & HNI)])".
    { done. }
    rewrite  DTH. simpl.
    by iDestruct (hn_interp_ptr_excl with "[$] [$]") as "?".
  Qed.

End QueueResources.
