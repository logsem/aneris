From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.nonblocking.examples Require Import simple_queue_utils.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Close Scope Z.


Class QueuePreG Σ := {
  q_pre_max :: MaxExactPreG Σ;
  q_pre_tok :: inG Σ (exclR unitO);
  q_pre_hq :: HistQueuePreG Σ;
  q_pre_rh :: ReadHistPreG Σ;
  q_pre_rprot :: inG Σ (gmapUR nat read_state_cmra);
  q_pre_dangle_rop :: inG Σ (excl_authUR (option nat));
}.


Class QueueG Σ := {
    q_pre :: QueuePreG Σ; 
    
    Head: loc; Tail: loc; BeingRead: loc; 
    FreeLater: loc; OldHeadVal: loc;

    q_hq :: HistQueueG Σ;
    q_rh :: ReadHistG Σ;

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
    
    Definition cancel_witness (r: nat): iProp Σ :=
      ∃ r', ⌜ r < r' ⌝ ∗ @me_lb _ q_me_h r'.

    Definition rop_token: iProp Σ := own q_γ_tok_rop (Excl ()).

    Definition safe_read (r: nat) (h br fl: nat) (od: option nat) rp: iProp Σ :=
      ⌜ r = h ⌝ ∗ (⌜ rp = rs_init ⌝ ∨ ⌜ r = br ⌝ ∗ ⌜ rp = rs_going ⌝ ∗ rop_token) ∨
      ⌜ r = h - 1 /\ r = br /\ is_Some od ⌝ ∗ ⌜ rp = rs_protected ⌝ ∨
      ⌜ r = br /\ r = fl ⌝ ∗  ⌜ rp = rs_protected ⌝
    .

    Definition rop_interp (rop: option nat) (h br fl: nat) (od: option nat): iProp Σ :=
      ∀ i, ⌜ rop = Some i  ⌝ -∗ ∃ r rp, ith_read i r 0 ∗ ith_rp i rp ∗
                     (safe_read r h br fl od rp ∨ ⌜ rp = rs_canceled ⌝ ∗ cancel_witness r).
  
    Definition read_head_resources (t br: nat): iProp Σ :=
      @me_exact _ q_me_t t ∗ @me_exact _ q_me_br br ∗ rop_frag None ∗ rop_token.

    Definition dequeue_resources (h fl: nat) (ph: loc) (od: option nat): iProp Σ :=
      @me_exact _ q_me_h h ∗ @me_exact _ q_me_fl fl ∗
      Head ↦{1/2} #ph ∗ dangle_frag od. 
  
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
                      br_lb r
    
    . 
            (* (let dom_fin := set_seq 0 (if rop then n else (S n)): gset nat in *)
            (*  forall i op, i ∈ dom_fin -> hist !! i = Some op -> rs_fin op.2). *)

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

    Global Instance rs_fin_dec rs: Decision (rs_fin rs).
    Proof.
      rewrite /rs_fin. destruct rs.
      all: try by (left; tauto).
      all: right; intros ?; set_solver. 
    Qed. 

    Global Instance old_rps_pers: forall hist rop, Persistent (old_rps hist rop).
    Proof using.
      intros. rewrite /old_rps. apply big_sepM_persistent.
      intros ? [[??] ?] ITH. simpl. 
      apply bi.exist_persistent. intros rp.
      rewrite bi.sep_assoc bi.sep_comm bi.sep_assoc. 
      apply Persistent_pure_helper; [apply _| ]. 
      intros. destruct H as [-> | [-> | ->]]; apply _.
    Qed.
    
    Definition queue_inv_inner (hq: HistQueue) (h t br fl: nat)
      (rop od: option nat) (hist: read_hist) (ohv: val): iProp Σ :=
      hq_auth hq ∗ 
      queue_interp hq h t br fl ∗ dangle_interp od h hq ∗ OldHeadVal ↦ ohv ∗
      ⌜ hq_state_wf h t br fl ⌝ ∗
      auths h t br fl ∗
      rop_interp rop h br fl od ∗
      read_hist_auth hist ∗ ⌜ read_hist_wf hist rop h ⌝ ∗ old_rps hist rop ∗
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
        (∃ hq h t br fl rop od hist ohv, queue_inv_inner hq h t br fl rop od hist ohv)
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
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >ROP & RHIST & >%RH_WF & RH & DQ)".
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
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od' & %hist & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >ROP & RHIST & >%RH_WF & RH & DQ)".
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
    iInv "INV" as "(%hq & %h & %t & %br & %fl & %rop & %od & %hist & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & DANGLE & OHV & >%ORDER & >AUTHS & >ROP & RHIST & >%RH_WF & RH & DQ)".

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
    auths h t br fl -∗ cancel_witness h'.
  Proof using.
    iIntros "(H&?&?&?)".
    rewrite /cancel_witness.
    iDestruct (me_auth_save with "H") as "LB".
    iExists _. by iFrame.
  Qed.

  Lemma dom_max_set_fold n:
    set_fold max 0 (set_seq 0 (S n): gset nat) = n.
  Proof using.
    clear. induction n.
    { done. }
    rewrite set_seq_S_end_union_L.
    rewrite union_comm_L. 
    erewrite set_fold_union.
    2-4: red; lia.
    simpl. rewrite IHn.
    rewrite set_fold_singleton. lia.
  Qed. 

  Lemma read_hist_wf_bump (hist: read_hist) rop h rp
    (RH_WF: read_hist_wf hist rop h)
    (n := set_fold max 0 (dom hist)):
  read_hist_auth hist
    -∗ ith_rp n rp
    ==∗
    let rp' := (if decide (rp = rs_init) then rs_canceled
                   else if decide (rp = rs_going) then rs_protected
                   else rp) in
  ∃ r (* b *), let hist' := <[ n := ((r, h + 1), rp') ]> hist in
         read_hist_auth hist' ∗ ith_read n r (h + 1) ∗ ⌜ read_hist_wf hist' rop (h + 1) ⌝ ∗
         ith_rp n rp' ∗
         (* ∗ br_lb b ∗ (⌜ b < h ⌝ -∗ ith_rp i rs_canceled) ∗ *)
         ⌜ r <= h ⌝.
  Proof using.
    rewrite /read_hist_wf. iIntros "AUTH RP".
    destruct RH_WF as (n_ & DOM & ROP & SEQ & BB).

    assert (n_ = n) as ->.
    { subst n. rewrite DOM. by rewrite dom_max_set_fold. }

    destruct (hist !! n) as [[[r b0] p]| ] eqn:NTH.
    2: { apply not_elem_of_dom in NTH. rewrite DOM in NTH.
         rewrite elem_of_set_seq in NTH. lia. }

    remember (if decide (rp = rs_init) then rs_canceled
                   else if decide (rp = rs_going) then rs_protected
                   else rp) as rp'. 

    iDestruct (ith_rp_hist_compat with "[$] [$]") as %(? & ? & EQ').
    rewrite NTH in H. inversion H. subst x. simpl in EQ'. subst p. clear H.  
    
    iMod (read_hist_update' _ _ _ _ (h + 1) rp rp' with "AUTH RP") as "(AUTH & #ITH & RP)".
    { apply NTH. }
    { rewrite Heqrp'. 
      rewrite /rs_wip. destruct rp; tauto. }
    rewrite Nat.max_r.
    2: { apply BB in NTH. simpl in NTH. lia. }
    iModIntro. do 1 iExists _. iFrame "#∗".
    iPureIntro. split.
    2: { eapply BB in NTH; eauto. by apply NTH. }

    exists n. split; [| split; [| split]]. 
    - rewrite dom_insert_L. apply mk_is_Some, elem_of_dom in NTH. set_solver.
    - done.
    - intros ?????. rewrite !lookup_insert_Some.
      intros [(? & ?) | (? & ITH) ] [(? & ?) | (? & JTH) ]; subst; simpl in *; try lia.
      + apply mk_is_Some, elem_of_dom in JTH.
        rewrite DOM elem_of_union elem_of_set_seq elem_of_singleton in JTH. lia.
      + eapply SEQ in H; eauto. done.
      + eapply SEQ; eauto.
    - intros ??. rewrite lookup_insert_Some.         
      intros [(? & ?) | (? & ITH) ]; subst; simpl; try lia.
      { eapply BB in NTH; eauto. simpl in NTH. lia. }
      eapply BB in ITH; eauto. lia.
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

  Lemma dequeue_upd_head_spec l τ π q h ph vh (nxh: loc) fl:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in ith_node h (ph, (vh, nxh))) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources h fl ph None) }}}
      #Head <- #nxh @τ
    {{{ RET #(); th_phase_frag τ π q ∗ (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources (h + 1) fl nxh (Some h)) ∗
                   ∃ i r b, ith_read i r (h + 1) ∗ ⌜ r <= h ⌝ ∗
                               br_lb b ∗
                               (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i rs_completed)) }}}.
  Proof using.
    simpl.
    iIntros (Φ) "([#QAT #INV] & #HTH & PH & CPS & DR) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & >DANGLE & OHV & >%ORDER & >AUTHS & >ROP & >RHIST & >%RH_WF & >#OLDS & >RH & >DQ)".
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
    
    iDestruct (take_snapshot with "[$]") as "#SHT".
    iDestruct "SHT" as "(_&_&#BR_LB&_)". 

    rewrite /rop_interp.
    destruct rop as [n| ]. 
    - iDestruct ("ROP" with "[//]") as "(%r & %rp & READ_ & RP & ROP)".      
      destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ]. subst n'. 
      iMod (read_hist_wf_bump with "[$] [RP]") as "(%r' & RHIST & #READ & %RH_WF' & RP & %READ_BOUND)".
      { eexists. eauto. }
      { rewrite DOM dom_max_set_fold. iFrame. }
      rewrite DOM dom_max_set_fold. 
      iDestruct (ith_read_agree with "READ READ_") as %<-.
      iFrame "READ". iFrame "%". iFrame "BR_LB". 
      rewrite -(bi.sep_True' ( ⌜ _ ⌝ -∗ _ )%I). iApply fupd_frame_l. iSplit.
      { iIntros (LT). iDestruct "ROP" as "[SAFE | [-> _]]".
        2: { do 2 (erewrite decide_False; [| done]). iFrame. }
        iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
        - iDestruct "FROM_HEAD" as "[-> [-> | (-> & -> & ?)]]".
          + erewrite decide_True; [| done]. iFrame.
          + lia. 
        - iDestruct "FROM_DANGLE" as "[(-> & -> & %X) ?]".
          clear -X. by destruct X. 
        - iDestruct "FROM_BR" as "([-> ->] & ->)". lia. } 

      iClear "HTH CPS".
      iMod ("CLOS" with "[-]") as "_"; [| done].
      iFrame "QI AUTHS OHV HQ RH DAUTH TOK RHIST". iNext.
      iExists _. rewrite Nat.add_sub. rewrite HTH /=.
      
      iSplitL "HNI". 
      { iRight. by iFrame. }
      iSplit.
      { iPureIntro. red. red in ORDER. repeat split; try lia. }
      rewrite DOM dom_max_set_fold in RH_WF'.
      iFrame "%". 
      iSplit.
      2: { iApply old_rps_olds.
           iDestruct (old_rps_olds with "OLDS") as "foo". 
           by rewrite delete_insert_delete. }
      rewrite /rop_interp. iIntros (i_ [=]). subst i_. 

      iFrame "READ_ RP". 
      iDestruct "ROP" as "[[HEAD | [DANGLE | FL]] | CANCEL_WITNESS]".
      + iDestruct "HEAD" as "(-> & [-> | (-> & -> & TOK)])".
        * iRight. iFrame "#∗". erewrite decide_True; [| done]. done.   
        * iLeft. iRight. iLeft. iFrame.
          iPureIntro. split.
          ** split; [lia | done].
          ** erewrite decide_False; [| done]. erewrite decide_True; [| done]. done.
      + iDestruct "DANGLE" as "((_ & _ & %) & _)". by destruct H.
      + iDestruct "FL"as "([-> ->] & ->)". 
        iLeft. rewrite /safe_read.
        repeat iRight.  iPureIntro. split; [done| ]. 
        do 2 (erewrite decide_False; [| done]). done.
      + iDestruct "CANCEL_WITNESS" as "(-> & CW)".
        iRight. iFrame.
        iPureIntro. do 2 (erewrite decide_False; [| done]). done.
    - destruct RH_WF as (n & DOM & [? | [=]] & RH_WF).
      destruct (hist !! n) as [[[??]?] | ] eqn:NTH. 
      2: { apply not_elem_of_dom in NTH. rewrite DOM in NTH.
           rewrite elem_of_set_seq in NTH. lia. }
      iDestruct (big_sepM_lookup  with "OLDS") as "RP".
      { simpl. apply NTH. } 
      iDestruct "RP" as "(%rp & RP & %FIN & #LB)".
      iDestruct (ith_rp_hist_compat with "[$] [$]") as %(? & ? & EQ').
      rewrite NTH in H0. inversion H0. subst x. subst rp. simpl in *.
      rename r into rp. clear H0.

      iDestruct (read_hist_get hist n with "RHIST") as "#READ".
      { rewrite NTH. repeat f_equal. }
      
      iMod (read_hist_wf_bump with "[$] [RP]") as "(%r' & RHIST & #READ' & %RH_WF' & RP_ & %READ_BOUND)".
      { eexists. eauto. }
      { rewrite DOM dom_max_set_fold. iFrame "RP". }
      rewrite decide_False.
      2: { red in FIN. destruct rp; set_solver. }
      rewrite decide_False.
      2: { red in FIN. destruct rp; set_solver. }
      rewrite DOM dom_max_set_fold.
      iDestruct (ith_read_agree with "READ READ'") as %->.
      iFrame "% READ' BR_LB".
      rewrite -(bi.sep_True' ( ⌜ _ ⌝ -∗ _ )%I). iApply fupd_frame_l. iSplit.
      { iIntros (LT). destruct FIN as [-> | [-> | ->]].
        all: try by iFrame.
        iDestruct (br_lb_bound with "[$] [$]") as %?. lia. }

      iMod ("CLOS" with "[-]") as "_"; [| done].
      iFrame "QI AUTHS OHV HQ RH DAUTH TOK RHIST". iNext.
      iExists _. rewrite Nat.add_sub. rewrite HTH /=.
      
      iSplitL "HNI". 
      { iRight. by iFrame. }
      iSplit.
      { iPureIntro. red. red in ORDER. repeat split; try lia. }
      rewrite DOM dom_max_set_fold in RH_WF'.
      do 2 (rewrite decide_False in RH_WF'; [| destruct FIN as [->| [->| ->]]; done]).
      destruct RH_WF as (SEQ &  BB). 
      Unshelve. 2: exact None. 
      rewrite bi.sep_assoc.
      
      iSplitR.
      2: { (* TODO: make a lemma? *)
        rewrite /old_rps. simpl.
        rewrite -insert_delete_insert.         
        rewrite insert_union_singleton_l big_sepM_union.
        2: { apply map_disjoint_dom. rewrite dom_insert_L. set_solver. }
        iSplitL.
        2: { iApply (big_sepM_subseteq with "[$]"). apply delete_subseteq. }
        rewrite big_sepM_singleton. iFrame. iFrame "% #". } 
      rewrite /rop_interp. iSplit. 
      { iIntros (i_ [=]). }

      (* TODO: make a lemma *)
      rewrite /read_hist_wf.
      iPureIntro. 

      exists n. split; [| split; [| split]]. 
    + rewrite dom_insert_L. apply mk_is_Some, elem_of_dom in NTH. set_solver.
    + tauto. 
    + intros ?????. rewrite !lookup_insert_Some.
      intros [(? & ?) | (? & ITH) ] [(? & ?) | (? & JTH) ]; subst; simpl in *; try lia.
      * apply mk_is_Some, elem_of_dom in JTH.
        rewrite DOM elem_of_union elem_of_set_seq elem_of_singleton in JTH. lia.
      * eapply SEQ in H0; eauto. done.
      * eapply SEQ; eauto.
    + intros ??. rewrite lookup_insert_Some.         
      intros [(? & ?) | (? & ITH) ]; subst; simpl; try lia.
      eapply BB in ITH; eauto. simpl in ITH. lia.
  Qed.

  Definition dequeue_fuel := 100.    

  Lemma check_BR_spec l τ π q h (* t *) (* br *) fl ph ndh i r b0
    (READ_BOUND: r <= h):
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in ith_node h (ph, ndh)) ∗
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources (h + 1) fl ndh.2 (Some h)) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel ∗
        ith_read i r (h + 1) ∗ br_lb b0
    }}}
      ! #BeingRead @τ
    {{{ (pbr: loc), RET #pbr; th_phase_frag τ π q ∗
            (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources (h + 1) fl ndh.2 (if (decide (pbr = ph)) then Some h else None)) ∗
            (⌜ pbr = ph ⌝ ∨ 
             ⌜ pbr ≠ ph ⌝ ∗ (let _: heap1GS Σ := iem_phys _ EM in  hn_interp (ph, ndh))) ∗
            ∃ b' ndbr', br_lb b' ∗ ⌜ b0 <= b' ⌝ ∗ ith_node b' (pbr, ndbr')
    }}}.
  Proof using.
    iIntros (Φ) "([#QAT #INV] & #HTH & DR& PH & CPS & #READ & #BR0) POST".
    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & >DANGLE & OHV & >%ORDER & >AUTHS & >ROP & >RHIST & >%RH_WF & >#OLDS & >RH & >DQ)".
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

    (* iCombine "HEAD HEAD'" as "HEAD".  *)
    iApply sswp_MU_wp; [done| ]. 
    iApply (wp_load with "BR"). iIntros "!> BR".
    MU_by_burn_cp. iApply wp_value.

    iApply "POST". iFrame.

    iDestruct (br_lb_bound with "BR0 AUTHS") as %BR0. 
    iDestruct (take_snapshot with "[$]") as "#SHT".
    iDestruct (hq_auth_get_ith with "HQ") as "[#BRTH' HQ]".
    { apply BRTH. }
    iFrame "BRTH'". 

    iAssert (queue_interp hq (h + 1) t br fl)%I
      with "[HNIS TAIL TLI HEAD BR FL]" as "QI".
    { by iFrame. }
    iAssert (br_lb br ∗ ⌜b0 ≤ br⌝)%I as "$".
    { iSplit; [| done].
      iDestruct "SHT" as "(?&?&?&?)". done. }

    simpl.
    destruct (decide (pbr = ph)) as [-> | NEQ].
    -
      iFrame. 
      iMod ("CLOS" with "[-]") as "_".
      { iFrame "#∗ %". iNext.
        rewrite Nat.add_sub HTH /=.
        iRight. by iFrame. }
      iModIntro. by iLeft.
    - iDestruct (ith_read_hist_compat with "[$] [$]") as %(b & p & READ & INCR_BOUND). 
      iMod (dangle_update _ _ None with "[$] [$]") as "[DAUTH DFRAG]".
      iFrame.      
      iApply fupd_or. iRight. iFrame "HNI".
      rewrite -(bi.sep_True' ⌜ _ ≠ _ ⌝%I). iApply fupd_frame_l. iSplit; [done| ].
      iMod ("CLOS" with "[-]") as "_"; [| done]. 

      rewrite /rop_interp.
      destruct rop.
      2: { iFrame "#∗ %". iNext. iSplitR.
           { by iLeft. }
           rewrite /rop_interp. by iIntros (??). }
      
      iDestruct ("ROP" with "[//]") as "(%r_ & %rp & READ_ & RP & ROP)".
      iDestruct (ith_read_hist_compat with "[$] READ_") as %(?&? & READ' & _). 

      iFrame "#∗ %". iNext. iSplitR.
      { by iLeft. }
      rewrite /rop_interp.
      iIntros (i' [=]). subst n.
      iDestruct "ROP" as "[SAFE | $]".
      2: { iFrame "#∗". }

      destruct (decide (i' = i)). 
      { subst. rewrite {1}/safe_read. rewrite Nat.add_sub.
        iFrame "READ_". 
        iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
        - iFrame.
        - iDestruct "FROM_DANGLE" as "[(-> & -> & _) ?]".
          congruence.
        - iFrame. }

      assert (i < i') as NEW.
      { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
        subst i'.
        apply mk_is_Some, elem_of_dom in READ. rewrite DOM elem_of_set_seq in READ.
        lia. }
      clear n.
      
      assert (h + 1 <= r_) as READ'_BOUND.
      { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
        subst. 
        apply proj1 in RH_WF. eapply RH_WF in NEW; eauto. simpl in NEW. lia. }
      iFrame "READ_".
      rewrite {1}/safe_read.
      iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
      + iFrame.
      + iDestruct "FROM_DANGLE" as "[(-> & -> & _) ?]". lia.
      + iFrame.
  Qed.

  Lemma read_FL_spec τ π h q fl nd od:
  {{{ (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources h fl nd od) ∗
      cp π d ∗ th_phase_frag τ π q }}}
  ! #FreeLater @τ
  {{{ RET (#fl); (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources h fl nd od) ∗
 th_phase_frag τ π q }}}.
  Proof using. Admitted.

  Lemma hn_interp_ptr_excl ptr nd1 nd2:
    (let _: heap1GS Σ := iem_phys _ EM in hn_interp (ptr, nd1)) -∗
    (let _: heap1GS Σ := iem_phys _ EM in hn_interp (ptr, nd2)) -∗ False.
  Proof using.
    simpl. destruct nd1, nd2. iIntros "[P1 ?] [P2 ?]".
    iCombine "P1 P2" as "P". iDestruct (pointsto_valid with "P") as %V.
    done.
  Qed.

  (* TODO: also holds if h is not in the hist queue (e.g. initially) *)
  Lemma queue_interp_ph_neq_pfl' (hq: HistQueue) h t br fl (ptr: loc):
    (let _: heap1GS Σ := iem_phys _ EM in queue_interp hq h t br fl) -∗
    ⌜ exists nd, hq !! h = Some (ptr, nd) ⌝ -∗ ⌜ exists nd, hq !! fl = Some (ptr, nd) ⌝ -∗
      False.
  Proof using.
    simpl. 
    iIntros "QI (%ndh & %HTH) (%ndfl & %FLTH)". rewrite /queue_interp.
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN &  HNIS & %pt & TAIL & TLI & %LL & HEAD & BR & FL)".
    iDestruct "FL" as "(% & %FLTH_ & FL & HNI_FL)".
    rewrite FLTH in FLTH_. inversion FLTH_. subst. simpl.
    rewrite HTH. simpl.
    iDestruct (big_sepL_elem_of with "HNIS") as "II".
    { apply elem_of_list_lookup. eexists.
      erewrite lookup_drop with (i := 0).
      by rewrite Nat.add_0_r. }
    simpl. by iDestruct (hn_interp_ptr_excl with "[$] [$]") as "?".
  Qed.    

  Lemma queue_interp_dangle_neq_pfl' (hq: HistQueue) h t br fl (ptr: loc):
    (let _: heap1GS Σ := iem_phys _ EM in queue_interp hq h t br fl) -∗
    (let _: heap1GS Σ := iem_phys _ EM in dangle_interp (Some (h - 1)) h hq) -∗
    ⌜ exists nd, hq !! fl = Some (ptr, nd) ⌝ -∗
    ⌜ exists nd, hq !! (h - 1) = Some (ptr, nd) ⌝ -∗
      False.
  Proof using.
    simpl. 
    iIntros "QI DI (%ndfl & %FLTH) (% & %DTH)". rewrite /queue_interp.
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN &  HNIS & %pt & TAIL & TLI & %LL & HEAD & BR & FL)".
    iDestruct "FL" as "(% & %FLTH_ & FL & HNI_FL)".
    rewrite FLTH in FLTH_. inversion FLTH_. subst. simpl.
    rewrite /dangle_interp.
    iDestruct "DI" as "(AUTH & [% | (_ & HNI)])".
    { done. }
    rewrite  DTH. simpl.
    by iDestruct (hn_interp_ptr_excl with "[$] [$]") as "?".
  Qed.

  Lemma get_to_free_spec 
    l τ π q h fl (ph: loc) ndh i r b
    (READ_BOUND: r <= h):
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in ith_node h (ph, ndh)) ∗
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_resources (h + 1) fl ndh.2 (Some h)) ∗ 
        th_phase_frag τ π q ∗ cp_mul π d (get_loc_fuel + get_loc_fuel + get_loc_fuel) ∗
        ith_read i r (h + 1) ∗
        br_lb b ∗ (⌜ b < r ⌝ -∗ (ith_rp i rs_canceled ∨ ith_rp i rs_completed))
    }}}
        (if: (#ph = !#BeingRead)
        then
            let: "old_fl" := !#FreeLater in
            #FreeLater <- #ph ;;
            "old_fl"
            else #ph) @ τ
    {{{ (to_free: loc), RET #to_free;
        ∃ hn, (let _: heap1GS Σ := iem_phys _ EM in hn_interp (to_free, hn)) ∗ th_phase_frag τ π q }}}.
  Proof using.
    simpl.
    iIntros (Φ) "([#QAT #INV] & #HTH & DR& PH & CPS & #READ & #BR0 & #NO_FL) POST".

    split_cps "CPS" get_loc_fuel.
    wp_bind (! _)%E.
    iApply (check_BR_spec with "[-POST CPS]").
    { apply READ_BOUND. }
    { iFrame "#∗". }
    iIntros "!> %pbr (PH & DR & RES)".
    iDestruct "RES" as "(RES & %b1 & %ndbr1 & #BR1 & %LEb & #BRTH1)". 

    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { set_solver. }
    MU_by_burn_cp. iApply wp_value.

    iDestruct "RES" as "[%PTR_EQ | [%NEQ HNI]]".
    2: { rewrite bool_decide_false; [| set_solver]. rewrite decide_False; [| done].
         pure_steps. iApply "POST". iFrame. }

    rewrite PTR_EQ. 

    rewrite bool_decide_true; [| set_solver]. rewrite decide_True; [| done].
    pure_steps.

    wp_bind (! _)%E.
    split_cps "CPS" 1. rewrite -cp_mul_1.
    iApply (read_FL_spec with "[-POST CPS]").
    { iFrame "#∗". }
    iIntros "!> [DR PH]".

    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (_ <- _)%E.

    iInv "INV" as "(%hq & %h_ & %t & %br & %fl_ & %rop & %od_ & %hist & %ohv & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >QI & >DANGLE & OHV & >%ORDER & >AUTHS & >ROP & >RHIST & >%RH_WF & >#OLDS & >RH & >DQ)".
    iDestruct "DQ" as "[(% & DR') | TOK]".
    { by iDestruct (dequeue_resources_excl with "[$] [$]") as "?". }
    iDestruct (dequeue_resources_auth_agree with "[$] [$]") as %[<- <-]. 
    iDestruct (dequeue_resources_dangle_agree with "[$] [$]") as %->.

    iClear "INV QAT".

    (* TODO: split into lemmas *)
    iDestruct (hq_auth_lookup with "[$] HTH") as %HTH.
    iAssert (⌜ t ≠ h ⌝)%I as %NEMPTY.
    { iIntros (->). red in ORDER. lia. }

    iPoseProof (queue_interp_dangle_neq_pfl' _ _ _ _ _ ph with "QI [DANGLE]") as "#PFL_NEQ_D".
    { by rewrite Nat.add_sub. }

    rewrite /dangle_interp. iDestruct "DANGLE" as "(DAUTH & [% | (_ & HNI)])"; [done| ].
    rewrite Nat.add_sub HTH /=. 
    rewrite /dequeue_resources. iDestruct "DR" as "(CH & CFL & HEAD' & DFRAG)".

    
    rewrite /queue_interp. iDestruct "QI" as "(%T_LEN &  HNIS & %pt & TAIL & TLI & %LL & HEAD & BR & FL)".
    iDestruct "BR" as "(%nbr & %BRTH & BR)".
    
    iDestruct (br_lb_bound with "BR1 AUTHS") as %BR1. 

    subst pbr. 
    destruct nbr as [pbr nbr].

    (* iCombine "HEAD HEAD'" as "HEAD".  *)
    iApply sswp_MU_wp; [done| ].

    iDestruct "FL" as "(%nfl & %FLTH & FL & HNI_FL)". 
    iApply (wp_store with "FL"). iIntros "!> FL".
    MU_by_burn_cp. iApply wp_value.

    iMod (dangle_update _ _ None with "[$] [$]") as "[DAUTH DFRAG]".
    iAssert (|==> auths (h + 1) t br h ∗ @me_exact _ q_me_fl h)%I with "[CFL AUTHS]" as "UPD".
    { rewrite /auths. iDestruct "AUTHS" as "(?&?&?&A)". iFrame.
      iApply (me_update with "A CFL"). red in ORDER. lia. }
    iMod "UPD" as "[AUTHS CFL]".

    iDestruct (br_lb_bound with "BR0 [$]") as %BR0. 
    iAssert (queue_interp hq (h + 1) t br h)%I
      with "[HNIS TAIL TLI HEAD BR FL HNI]" as "QI".
    { iFrame. 
      iSplit; [done| ].
      iFrame "%". iFrame. } 

    rewrite /rop_interp.
    destruct rop. 
    - iDestruct ("ROP" with "[//]") as "(%r_ & %rp & READ_ & RP & ROP)".
      iDestruct (ith_read_hist_compat with "[$] READ_") as %(?&? & READ' & _). 
      iDestruct (ith_read_hist_compat with "[$] READ") as %(?&? & READ & BB).
      iDestruct (hq_auth_lookup with "[$] BRTH1") as %BRTH1.
      
      iAssert (dequeue_resources (h + 1) h ndh.2 None)%I with "[CH CFL HEAD' DFRAG]" as "DR".
      { iFrame. }

      iMod ("CLOS" with "[-POST CPS PH DR HNI_FL]") as "_".
      { iFrame. iExists _. iNext. iSplitR.
        { by iLeft. }        
        iFrame "%". iFrame "OLDS". 
        iSplit; cycle 1.
        - rewrite /rop_interp.
          iIntros (i' [=]). subst n.
          iDestruct "ROP" as "[SAFE | $]".
          2: { iFrame. }
          iFrame "READ_".
          
          destruct (decide (i' = i)). 
          { subst. rewrite {1}/safe_read. rewrite Nat.add_sub.
            iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
            - iFrame.
            - iDestruct "FROM_DANGLE" as "[(-> & -> & _) ->]".
              iFrame "RP". 
              iLeft. rewrite /safe_read. rewrite Nat.add_sub.
              do 2 iRight. by iFrame. 
            - iDestruct "FROM_BR" as "([-> ->] & ->)". 
              rewrite READ in READ'. inversion READ'. subst r x1 x2.
              apply Nat.le_lteq in BR0 as [BR0 | ->].
              { iSpecialize ("NO_FL" with "[//]"). iExFalso.
                iAssert (∃ rp', ith_rp i rp' ∗ ⌜ rp' = rs_canceled \/ rp' = rs_completed⌝)%I as "(%rp' & RP' & %RP')".
                { iDestruct "NO_FL" as "[$|$]"; set_solver. }
                iApply (ith_rp_mut_excl with "RP' RP").
                destruct RP' as [-> | ->]; done. }
              rename x into bi.
              red in RH_WF.
              destruct RH_WF as (n' & DOM & [? | [=]] & SEQ & BB'); [done| ].
              subst n'.
              pose proof READ as EQ%BB'. simpl in EQ.
              assert (bi = h + 1) as -> by lia.  clear BB EQ.
              assert (b1 = fl) as -> by lia.
              rewrite BRTH in BRTH1. inversion BRTH1. subst pbr ndbr1.
              iDestruct ("PFL_NEQ_D" with "[] []") as "?".
              { eauto. }
              { eauto. }
              done. }
          
          assert (i < i') as NEW.
          { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
            subst i'.
            apply mk_is_Some, elem_of_dom in READ. rewrite DOM elem_of_set_seq in READ.
            lia. }
          clear n.

          assert (h + 1 <= r_) as READ'_BOUND.
          { red in RH_WF. destruct RH_WF as (n' & DOM & [? | [=]] & RH_WF); [done| ].
            apply proj1 in RH_WF. eapply RH_WF in NEW; eauto. simpl in NEW. lia. }
          rewrite {1}/safe_read.
          iDestruct "SAFE" as "[FROM_HEAD | [FROM_DANGLE | FROM_BR]]".
          + iFrame.
          + iDestruct "FROM_DANGLE" as "[(-> & -> & _) ?]". lia.
          + iFrame.
            iDestruct "FROM_BR" as "([% %] & ?)". subst.
            red in ORDER. lia.
        - rewrite /hq_state_wf. iPureIntro.
          red in ORDER. lia. }

      iModIntro. wp_bind (Rec _ _ _)%E. pure_steps.
      (* TODO: fix a mistake in fl read spec *)
      admit.
    - 
      iAssert (dequeue_resources (h + 1) h ndh.2 None)%I with "[CH CFL HEAD' DFRAG]" as "DR".
      { iFrame. }

      iMod ("CLOS" with "[-POST CPS PH DR HNI_FL]") as "_".
      { iFrame. iExists _. iNext. iSplitR.
        { by iLeft. }
        iFrame "% OLDS".
        iSplit; cycle 1.
        - rewrite /rop_interp. by iIntros (??). 
        - rewrite /hq_state_wf. iPureIntro.
          red in ORDER. lia. }

      iModIntro. wp_bind (Rec _ _ _)%E. pure_steps.
      (* TODO: fix a mistake in fl read spec *)
      admit.
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
