From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From iris.base_logic.lib Require Import saved_prop. 
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From trillium.fairness.lawyer.examples.ticketlock Require Import obls_atomic fair_lock.


Section Ticketlock.
  Context `{ODd: OfeDiscrete DegO} `{ODl: OfeDiscrete LevelO}.
  Context `{LEl: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.

  Definition Tid := locale heap_lang.

  Local Infix "*'" := prod (at level 10, left associativity).

  Definition tau_codom Σ: Type :=
    Tid *' Phase *' Qp *'
    (gset SignalId) *' (gset Level) *'
    (* (ofe_mor val (iProp Σ)) *' (ofe_mor (option nat) (iProp Σ)). *)
    (val -> (iProp Σ)) *' ((option nat) -> (iProp Σ)).

  Definition tau_codom_gn: Type := 
    Tid *' Phase *' Qp *'
    (gset SignalId) *' (gset Level) *'
    gname *' gname.
                                       
  Local Infix "**" := prodO (at level 10, left associativity).

  (* Definition tau_codomO Σ: ofe := prodO (prodO (prodO (prodO Tid Phase) (gsetO SignalId)) (gsetR Level)) *)
  (*                                   (* ((iPropO Σ)) *) *)
  (*                                       (ofe_morO valO (iPropO Σ)) *)
  (* . *)
  (* Definition tau_codomO Σ: ofe := *)
  (*   Tid ** Phase ** Qp ** (gsetO SignalId) ** (gsetR Level) ** *)
  (*   (ofe_morO valO (iPropO Σ)) ** (ofe_morO (optionR natO) (iPropO Σ)). *)
 
  Class TicketlockPreG Σ := {
      tl_tau_map_pre :> inG Σ (authUR (gmapUR nat (exclR $ tau_codom_gn)));
      tl_tau_sp_post :> savedPredG Σ val;
      tl_tau_sp_rr :> savedPredG Σ (option nat);
      tl_tokens_pre :> inG Σ (authUR (gset_disjUR natO));
      tl_held_pre :> inG Σ (excl_authUR boolO);
      tl_ow_lb_pre :> inG Σ mono_natUR;
      tl_rel_tok_pre :> inG Σ (exclR unitO);
  }.

  Class TicketlockG Σ := {
      tl_pre :> TicketlockPreG Σ;
      tl_γ_tau_map: gname; tl_γ_tokens: gname; tl_γ_held: gname;
      tl_γ_ow_lb: gname; tl_γ_rel_tok: gname;
  }.

  Definition ticket_tau `{TicketlockG Σ} (n: nat) (cd: tau_codom Σ): iProp Σ :=
    ∃ (γ__p γ__r: gname),
      let cd_gn: tau_codom_gn := (cd.1.1, γ__p, γ__r) in
      own tl_γ_tau_map ((◯ {[ n := Excl cd_gn ]}): authUR (gmapUR nat _)) ∗
      saved_pred_own γ__p DfracDiscarded cd.1.2 ∗ saved_pred_own γ__r DfracDiscarded cd.2.

  Definition tokens_auth `{TicketlockG Σ} (N: nat) :=
    own tl_γ_tokens ((● (GSet $ set_seq 0 N)): authUR (gset_disjUR natO)).
  Definition ticket_token `{TicketlockG Σ} (i: nat) :=
    own tl_γ_tokens ((◯ (GSet {[ i ]})): authUR (gset_disjUR natO)).

  Definition held_auth `{TicketlockG Σ} (b: bool) :=
    own tl_γ_held ((● Excl' b): (excl_authUR boolO)).
  Definition held_frag `{TicketlockG Σ} (b: bool) :=
    own tl_γ_held ((◯ Excl' b): (excl_authUR boolO)).

  Definition ow_exact `{TicketlockG Σ} (n: nat) :=
    own tl_γ_ow_lb ((●MN n): mono_natUR).
  Definition ow_lb `{TicketlockG Σ} (n: nat) :=
    own tl_γ_ow_lb (mono_nat_lb n).

  Definition rel_tok `{TicketlockG Σ} := own tl_γ_rel_tok (Excl ()).

  Lemma ticket_token_excl `{TicketlockG Σ} i:
    ticket_token i -∗ ticket_token i -∗ False.
  Proof using.
    clear ODl ODd LEl.
    iApply bi.wand_curry. rewrite -own_op -auth_frag_op.
    iIntros "X". iDestruct (own_valid with "X") as %V.
    rewrite auth_frag_valid in V. apply gset_disj_valid_op in V. set_solver.
  Qed.

  Lemma ticket_token_bound `{TicketlockG Σ} i N:
    ticket_token i -∗ tokens_auth N -∗ ⌜ i < N ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite bi.sep_comm -own_op.
    iIntros "X". iDestruct (own_valid with "X") as %V.
    apply auth_both_valid_discrete in V as [IN V].
    apply gset_disj_included, elem_of_subseteq_singleton in IN.
    apply elem_of_set_seq in IN. iPureIntro. lia.
  Qed.

  Lemma held_agree `{TicketlockG Σ} b1 b2:
    held_auth b1-∗ held_frag b2 -∗ ⌜ b1 = b2 ⌝.
  Proof using.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. apply excl_auth_agree_L in Hval. set_solver.
  Qed.

  Lemma held_update `{TicketlockG Σ} b1 b2 b':
    held_auth b1 -∗ held_frag b2 ==∗
    held_auth b' ∗ held_frag b'.
  Proof using.
    iIntros "HA HB". iCombine "HB HA" as "H".
    rewrite -!own_op. iApply own_update; [| by iFrame].
    apply excl_auth_update.
  Qed.

  Ltac destruct_cd cd :=
    destruct cd as [[[[[[?τ ?π] ?q] ?Ob] ?L] ?Post] ?RR].

  Lemma ow_exact_lb `{TicketlockG Σ} n:
    ow_exact n -∗ ow_exact n ∗ ow_lb n.
  Proof using.
    iIntros "EX".
    rewrite /ow_exact. rewrite mono_nat_auth_lb_op.
    rewrite /ow_lb -own_op.
    erewrite (mono_nat_lb_op_le_l n) at 1; [| reflexivity].
    by rewrite cmra_assoc.
  Qed.

  Lemma ow_exact_increase `{TicketlockG Σ} n m
    (LE: n <= m):
    ow_exact n ==∗ ow_exact m ∗ ow_lb m.
  Proof using.
    iIntros "EX".
    rewrite /ow_exact.
    rewrite /ow_lb -!own_op.
    iApply (own_update with "[$]").
    etrans.
    { apply mono_nat_update, LE. }
    by rewrite {1}mono_nat_auth_lb_op.
  Qed.

  Lemma ow_lb_le_exact `{TicketlockG Σ} i n:
    ow_lb i -∗ ow_exact n -∗ ⌜ i <= n ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite bi.sep_comm -own_op. iIntros "X".
    iDestruct (own_valid with "X") as %V%mono_nat_both_valid. done.
  Qed.

  Definition tl_LK `{TicketlockG Σ} `{gen_heapGS loc val Σ}
    (st: FL_st): iProp Σ :=
    let '(lk, r, b) := st in
    ∃ (l__ow l__tk: loc),
      ⌜ lk = (#l__ow, #l__tk)%V ⌝ ∗ l__ow ↦{/ 2} #r ∗
      held_frag b.

  (* Right now we just assume that the resulting OM has all needed degrees and levels *)
  Context (d__w d__l0 d__h0 d__e d__m0: Degree).
  Hypothesis
    (fl_degs_wl0: deg_lt d__w d__l0)
    (fl_degs_lh0: deg_lt d__l0 d__h0)
    (fl_degs_he: deg_lt d__h0 d__e)
    (fl_degs_em: deg_lt d__e d__m0)
  .

  Definition tl_exc := 20.

  (* we need to have a non-empty set of "acquire levels" to verify the client. *)
  (* seemingly it's possible to get rid of this restriction by having an extra
     "lower bound" of levels in the definition of TLAT. *)
  (* TODO: clarify if it's possible *)
  Context (lvl_acq: Level).

  Definition lvls_acq: gset Level := {[ lvl_acq ]}. 
  
  Program Definition TLPre: FairLockPre := {|    
    fl_c__cr := 2 + tl_exc;
    fl_B := fun c => 2 * c + 3 + tl_exc;
    fl_GpreS := TicketlockPreG;
    fl_GS := TicketlockG;
    fl_LK := fun Σ FLG HEAP => tl_LK;
    fl_degs_lh := fl_degs_lh0;
    fl_d__m := d__m0;
    fl_acq_lvls := lvls_acq;
  |}.
  Next Obligation.
    etrans; eauto.
  Defined.

  Let OAM := ObligationsAM.
  Let ASEM := ObligationsASEM.

  Context {Σ: gFunctors}.
  (* Context {invs_inΣ: invGS_gen HasNoLc Σ}. *)
  Context {oGS: @asem_GS _ _ ASEM Σ}.
  Context `{EM: ExecutionModel heap_lang M}.
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).
           
  Let tl_TAU := TAU_FL (FLP := TLPre) (oGS := oGS).

  Definition TAU_stored `{TLG: TicketlockG Σ} (lk: val) (c: nat) (cd: tau_codom Σ): iProp Σ :=
    let '(τ, π, q, Ob, L, Φ, RR) := cd in
    obls τ Ob (oGS := oGS) ∗ sgns_levels_gt' Ob L (oGS := oGS) ∗
    th_phase_frag τ π (q /2) (oGS := oGS) ∗
    tl_TAU τ (acquire_at_pre lk (FLP := TLPre) (FLG := TLG)) (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        L
        (fun '(_, _, b) => b = false)
        c π
        (* (fun _ _ => bi_wand (th_phase_eq τ π (oGS := oGS): iProp Σ) (Φ #())) *)
        q
        (fun _ _ => Φ #())
        Ob RR.

  (* Instance TAU_stored_Proper `{TLG: TicketlockG Σ}: *)
  (*   Proper (eq ==> eq ==> equiv ==> equiv) TAU_stored. *)
  (* Proof using. *)
  (*   intros ?????????. subst. rewrite /TAU_stored. *)
  (*   destruct x1 as [[[[[[]]]]]], y1 as [[[[[[]]]]]]. *)
  (*   rename H1 into X. *)
  (*   repeat (inversion X as [X1 ?Y]; clear X; rename X1 into X). simpl in *. subst. *)
  (*   apply leibniz_equiv_iff in Y1, Y2, X, Y3, Y4. subst. *)
  (*   rewrite {1 2}X. rewrite Y3.  *)
  (*   rewrite /tl_TAU /TAU_FL. simpl. *)
  (*   do 3 (iApply bi.sep_proper; [by eauto| ]). *)
  (*   iApply TAU_Proper; solve_proper. *)
  (* Qed. *)

  Definition tau_interp `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) (i: nat) (cd: tau_codom Σ): iProp Σ :=
      let '((((((τ, π), q), _), _), Φ), _) := cd in
      (TAU_stored lk c cd ∗ ⌜ ow < i ⌝ ∨
       (((th_phase_frag τ π (q /2) (oGS := oGS) -∗ Φ #()) ∗ rel_tok ∨ ticket_token i) ∗ ⌜ ow = i ⌝) ∨
       ticket_token i ∗ ⌜ i < ow ⌝).

  Arguments tau_interp _ _ _ _ _ cd: simpl nomatch. 

  (* Lemma tau_interp_Proper_impl' `{TicketlockG Σ} lk c ow i x y: *)
  (*   (x ≡ y) -∗ tau_interp lk c ow i x -∗ tau_interp lk c ow i y. *)
  (* Proof using. *)
  (*   clear fl_degs_wl0 d__w ODl ODd LEl.  *)
  (*   iIntros "#EQUIV". rewrite /tau_interp. *)
  (*   rewrite /TAU_stored. *)
  (*   destruct x as [[[[[[]]]]]], y as [[[[[[]]]]]]. simpl. *)
  (*   repeat rewrite prod_equivI. simpl. iDestruct "EQUIV" as "[[[[[[%U %W] %V] %Y]%Z] #A] #B]". *)
  (*   apply leibniz_equiv_iff in Y, Z. apply (proj1 (leibniz_equiv_iff _ _)) in U, W, V. subst. *)
  (*   rewrite !ofe_morO_equivI. *)
  (*   iIntros "T". iDestruct "T" as "[T | [T | T]]"; try by (iRight; iFrame). *)
  (*   2: { iRight. iLeft. iDestruct "T" as "[T ->]". iSplit; [| done]. *)
  (*        iDestruct "T" as "[T | ?]"; [| by iFrame]. *)
  (*        iSpecialize ("A" $! #()). *)
  (*        iLeft. by iRewrite -"A". } *)
  (*   iLeft. *)
  (*   iDestruct "T" as "[[? (?&?&T)] ?]". iFrame. *)
  (*   rewrite /tl_TAU /TAU_FL. *)
  (*   iApply (TAU_proper' with "[] [] [$]"). *)
  (*   all: iIntros; iApply internal_eq_sym; set_solver. *)
  (* Qed. *)
    
  Definition tau_map_interp `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) (TM: gmap nat tau_codom_gn): iProp Σ :=
    own tl_γ_tau_map ((● (Excl <$> TM)): authUR (gmapUR nat (exclR $ tau_codom_gn))) ∗
    [∗ map] i ↦ cd_gn ∈ TM,
      ∃ (Φ: val -> iProp Σ) (RR: option nat -> iProp Σ), saved_pred_own cd_gn.1.2 DfracDiscarded Φ ∗ saved_pred_own cd_gn.2 DfracDiscarded RR ∗
      let cd: tau_codom Σ := (cd_gn.1.1, Φ, RR) in
      tau_interp lk c ow i cd.
  
  Definition tl_inv_inner `{TicketlockG Σ} (tl: val) (c: nat): iProp Σ :=
    ∃ (l__ow l__tk: loc) (ow tk: nat) TM,
      ⌜ tl = (#l__ow, #l__tk)%V ⌝ ∗ ⌜ ow <= tk ⌝ ∗ exc_lb (tk - ow + 2) (oGS := oGS) ∗
      l__ow ↦{/ 2} #ow ∗ l__tk ↦ #tk ∗ ow_exact ow ∗ held_auth (negb (ow =? tk)) ∗
      tokens_auth tk ∗
      ⌜ dom TM = set_seq 0 tk ⌝ ∗ (* tau_map_auth TM ∗ *) tau_map_interp tl c ow TM ∗
      (⌜ ow = tk ⌝ → rel_tok).

  Lemma ticket_tau_alloc `{TicketlockG Σ} lk c ow TM n cd
    (FRESH: n ∉ dom TM):    
    tau_map_interp lk c ow TM -∗
    tau_interp lk c ow n cd
    ==∗ ∃ cd_gn, tau_map_interp lk c ow (<[ n := cd_gn ]> TM) ∗ ticket_tau n cd.
  Proof using.
    clear ODl ODd LEl fl_degs_wl0 d__w.
    iIntros "TMA TI". destruct_cd cd. 
    iMod (saved_pred_alloc Post DfracDiscarded) as (γ__p) "#POST"; [done| ].
    iMod (saved_pred_alloc RR DfracDiscarded) as (γ__r) "#RR"; [done| ].

    rewrite /tau_map_interp. iDestruct "TMA" as "[TMA PREDS]".
    iExists (τ, π, q, Ob, L, γ__p, γ__r).
    rewrite big_opM_insert. iFrame "PREDS". 
    2: { by apply not_elem_of_dom. }
    rewrite bi.sep_comm bi.sep_assoc. 
    iApply bupd_frame_r. iSplitL "TMA".
    2: { do 2 iExists _. iFrame "#∗". }
    rewrite /ticket_tau. do 2 (setoid_rewrite bi.sep_exist_r).
    do 2 iExists _. simpl. iFrame "#∗".  
    rewrite bi.sep_comm.
    rewrite -own_op. iApply own_update; [| by iFrame].
    apply auth_update_alloc.
    rewrite fmap_insert. apply alloc_singleton_local_update.
    2: done.
    apply not_elem_of_dom. set_solver.
  Qed.

  Lemma tau_map_ticket `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) TM i cd:
    tau_map_interp lk c ow TM -∗ ticket_tau i cd -∗
    ∃ cd_gn, ⌜ TM !! i = Some cd_gn ⌝ ∗ ⌜ cd_gn.1.1 = cd.1.1 ⌝ ∗
             saved_pred_own cd_gn.1.2 DfracDiscarded cd.1.2 ∗ saved_pred_own cd_gn.2 DfracDiscarded cd.2.
  Proof using.
    iIntros "TM TK". rewrite /tau_map_interp /ticket_tau.
    iDestruct "TM" as "[TMA SP]". iDestruct "TK" as (??) "(TK & SP1 & SP2)".
    destruct_cd cd. simpl.
    iExists (_, _, _, _, _, _, _).
    iFrame. simpl. iSplit; [| done].
    iCombine "TMA TK" as "TK". 
    iDestruct (own_valid with "TK") as %V%auth_both_valid_discrete.
    iPureIntro. destruct V as [IN V]. 
    apply singleton_included_exclusive_l in IN.
    2, 3: apply _ || done.
    apply leibniz_equiv_iff in IN.
    apply lookup_fmap_Some in IN as (?&IN&?).
    inversion IN. by subst.
  Qed.

  Lemma tau_map_ticket_interp `{TicketlockG Σ} TM i cd lk c ow:
    ticket_tau i cd -∗ tau_map_interp lk c ow TM -∗
    ∃ Φ' RR',
      let cd' := (cd.1.1, Φ', RR') in
      tau_interp lk c ow i cd' ∗ ticket_tau i cd ∗
      (tau_interp lk c ow i cd' -∗ tau_map_interp lk c ow TM) ∗
      (∀ v, ▷ (cd.1.2 v ≡ Φ' v)) ∗ (∀ r, ▷ (cd.2 r ≡ RR' r)). 
  Proof using.
    clear fl_degs_wl0 d__w ODl ODd LEl.
    iIntros "T TMI".
    rewrite /tau_map_interp. iDestruct "TMI" as "[AUTH TMI]". 
    iDestruct (tau_map_ticket with "[$] [$]") as (? ITH EQ) "(#SP1 & #SP2)".
    destruct_cd cd. 
    destruct cd_gn as [[]]. simpl in EQ. subst p.
    
    remember (τ, π, q, Ob, L, Post, RR) as cd. simpl.
    rewrite {2}(map_split TM i).
    rewrite big_opM_union.
    2: { apply map_disjoint_dom. destruct lookup; set_solver. }
    iDestruct "TMI" as "[TKI CLOS]".
    rewrite ITH. simpl. rewrite big_sepM_singleton.
    
    (* iDestruct (tau_interp_Proper_impl' with "TK TKI") as "TKI". iFrame. *)
    iFrame "T AUTH".
    iDestruct "TKI" as (Φ' RR') "(#SP1' & #SP2' & TI')". simpl.    
    do 2 iExists _. iSplitL "TI'".
    { subst cd. simpl. iFrame. }
    iSplitL.
    2: { iSplit; iIntros.
         - iDestruct (saved_pred_agree with "SP1 SP1'") as "foo".
           iApply "foo".
         - iDestruct (saved_pred_agree with "SP2 SP2'") as "foo".
           iApply "foo". }
    iIntros "TKI".
    iDestruct (big_sepM_insert_delete with "[CLOS TKI]") as "TMI".
    2: { rewrite insert_id; [| done]. iFrame. }
    simpl. 
    iFrame.  do 2 iExists _. iFrame "#∗".
    subst cd. iFrame. 
  Qed.

  (* Lemma TMI_extend_queue `{TicketlockG Σ} lk c ow TM tk cd *)
  (*   (DOM: dom TM = set_seq 0 tk) *)
  (*   (QUEUE: ow < tk): *)
  (*   tau_map_interp lk c ow TM -∗ TAU_stored lk c cd -∗ *)
  (*   tau_map_interp lk c ow (<[ tk := cd ]> TM). *)
  (* Proof using. *)
  (*   iIntros "TMI TAU". *)
  (*   rewrite /tau_map_interp. rewrite big_opM_insert. *)
  (*   2: { apply not_elem_of_dom. rewrite DOM. intros ?%elem_of_set_seq. lia. } *)
  (*   iFrame. rewrite /tau_interp. *)
  (*   destruct cd as [[[[[[]]]]]]. iLeft. by iFrame. *)
  (* Qed. *)

  Lemma TMI_extend_acquire `{TicketlockG Σ} lk c ow TM (cd: tau_codom Σ)
    (DOM: dom TM = set_seq 0 ow):
    let '((((((τ, π), q), _), _), Φ), _) := cd in   
    tau_map_interp lk c ow TM -∗ rel_tok -∗
    (th_phase_frag τ π (q /2) (oGS := oGS) -∗ cd.1.2 #()) ==∗
    ∃ cd_gn, tau_map_interp lk c ow (<[ ow := cd_gn ]> TM) ∗ ticket_tau ow cd.
  Proof using.
    destruct_cd cd. simpl. 
    iIntros "TMI RTOK TAU".    
    iMod (ticket_tau_alloc with "[$] [RTOK TAU]") as "FOO".
    3: { by iFrame. }
    { rewrite DOM elem_of_set_seq. lia. }
    rewrite /tau_interp. iRight. iLeft. iSplit; [| done].
    iLeft. iFrame. 
  Qed.

  Lemma tokens_alloc `{TicketlockG Σ} (N: nat):
    tokens_auth N ==∗ tokens_auth (S N) ∗ ticket_token N.
  Proof using.
    iIntros. rewrite /tokens_auth /ticket_token.
    rewrite -own_op. iApply own_update; [| by iFrame].
    apply auth_update_alloc.
    rewrite set_seq_S_end_union_L. simpl.
    etrans.
    1: eapply gset_disj_alloc_empty_local_update.
    2: { reflexivity. }
    apply disjoint_singleton_l. by (intros ?%elem_of_set_seq; lia).
  Qed.

  Definition get_ticket: val :=
    λ: "lk", FAA (Snd "lk") #1.

  Definition wait: val :=
    rec: "wait" "lk" "t" :=
      let: "o" := !(Fst "lk") in
      if: "t" = "o"
      then #()
      else "wait" "lk" "t"
  .

  Definition tl_acquire : val :=
    λ: "lk",
      let: "t" := get_ticket "lk" in
      wait "lk" "t"
  .

  Definition tl_release: val :=
      λ: "lk", FAA (Fst "lk") #1
  .

  Definition tl_is_lock `{TicketlockG Σ} lk c := inv fl_ι (tl_inv_inner lk c).

  Definition tl_newlock: val :=
    λ: <>,
       let: "ow" := ref #(0%nat) in
       let: "tk" := ref #(0%nat) in
       ("ow", "tk").

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS _ EM hGS (↑ nroot)}.

  Lemma tl_newlock_spec `{TicketlockPreG Σ} τ π c
    (BOUND: fl_c__cr TLPre <= LIM_STEPS):
      {{{ cp π d__m0 (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) }}}
        tl_newlock #() @ τ
      {{{ lk, RET lk; ∃ TLG: TicketlockG Σ, tl_LK (lk, 0, false) ∗ tl_is_lock lk c ∗ th_phase_eq τ π (oGS := oGS) }}}.
  Proof using OBLS_AMU.
    clear fl_degs_wl0 d__w ODl ODd LEl.
    iIntros (Φ) "(CP & PH) POST". rewrite /tl_newlock.
    pure_step_hl. MU_by_BMU.
    simpl. do 2 rewrite -Nat.add_1_r. rewrite -Nat.add_assoc. iApply BMU_split.
    iApply OU_BMU_rep.
    iApply (OU_rep_wand with "[-PH]").
    2: { iApply (increase_eb_upd_rep0 with "[$]"). }
    iIntros "[#EB PH]".
    
    iApply OU_BMU. iApply (OU_wand with "[-CP PH]").
    2: { (* TODO: can we remove phase restriction for exchange? *)
         iApply (exchange_cp_upd with "[$] [$] [$]").
         { reflexivity. }
         apply fl_degs_em. }
    iIntros "[CPS PH]". BMU_burn_cp.

    wp_bind (ref _)%E. iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iIntros "!> %l__ow OW _". MU_by_burn_cp.
    pure_steps. wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (ref _)%E. iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iIntros "!> %l__tk TK _". MU_by_burn_cp. pure_steps.
    
    iMod (own_alloc (● ∅ ⋅ ◯ _: authUR (gmapUR nat (exclR $ tau_codom_gn)))) as (γ__tm) "[TM_AUTH TM_FRAG]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    iMod (@own_alloc _ _ _ (● (GSet ∅) ⋅ _: authUR (gset_disjUR natO))) as (γ__toks) "[TOKS_AUTH TOKS_FRAG]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    iMod (own_alloc (● Excl' false ⋅ ◯ _: (excl_authUR boolO))) as (γ__h) "[HELD_AUTH HELD_FRAG]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    iMod (own_alloc (●MN 0: mono_natUR)) as (γ__lb) "LB_AUTH".
    { apply mono_nat_auth_valid. }
    iMod (own_alloc (Excl ())) as (γ__rt) "RT".
    { done. }
    rewrite -{1}Qp.inv_half_half. iDestruct "OW" as "[OW OW']".

    eset (TLG := Build_TicketlockG _ _ γ__tm γ__toks γ__h γ__lb γ__rt).
    iApply fupd_wp.
    iMod (inv_alloc fl_ι _ (tl_inv_inner _ c) with "[-POST OW' HELD_FRAG CPS PH]") as "#INV".
    { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame.
      do 2 (iSplit; [done| ]). iSplit.
      { simpl. iApply exc_lb_le; [| done]. unfold tl_exc. lia. }
      rewrite Nat.eqb_refl. iFrame.
      iSplit.
      { iPureIntro. apply dom_empty_L. }
      iSplit; [| done].
      rewrite /tau_map_interp. rewrite fmap_empty. iFrame. set_solver. }

    iModIntro. pure_steps.
    wp_bind (Rec _ _ _)%V. pure_steps.
    iApply "POST". iExists _. iFrame "#∗".
    do 2 iExists _. iFrame. done.
  Qed.

  (* Set Ltac Profiling. *)

  Section AfterInit.
        
  Context {TLG: TicketlockG Σ}.
    
  (* TODO: find existing *)
  Lemma fupd_frame_all E1 E2 P:
    ((|==> P) ∗ |={E1, E2}=> emp: iProp Σ) ⊢ |={E1, E2}=> P.
  Proof using.
    iIntros "[P ?]". iMod "P". by iFrame.
  Qed.

  Definition wait_res o' t τ π q Ob Φ RR: iProp Σ :=
    ⌜ o' <= t ⌝ ∗
    ow_lb o' ∗ cp_mul π d__h0 (t - o') (oGS := oGS) ∗
    (∃ r__p, RR r__p ∗ (⌜ r__p = Some o' ⌝ ∨ cp π d__h0 (oGS := oGS))) ∗
    cp_mul π d__w 10 (oGS := oGS) ∗
    let cd: tau_codom Σ := (τ, π, q, Ob, lvls_acq, Φ, RR) in
    ticket_token t ∗ ticket_tau t cd
    ∗ th_phase_frag τ π (q / 2) (oGS := oGS)
  .

  (* TODO: move, remove duplicates *)
  Ltac remember_goal :=
  match goal with | |- envs_entails _ ?P =>
    iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ]
  end.

  (* TODO: why it works only in specific cases? *)
  Opaque cp_mul. 

  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma get_ticket_spec s (lk: val) c (τ: locale heap_lang) π q
    (* (Φ: ofe_mor val (iProp Σ)) *)
    Φ
    (Ob: gset SignalId)
    (* (RR: ofe_mor (option nat) (iProp Σ)) *)
    RR
    (LIM_STEPS': fl_B TLPre c <= LIM_STEPS):
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ⊢
        TAU_FL τ
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        {[lvl_acq]}
        (fun '(_, _, b) => b = false)
        c π q (fun _ _ => Φ #())
        Ob RR
        (oGS := oGS) (FLP := TLPre)
        -∗
        TLAT_pre τ {[lvl_acq]} d__e RR π q Ob (oGS := oGS) -∗
        cp_mul π d__w 10 (oGS := oGS) -∗
        WP (get_ticket lk) @ s; τ; ⊤ {{ tv, ∃ (t o': nat), ⌜ tv = #t ⌝ ∗ wait_res o' t τ π q Ob Φ RR }}.
  Proof using OBLS_AMU fl_degs_wl0.
    clear ODl ODd LEl.
    iIntros "[#INV #EB]". rewrite /TLAT_FL /TLAT.
    iIntros "TAU PRE CPS".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & #SGT & PH & CPe)".
    rewrite /get_ticket.

    pure_steps.

    (* TODO: ??? worked fine when get_ticket was inlined into tl_acquire *)
    (* wp_bind (Snd _)%E. *)
    assert (FAA (Snd lk) #1 = fill_item (FaaLCtx #(LitInt 1)) (Snd lk)) as CTX by done.
    iApply (wp_bind [(FaaLCtx #1)] s ⊤ τ (Snd lk) (Λ := heap_lang)). simpl.
    
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & #EBd & >OW & >TK & >EXACT & >HELD & >TOKS & >%DOM__TM & TAUS & RTOK)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    rewrite /TAU_FL. rewrite TAU_elim. iMod "TAU" as (st) "[[ST %ST__lk] TAU]".
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_faa with "TK").
    iIntros "!> TK'". iNext. MU_by_BMU.
    simpl.
    iApply BMU_lower; [apply PeanoNat.Nat.le_add_r| ].
    rewrite (Nat.add_comm _ 3). iApply OU_BMU.
    (* iDestruct (cp_mul_take with "CPSw") as "[CPSw CPw]". *)
    apply Nat.le_sum in LEot as [d ->].
    iApply (OU_wand with "[-CPe PH]").
    2: { iApply (exchange_cp_upd with "[$] [$]").
         { apply (Nat.le_refl (S (S d))). }
         { apply fl_degs_he. }
         rewrite Nat.sub_add'. by rewrite Nat.add_comm. }
    iIntros "[CPSh PH]".
    iDestruct (cp_mul_take with "CPSh") as "[CPSh CPh]".

    iApply OU_BMU. iApply (OU_wand with "[-CPh PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] EB").
         { Unshelve. 3: exact 10. lia. shelve. }
         etrans; [apply fl_degs_wl0 | apply fl_degs_lh0]. }
    iIntros "[CPS' PH]".

    iApply OU_BMU. iApply (OU_wand with "[-PH]").
    2: { iApply (increase_eb_upd with "EBd [$]"). }
    iClear "EBd". iIntros "[#EBd' PH]".
    
    iDestruct (ow_exact_lb with "[$]") as "[EXACT LB]".
    remember_goal.
    iMod (tokens_alloc with "[$]") as "[TOKS TOK]".
    (* iMod (ticket_tau_alloc with "[$]") as "[TM TK_TAU]". *)
    (* { rewrite DOM__TM. intros [_ IN]%elem_of_set_seq. simpl in IN. *)
    (*   by apply Nat.lt_irrefl in IN. } *)
    iApply "GOAL". iClear "GOAL".

    iDestruct (th_phase_frag_halve with "PH") as "[PH PH']".
    destruct (Nat.eq_0_gt_0_cases d) as [-> | QUEUE].
    2: { BMU_burn_cp.
         rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. simpl.
         iModIntro.
         pure_steps.
         do 2 iExists _.
         iFrame. rewrite Nat.sub_add'.
         rewrite {1}cp_mul_take. iDestruct "CPSh" as "[CPSh CPh]".
         iFrame.

         iDestruct "TAU" as "[_ [_ AB]]".
         iMod ("AB" with "[ST]") as "TAU"; [by iFrame| ].
         iMod (ticket_tau_alloc _ c ow TM (ow + d) with "[$] [TAU PH OB]") as (cd_gn) "[TMI TK]".
         { rewrite DOM__TM. intros ?%elem_of_set_seq. lia. }
         { Unshelve. 2: repeat eapply pair.
           simpl. iLeft. iFrame "OB PH SGT". iSplit; [| iPureIntro; lia]. 
           iApply "TAU". }

         iFrame "TK". 
         iApply fupd_frame_all.
         iSplitL "RR0".
         { iModIntro. iSplit; [done| ]. iSplit; [iPureIntro; lia| ].
           iExists _. iFrame. }

         iClear "RTOK".
         iMod ("CLOS" with "[HELD TK' OW EXACT TOKS TMI]") as "_"; [| done].
         iNext. rewrite /tl_inv_inner.
         do 5 iExists _. iFrame.
         (* Set Printing Coercions. *)
         (* Set Printing All. *)

         rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
         replace (((ow + d)%nat + 1)%Z) with (Z.of_nat $ S (ow + d)) by lia.
         iFrame. rewrite !bi.sep_assoc. iSplit.
         2: { iIntros "%". lia. }
         replace ((S (ow + d) - ow + 2)) with (S (d + 2)) by lia. iFrame "#∗".
         iPureIntro. split.
         { split; [done| lia]. }
         rewrite dom_insert_L DOM__TM.
         by rewrite set_seq_S_end_union_L. }

    rewrite (proj2 (Nat.eqb_eq _ _)); [| done]. simpl.
    iApply (BMU_lower _ (c + (0 + c))); [lia| ].
    iApply BMU_split.
    rewrite /tl_LK. destruct st as [[]]. iDestruct "ST" as (??) "(-> & OW' & HELD')".
    rewrite !Nat.add_0_r. rewrite Nat.add_0_r in DOM__TM.
    iDestruct "TAU" as "[_ [COMM _]]".
    iDestruct (held_agree with "[$] [$]") as "<-".
    rewrite /tl_LK.
    iSpecialize ("COMM" with "[OB PH']").
    { iFrame. iSplit; [done| ]. iPureIntro. by apply Qp.div_le. }

    iApply (BMU_wand with "[-COMM]"); [| done].
    iIntros "COMM".
    BMU_burn_cp. iModIntro. iApply wp_value.
    (* do 2 iExists _. iFrame. iApply fupd_frame_all. *)

    iMod (held_update _ _ true with "[$] [$]") as "[HELD HELD']".
    iMod ("COMM" $! (_, _, _) with "[HELD' OW']") as "Φ".
    { rewrite /acquire_at_post. simpl. rewrite /tl_LK.
      iFrame. iSplit; [| done]. do 2 iExists _. iFrame. done. }
    rewrite -{2}(Qp.div_2 q). rewrite Qp.add_sub. simpl.

    iSpecialize ("RTOK" with "[//]"). 
    iMod (TMI_extend_acquire _ _ _ _ (((((((_), _), _), _), _), _), _) with "[$] [$] [$]") as (?) "[TMI TK]"; eauto.

    do 2 iExists _. iFrame. iApply fupd_frame_all.
    iSplitL "CPSh RR0".
    { rewrite Nat.sub_diag. iModIntro.
      iSplit; [done| ]. iSplit; [done| ]. iApply bi.sep_exist_l.
      iExists _. iFrame. rewrite bi.sep_or_l. iRight.
      by rewrite -cp_mul_take. }
    
    iApply "CLOS". iNext. rewrite /tl_inv_inner.
    rewrite -(Nat.add_1_r ow).
    replace (Z.of_nat ow + 1)%Z with (Z.of_nat (ow + 1)) by lia.
    do 5 iExists _. iFrame.
    rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. iFrame.
    iFrame. rewrite !bi.sep_assoc. iSplit.
    2: { iIntros "%". lia. }
    rewrite Nat.sub_diag Nat.sub_add'. iFrame "#∗".
    iPureIntro. split.
    { split; [done| lia]. }
    rewrite dom_insert_L DOM__TM.
    rewrite set_seq_add_L. simpl.
    set_solver.
  Qed.

  (* TODO: move, derive from generalized Proper instance(s) *)
  Lemma sgns_levels_gt'_ge' R L:
    sgns_levels_gt' R L (oGS := oGS) -∗ sgns_levels_ge' R L (oGS := oGS).
  Proof using.
    iIntros "?". iApply (big_sepS_impl with "[$]").
    iIntros "!> % %IN (%l & #SGN & %GT)".
    iExists _. iFrame "SGN". iPureIntro.
    eapply set_Forall_impl; eauto. 
    rewrite /lvl_lt. intros ?. rewrite /flip. apply strict_include.
  Qed.

  Lemma wait_spec (lk: val) c o' (t: nat) τ π q Ob Φ RR
    (LIM_STEPS': fl_B TLPre c <= LIM_STEPS):
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ∗ wait_res o' t τ π q Ob Φ RR 
    ⊢ WP (wait lk #t) @ τ {{ v, Φ v ∗ rel_tok }}.
  Proof using fl_degs_wl0 OBLS_AMU.
    clear ODl ODd LEl.
    iLöb as "IH" forall (o').
    rewrite {2}/wait_res. iIntros "(#INV & #EXC & %LEo't & OW_LB & CPSh & RR & CPS & TOK & TAU & PH)".
    rewrite {2}/wait.
    pure_steps.

    wp_bind (Fst _)%E.
    (* TODO: make a lemma? and remove duplicates *)
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & #EBd & >OW & >Ltk & >EXACT & >HELD & >TOKS & >%DOM__TM & TAUS & RTOK)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_load with "[OW]"); [done| ]. iIntros "!> OW".
    
    iDestruct (ticket_token_bound with "[$] [$]") as %LTttk.
    destruct (decide (ow = t)) as [-> | QUEUE].
    { rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
      iDestruct (tau_map_ticket_interp with "[$] [$]") as (??) "(TAUtk & TK & TMI_CLOS & #EQ1 & #EQ2)".
      rewrite {1}/tau_interp. iDestruct "TAUtk" as "[[? %] | [[TAUtk _] | [? %]]]".
      1, 3: lia.
      simpl. iDestruct "TAUtk" as "[[Φ RTOK'] | TOK']".
      2: { by iDestruct (ticket_token_excl with "[$] [$]") as %?. }
      iSpecialize ("TMI_CLOS" with "[TOK]").
      { rewrite /tau_interp. iRight. iLeft. iSplit; [| done]. iFrame. }
      MU_by_burn_cp. iModIntro. pure_steps.
      iMod ("CLOS" with "[TMI_CLOS OW TOKS HELD EXACT Ltk]") as "_".
      { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame "#∗".
        rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
        rewrite !bi.sep_assoc. iSplitL; [by iFrame| ].
        iIntros "%". lia. }
      iModIntro.

      wp_bind (Rec _ _ _)%V. pure_steps.
      wp_bind (_ = _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step.
      { simpl. tauto. }
      iNext. MU_by_burn_cp. rewrite bool_decide_eq_true_2; [| tauto].
      pure_steps. iFrame.
      iRewrite ("EQ1" $! #()). by iApply "Φ". }

    iDestruct (tau_map_ticket_interp with "[$] [$]")  as (??) "(TAUtk & TK & TMI_CLOS & #EQ1 & #EQ2)".
    rewrite {1}/tau_interp.
    apply Nat.le_lteq in LEot as [LTot | EQ].
    2: { subst tk. iDestruct "TAUtk" as "[[? %] | [[? %] | [? %]]]".
         all: try lia.
         by iDestruct (ticket_token_excl with "[$] [$]") as %?. }

    iDestruct "TAUtk" as "[[TAUs %] | [[? %] | [? %]]]".
    all: try lia.
    2: { by iDestruct (ticket_token_excl with "[$] [$]") as %?. }
    rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
    rewrite /TAU_stored. iDestruct "TAUs" as "(OB & #SLT & PH' & TAUs)".
    rewrite /tl_TAU /TAU_FL. rewrite TAU_elim.
    rewrite /TAU_acc. iNext. MU_by_BMU.
    iApply BMU_invs. simpl.
    iMod "TAUs" as ([[lk_ r] b]) "[PRE [WAIT _]]".
    rewrite /acquire_at_pre. simpl. iDestruct "PRE" as "[>(%&%&%EQ&OW'&HELD') ->]".
    inversion EQ. subst l__ow0 l__tk0. clear EQ.
    iDestruct (held_agree with "[$] [$]") as %<-.
    iDestruct (mapsto_agree with "[$] [$]") as %EQ. inversion EQ as [EQ'].
    apply Nat2Z.inj' in EQ'. subst r. clear EQ.
    iDestruct (ow_lb_le_exact with "[$] [$]") as %LBow.
    replace (t - o') with (t - ow + (ow - o')) by lia.
    rewrite cp_mul_split. iDestruct "CPSh" as "[CPSh CPSh']".
    iSpecialize ("WAIT" with "[OB PH RR CPSh']").
    { iFrame. iSplitR.
      { by iApply sgns_levels_gt'_ge'. }
      iSplit.
      { iPureIntro. by apply Qp.div_le. }
      iSplit; [| done].
      iDestruct "RR" as (r) "[RR RR']". iExists _. iFrame.
      iRewrite ("EQ2" $! r) in "RR". iFrame "RR". 
      iDestruct "RR'" as "[-> | ?]"; [| by iFrame].
      apply Nat.le_sum in LBow as [d ->]. rewrite Nat.sub_add'.
      destruct d.
      - rewrite Nat.add_0_r. by iLeft.
      - rewrite cp_mul_take. iDestruct "CPSh'" as "[??]". iFrame. }
    iModIntro.
    iApply (BMU_lower _ (c + (3 + c))); [lia| ].
    iApply BMU_split. iApply (BMU_wand with "[-WAIT] [$]").
    iIntros "(RR & CP & PH & OB & CLOS')".
    iSpecialize ("CLOS'" with "[OW' HELD']").
    { iFrame. iSplit; [| done]. iNext. do 2 iExists _. iFrame. eauto. }
    iApply OU_BMU.
    iApply (OU_wand with "[-CP PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] EXC").
         { reflexivity. }
         apply fl_degs_wl0. }
    iIntros "[CPS' PH]".
    iDestruct (cp_mul_split with "[CPS CPS']") as "CPS"; [iFrame| ]. simpl.
    iApply BMU_intro. iMod "CLOS'" as "TAUs". iModIntro.
    (* rewrite cp_mul_take. iDestruct "CPS" as "[CPS CP]". *)
    split_cps "CPS" 1. rewrite -cp_mul_1.
    iSplitR "CPS'".
    2: { do 2 iExists _. iFrame. done. }
    iModIntro. pure_steps.
    iSpecialize ("TMI_CLOS" with "[TAUs SLT OB PH']").
    { rewrite /tau_interp. iLeft. iSplit; [| done].
      rewrite /TAU_stored. by iFrame. }
    iClear "OW_LB". iDestruct (ow_exact_lb with "[$]") as "[EXACT OW_LB]".
    iMod ("CLOS" with "[TMI_CLOS OW TOKS HELD EXACT Ltk]") as "_".
    { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame.
      rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. iFrame "#∗".
      rewrite !bi.sep_assoc. iSplit.
      { iPureIntro. repeat split; eauto. lia. }
      iIntros "->". lia. }
    iModIntro.
    wp_bind (Rec _ _ _)%V. pure_steps.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    iNext. MU_by_burn_cp. rewrite bool_decide_eq_false_2.
    2: { intros [=EQ%Nat2Z.inj']. lia. }
    do 2 pure_step_cases.

    iApply ("IH" $! ow).
    iFrame "#∗". iSplit; [iPureIntro; lia| ]. iSplitL "RR".
    { iExists _.
      iRewrite -("EQ2" $! (Some ow)) in "RR". iFrame "RR".          
      iFrame. by iLeft. }
    replace 21 with (10 + 11) by lia. rewrite cp_mul_split.
    iDestruct "CPS" as "[??]". iFrame.
  Qed.

  Lemma rel_tok_excl: rel_tok -∗ rel_tok -∗ ⌜ False ⌝.
  Proof using.
    iStartProof. rewrite bi.wand_curry -own_op.
    iIntros "X". by iDestruct (own_valid with "[$]") as %V.
  Qed.

  Lemma tau_map_interp_update (TM: gmap nat tau_codom_gn) (l__ow l__tk: loc) c (ow: nat)
    (lk := (#l__ow, #l__tk)%V)
    (next := bool_decide (ow + 1 ∈ dom TM)):
    tau_map_interp lk c ow TM -∗ held_auth false -∗
    l__ow ↦{/ 2} #(ow + 1)%nat -∗ rel_tok -∗
    BMU (⊤ ∖ ↑fl_ι) c (held_auth next ∗ l__ow ↦{/ 2} #(ow + 1)%nat ∗
                        (⌜ next = false ⌝ → rel_tok) ∗
                        tau_map_interp lk c (ow + 1) TM) (oGS := oGS).
  Proof using.
    clear fl_degs_wl0 d__w ODl ODd LEl OBLS_AMU.
    iIntros "TMI AUTH LOW RTOK". rewrite /tau_map_interp.

    rewrite {2 4}(map_split TM ow).
    rewrite !big_opM_union.
    2, 3: apply map_disjoint_dom; destruct lookup; set_solver.
    iDestruct "TMI" as "(TM & OW & TMI)".

    rewrite (map_split (delete _ _ ) (ow + 1)).
    rewrite !big_opM_union.
    2, 3: apply map_disjoint_dom; destruct lookup; set_solver.
    iDestruct "TMI" as "[OW' TMI]".
    rewrite !bi.sep_assoc. iApply (BMU_frame_r with "[TMI]").
    { iApply (big_sepM_impl with "[$]").
      iIntros "!>" (i cd ITH) "TI".
      apply lookup_delete_Some in ITH as [? [? ITH]%lookup_delete_Some].
      rewrite /tau_interp. destruct cd as [[[[[[]]]]]].
      iDestruct "TI" as (??) "(#SP1 & #SP2 & [[? %] | [[? %] | [? %]]])"; try lia.
      all: do 2 iExists _; iFrame "SP1 SP2". 
      - iLeft. iFrame. iPureIntro. lia.
      - do 2 iRight. iFrame. iPureIntro. lia. }
    rewrite -bi.sep_assoc bi.sep_comm -bi.sep_assoc.
    iPoseProof BMU_frame_l as "foo". rewrite bi.wand_curry. iApplyHyp "foo".

    iApply (bi.wand_frame_l with "[-RTOK OW]").
    2: { destruct (TM !! ow) as [cd| ] eqn:OW.
         2: { iSplitR "RTOK"; [| iAccu]. set_solver. }
         simpl. rewrite !big_sepM_singleton.
         rewrite /tau_interp. destruct cd as [[[[[[]]]]]].
         (* iDestruct "OW" as "[[? %] | [[OW %] | [? %]]]"; try lia. *)
         iDestruct "OW" as (??) "(#SP1 & #SP2 & [[? %] | [[OW %] | [? %]]])"; try lia.
         iDestruct "OW" as "[CD | TT]".
         { iDestruct "CD" as "[_ RT]".
           by iDestruct (rel_tok_excl with "[$] [$]") as "?". }
         iFrame. do 2 iExists _. iFrame "SP1 SP2".
         do 2 iRight. iFrame. iPureIntro. lia. }
    iIntros "RTOK".
    rewrite !lookup_delete_ne; [| lia].
    destruct (TM !! (ow + 1)) as [[[[[[[]]]]]]| ] eqn:OW'; simpl; subst next.
    2: { rewrite bool_decide_eq_false_2; [| by apply not_elem_of_dom].
         iApply BMU_intro. iFrame. set_solver. }
    simpl. rewrite bool_decide_eq_true_2; [| by apply elem_of_dom].
    rewrite !big_sepM_singleton.
    rewrite {1}/tau_interp.
    (* iDestruct "OW'" as "[[TAU %] | [[? %] | [? %]]]"; try lia. *)
    iDestruct "OW'" as (??) "(#SP1 & #SP2 & [[TAU %] | [[? %] | [? %]]])"; try lia.
    rewrite /TAU_stored.
    simpl. iDestruct "TAU" as "(OB' & #SLT' & PH' & TAUs')". simpl.
    rewrite /tl_TAU /TAU_FL. rewrite TAU_elim. simpl.
    rewrite /TAU_acc.
    
    iApply BMU_invs.
    iMod "TAUs'" as ([[lk_ r] b]) "[PRE [_ [COMM _]]]". iModIntro.

    rewrite /acquire_at_pre. simpl.
    remember_goal.
    iDestruct "PRE" as "[>(%&%&%EQ&LOW'&HELD') ->]".
    iApply "GOAL". iClear "GOAL".
    subst lk. inversion_clear EQ.
    iDestruct (held_agree with "[$] [$]") as %<-.
    iDestruct (mapsto_agree with "LOW LOW'") as %EQ.
    inversion EQ as [EQ'']. assert (r = ow + 1) as -> by lia. clear EQ'' EQ.
    iSpecialize ("COMM" with "[$OB' $PH']").
    { iPureIntro. split; [done| ]. by apply Qp.div_le. }
    iApply (BMU_wand with "[-COMM] [$]"). iIntros "CLOS'".
    iMod (held_update _ _ true with "[$] [$]") as "[HELD HELD']".
    iFrame "HELD LOW TM".
    iMod ("CLOS'" $! (_, ow + 1, true) with "[-RTOK]").
    { rewrite /acquire_at_post. simpl. iSplit; [| done].
      rewrite Nat2Z.inj_add. do 2 iExists _. iFrame. eauto. }
    iModIntro. rewrite /tau_interp.
    iSplitL.
    2: { by iIntros "%". }
    do 2 iExists _. iFrame "SP1 SP2". 
    iRight. iLeft.
    rewrite -{1}(Qp.div_2 q). rewrite Qp.add_sub. simpl.
    iSplit; [| done]. iLeft. iFrame.
  Qed.

  (* TODO: move, remove duplicates *)
  Hypothesis (LS_LB: S tl_exc ≤ LIM_STEPS). 

  (* TODO: move, use in other lemmas *)
  Lemma first_BMU τ π q d0 d n E
    (DEG_LT: deg_lt d d0)
    (LIM: S n <= LIM_STEPS):
    th_phase_frag τ π q (oGS := oGS) -∗ cp π d0 (oGS := oGS) -∗
    BMU E (S n) (cp_mul π d n (oGS := oGS) ∗ exc_lb n (oGS := oGS) ∗ th_phase_frag τ π q (oGS := oGS)) (oGS := oGS).
  Proof using.
    iIntros "PH CP".
    do 2 rewrite -Nat.add_1_r. simpl. iApply BMU_split.
    iApply OU_BMU_rep.
    iApply (OU_rep_wand with "[-PH]").
    2: { iApply (increase_eb_upd_rep0 with "[$]"). }
    iIntros "[#EB PH]".    
    
    iApply OU_BMU. iApply (OU_wand with "[-CP PH]").
    2: { (* TODO: can we remove phase restriction for exchange? *)
         iApply (exchange_cp_upd with "[$] [$] [$]").
         { reflexivity. }
         eauto. }
    iIntros "[CPS PH]".
    iApply BMU_intro. iFrame "#∗".
  Qed.

  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma tl_release_spec (lk: val) c τ:
    tl_is_lock lk c ∗ rel_tok ⊢
        TLAT_FL τ
        (release_at_pre lk (FLP := TLPre) (FLG := TLG))
        (release_at_post lk (FLP := TLPre) (FLG := TLG))
        ∅
        (fun _ => True%type)
        (fun _ _ => None)
        (fun _ '(_, r, _) => #r)
         c
         (tl_release lk)
        (oGS := oGS)
        (FLP := TLPre).
  Proof using fl_degs_wl0 OBLS_AMU LS_LB.
    clear ODl ODd LEl.
    iIntros "(#INV & RT)". rewrite /TLAT_FL /TLAT.
    iIntros (Φ q π Ob RR) "%LIM_STEPS' PRE TAU".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & _ & PH & CP)".
    rewrite /tl_release.

    pure_step_hl. MU_by_BMU.    
    iApply (BMU_lower _ 20).
    { simpl. rewrite /tl_exc. lia. }
    iApply (BMU_wand with "[-CP PH]").
    2: { iApply (first_BMU with "[$] [$]"); [| eauto].
         { trans d__e; [trans d__h0| ]; [trans d__l0|..]; eauto. }
         simpl. etrans; [| apply LIM_STEPS'].
         simpl. rewrite /tl_exc. lia. }
    iIntros "(CPS & #EB & PH)".
    burn_cp_after_BMU. 
    
    (* iApply OU_BMU. iApply (OU_wand with "[-CP PH]"). *)
    (* 2: { (* TODO: can we remove phase restriction for exchange? *) *)
    (*      iApply (exchange_cp_upd with "[$] [$] [$]"). *)
    (*      { reflexivity. } *)
    (*      trans d__e; [trans d__h0| ]; [trans d__l0|..]; eauto. } *)
    (* iIntros "[CPS PH]". BMU_burn_cp. *)

    assert (FAA (Fst lk) #1 = fill_item (FaaLCtx #(LitInt 1)) (Fst lk)) as CTX by done.
    iApply (wp_bind [(FaaLCtx #1)] NotStuck ⊤ τ (Fst lk) (Λ := heap_lang)). simpl.
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & >#EBD & >OW & >Ltk & >EXACT & >HELD & >TOKS & >%DOM__TM & TAUS & _)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ].
    rewrite TAU_elim.
    iMod "TAU" as ([[]]) "[ST TAU]". iModIntro.
    rewrite /release_at_pre. simpl.
    remember_goal.
    iDestruct "ST" as "(>(%&%&%&OW'&HELD')&[% %EQ])". subst.
    iApply "GOAL". iClear "GOAL".
    inversion EQ. subst. clear EQ.
    iDestruct (mapsto_agree with "OW OW'") as %EQ. inversion EQ as [EQ'].
    apply Nat2Z.inj' in EQ'. subst n. clear EQ.
    iCombine "OW OW'" as "OW". rewrite Qp.inv_half_half.
    iDestruct (held_agree with "[$] [$]") as %EQ.
    destruct Nat.eqb eqn:EQ'; [done| ]. apply PeanoNat.Nat.eqb_neq in EQ'. clear EQ.
    iApply (wp_faa with "[$]"). iIntros "!> OW".
    iDestruct "TAU" as "[_ [TAU _]]".
    iNext. MU_by_BMU.
    iSpecialize ("TAU" with "[$OB $PH]").
    { done. }
    simpl. iApply BMU_lower; [apply PeanoNat.Nat.le_add_r| ].
    simpl. rewrite -Nat.add_assoc. iApply BMU_split.
    iApply (BMU_wand with "[-TAU] [$]"). iIntros "CLOS'". rewrite -Nat.add_assoc.
    iSpecialize ("CLOS'" $! (_, (ow + 1), false)).
    remember_goal.
    iMod (held_update _ _ false with "[$] [$]") as "[HELD HELD']".
    iMod (ow_exact_increase _ (ow + 1) with "[$]") as "[EXACT OW_LB]"; [lia| ].
    iApply "GOAL". iClear "GOAL".
    
    rewrite -{2}Qp.inv_half_half. rewrite mapsto_fractional. iDestruct "OW" as "[OW OW']".
    iSpecialize ("CLOS'" with "[OW' HELD']").
    { rewrite /release_at_post. simpl. iSplit; [| by eauto].
      do 2 iExists _. iSplitR; [by eauto| ]. iFrame.
      Set Printing Coercions.
      by rewrite Nat2Z.inj_add. }

    iApply BMU_proper.
    1, 2: reflexivity.
    { apply bi.sep_comm. }
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
    iApply (BMU_frame_l with "[CP]").
    { do 2 iExists _. by iFrame. }
    iApply (BMU_mask_comm with "[-CLOS'] [$]"); [set_solver| ].
    iIntros "Φ". simpl.

    iPoseProof (tau_map_interp_update with "[$] [$] [OW] [$]") as "UPD".
    { by rewrite Nat2Z.inj_add. }
    iApply BMU_split. iApply (BMU_wand with "[-UPD] [$]"). iIntros "(HELD & OW & RTOK & TMI)".
    rewrite Qp.sub_diag. simpl. iSpecialize ("Φ" with "[//]"). 
    iApply BMU_intro. pure_steps.
    iMod ("CLOS" with "[-Φ RR0 CPS OW_LB]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _.
      iRevert "EBD". iFrame. iIntros "#EBd".
      iSplit; [done| ]. iSplit; [iPureIntro; lia| ].
      erewrite bool_decide_ext with (Q := ow + 1 ≠ tk). 
      2: { rewrite DOM__TM elem_of_set_seq. simpl. lia. }
      iSplitR.
      { iApply (exc_lb_le with "EBd"). lia. }
      rewrite bi.sep_assoc. iSplitR "RTOK".
      2: { iApply bi.impl_proper; [..| done | by iFrame].
           rewrite bool_decide_eq_false. iPureIntro. tauto. }
      iSplit; [| done].
      rewrite /held_auth. erewrite Excl_proper; [by iFrame| ].
      destruct Nat.eqb eqn:OW'.
      - apply Nat.eqb_eq in OW'. apply bool_decide_eq_false. lia.
      - apply Nat.eqb_neq in OW'. apply bool_decide_eq_true. lia. }

    iModIntro. by iApply "Φ".
  Qed.

  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma tl_acquire_spec (lk: val) c τ:
    tl_is_lock lk c ⊢
        TLAT_FL τ
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        {[ lvl_acq ]}
        (fun '(_, _, b) => b = false)
        (fun _ _ => Some rel_tok)
        (fun _ _ => #())
        c (tl_acquire lk)
        (oGS := oGS)
        (FLP := TLPre).
  Proof using fl_degs_wl0 d__w OBLS_AMU LS_LB.
    clear ODl ODd LEl. 
    iIntros "#INV". rewrite /TLAT_FL /TLAT.
    iIntros (Φ q π Ob RR) "%LIM_STEPS' PRE TAU".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & #SGT & PH & CP)".

    rewrite /tl_acquire. pure_step_hl. MU_by_BMU.
    simpl. iApply (BMU_lower _ (S tl_exc + (c + c + 2))); [lia| ].
    iApply BMU_split. iApply (BMU_wand with "[-CP PH]").
    2: { iApply (first_BMU with "[$] [$]"); [| eauto].
         apply fl_degs_em. }
    iIntros "(CPSe & #EB & PH)".
    
    iApply (BMU_lower _ 2).
    { simpl. lia. }
    iDestruct (cp_mul_take with "CPSe") as "[CPSe CPe]".
    iApply OU_BMU. iApply (OU_wand with "[-CPe PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] [$]").
         { reflexivity. }
         apply fl_degs_he. }
    iIntros "[CPSh PH]". iDestruct (cp_mul_take with "CPSh") as "[CPSh CPh]".
    iApply OU_BMU. iApply (OU_wand with "[-CPh PH]").
    2: { iApply (exchange_cp_upd _ _ _ _ d__w with "[$] [$] [$]").
         { reflexivity. }
         do 2 (etrans; eauto). }
    iIntros "[CPS PH]". BMU_burn_cp.
    replace 19 with (10 + 9) at 3 by lia.
    iDestruct (cp_mul_split with "CPS") as "[CPS1 CPS]".

    (* Set Printing Coercions. *)
    (* set (post := (fun x => bi_wand rel_tok (Φ x)) : ofe_car valO → ofe_car (iPropO Σ)).  *)
    (* assert (NonExpansive post) as NE_Φ by apply _. *)
    (* assert (NonExpansive RR) as NE_RR. *)
    (* { (* TODO: why it's not inferred automatically? *) *)
    (*   simpl in *. *)
    (*   red. intros ????. *)
    (*   apply discrete_iff in H. *)
    (*   2: by apply _. *)
    (*   apply leibniz_equiv_iff in H. by subst. } *)
    set (post := (fun x => bi_wand rel_tok (Φ x))). 
    
    pure_steps.
    rewrite cp_mul_take. iDestruct "CPSe" as "[CPSe CPe]".
    iApply (wp_wand with "[TAU OB PH CPe RR0 CPS1]").
    { iApply (get_ticket_spec with "[$] [TAU] [OB PH CPe RR0] [$]").
      { done. }
      { simpl. rewrite /TAU_FL. simpl.
        iApply (TAU_Proper with "[$]").
        all: try reflexivity.
        Unshelve. 2: exact post. done. }
      rewrite /TLAT_pre. iFrame "#∗". }
    simpl. iIntros (?) "(%&%&->&WR)".
    rewrite /wait_res.

    do 6 rewrite bi.sep_assoc.    
    iDestruct "WR" as "[WR_ PH]".

    wp_bind (Rec _ _ _)%V.
    do 3 pure_step_cases.
    iApply (wp_wand with "[WR_ PH]").
    { iApply wait_spec; eauto.
      do 5 rewrite -bi.sep_assoc. iDestruct "WR_" as "(?&?&?&?&?&?&?)".
      iFrame "#∗". }

    subst post. simpl. iIntros (?) "[POST ?]". by iApply "POST".
  Qed.

  End AfterInit.

  (* Show Ltac Profile. *)

  (* TODO: move, remove duplicates *)
  Hypothesis (LS_LB: S tl_exc ≤ LIM_STEPS). 

  Program Definition TL_FL: FairLock (oGS := oGS) (FLP := TLPre) := {|
    fl_is_lock FLG hGS := @tl_is_lock FLG;
    fl_create := tl_newlock; fl_acquire := tl_acquire; fl_release := tl_release;
    fl_release_token FLG := @rel_tok _ FLG;
  |}.
  Next Obligation.
    iIntros "%%%%% % !> (CP & PH) POST".
    unshelve iApply (tl_newlock_spec with "[-POST] [$]").
    { eauto. }
    { done. }
    iFrame.
  Qed.
  Next Obligation.
    iIntros "%%%% #LOCK".
    iApply (tl_acquire_spec with "[$]"). done.
  Qed.
  Next Obligation.
    iIntros "%%%% (#LOCK & RT)".
    iApply (tl_release_spec with "[$]"). done.
  Qed.     
    
End Ticketlock.
