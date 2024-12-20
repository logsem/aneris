From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em.
From trillium.fairness.lawyer Require Import program_logic.


Ltac remember_goal :=
  match goal with | |- envs_entails _ ?P =>
    iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ]
  end.


Section TotalTriples.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{LEl: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Context {Σ: gFunctors}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.

  (* Context {Inhabited Locale}. *)
  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.

  (* TODO: move *)
  Definition sgns_level_ge (R: gset SignalId) lm: iProp Σ :=
    [∗ set] s ∈ R, (∃ l, sgn s l None (oGS := oGS) ∗ ⌜ lvl_le lm l ⌝). 

  (* TODO: move *)
  Definition sgns_level_ge' (R: gset SignalId) (L: gset Level): iProp Σ := 
    [∗ set] l ∈ L, sgns_level_ge R l.
  (* TODO: move *)
  Definition sgns_level_gt' (R: gset SignalId) (L: gset Level): iProp Σ := 
    [∗ set] l ∈ L, sgns_level_gt R l (oGS := oGS).

  Let Locale := locale heap_lang. 


  Section AtomicTriples. 
    Context
      (τ: Locale)(* TODO: should it be fixed? *)
      {ST: Type}
      (P: ST -> iProp Σ) (Q: ST -> ST -> iProp Σ) (* second ST is the previous state *)
      (L: gset Level) (* TODO: only finite sets? *)
      {RO: Type}
      (round: ST -> RO) (* TODO: can we get away with ST only? *)
      (TGT: ST -> Prop) (* `{forall x, Decision (TGT x)} *)
      (d__h d__l d__m: Degree)
      (c: nat) (B: nat -> nat)
      (ε__m: coPset)
    .

    Section AtomicUpdates.
      Context
        (ε: coPset)
        (π: Phase)
        (Φ: ST -> ST -> iProp Σ)
        (O: gset SignalId)
        (RR: option RO -> iProp Σ)
      .

      Definition TAU_acc (V: iProp Σ): iProp Σ :=
        |={ε, ∅}=> ∃ x, P x ∗ (
              let abort := P x ={∅, ε}=∗ V in
              (let r := round x in
               ∀ O', obls τ O' (oGS := oGS) ∗ sgns_level_ge' O' L ∗
                        th_phase_eq τ π (oGS := oGS) ∗
                      (∃ r__p, RR r__p ∗ (⌜ r__p = Some r ⌝ ∨ cp π d__h (oGS := oGS))) ∗
                      ⌜ ¬ TGT x ⌝ -∗
                      BMU ∅ c (oGS := oGS) (
                        RR (Some r) ∗ cp π d__l (oGS := oGS) ∗
                        th_phase_eq τ π (oGS := oGS) ∗
                        obls τ O' (oGS := oGS) ∗
                        abort
                      )
              ) ∧
              ((∃ r__p, RR r__p) ∗ ⌜ TGT x ⌝ ∗ obls τ O (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) -∗
               BMU ∅ c (oGS := oGS) (∀ y, Q y x ={∅, ε}=∗ Φ y x)) ∧
              abort
      ).

      Definition TAU_pre (V : () → iProp Σ) (_ : ()) : iProp Σ :=
        TAU_acc (V ()).

      Lemma TAU_acc_mono V1 V2:
        (V1 -∗ V2) -∗ TAU_acc V1 -∗ TAU_acc V2.
      Proof using.
        iIntros "V12 T1". rewrite /TAU_acc.
        iMod "T1" as (?) "[P T1]". iModIntro. iExists _. iFrame "P".
        iSplit; [| iSplit].
        - iIntros (?) "X". iDestruct "T1" as "[T1 _]".
          iSpecialize ("T1" with "[$]").
          iApply (BMU_wand with "[-T1]"); [| done].
          iIntros "(?&?&?&?&AB)". iFrame.
          iIntros "?". iMod ("AB" with "[$]"). by iApply "V12".
        - iDestruct "T1" as "[_ [T1 _]]". done.
        - iDestruct "T1" as "[_ [_ AB]]".
          iIntros "?". iMod ("AB" with "[$]"). by iApply "V12".
      Qed.           

      Local Instance TAU_pre_mono : BiMonoPred TAU_pre.
      Proof.
        constructor.
        - iIntros (P1 P2 ??) "#HP12". iIntros ([]) "AU".
          rewrite /TAU_pre.
          iApply (TAU_acc_mono with "[] [$]"). done. 
        - intros ??. solve_proper.
      Qed.

      Local Definition TAU_def :=
        bi_greatest_fixpoint TAU_pre ().

      (* TODO: seal *)
      Definition TAU := TAU_def.
      
      Lemma TAU_elim:
        TAU ⊣⊢ TAU_acc TAU.
      Proof using.
        rewrite /TAU /TAU_def /=. apply: greatest_fixpoint_unfold.
      Qed.

      Lemma TAU_intro U V:
        Absorbing U → Persistent U →
        (U ∧ V ⊢ TAU_acc V) → U ∧ V ⊢ TAU.
      Proof.
        rewrite /TAU /TAU_def /=.
        iIntros (?? HAU) "[#HP HQ]".
        iApply (greatest_fixpoint_coiter _ (λ _, V)); last done.
        iIntros "!>" ([]) "HQ".
        iApply HAU. iSplit; by iFrame.
      Qed.

    End AtomicUpdates.

    Context `{EM: ExecutionModel heap_lang M}. 
    Context `{hGS: @heapGS Σ _ EM}.
    Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

    Definition TLAT_pre (RR: option RO -> iProp Σ) π (O: gset SignalId): iProp Σ :=
      RR None ∗ obls τ O (oGS := oGS) ∗ sgns_level_gt' O L ∗
      th_phase_eq τ π (oGS := oGS) ∗ cp π d__m (oGS := oGS). 
    
    Definition TLAT e s
      (POST: ST -> ST -> option (iProp Σ))
      (get_ret: ST -> ST -> val)
      : iProp Σ :=
      ∀ Φ π O RR,
        ⌜ B c <= LIM_STEPS ⌝ -∗ TLAT_pre RR π O -∗
        TAU (⊤ ∖ ε__m) π (fun y x => POST y x -∗? Φ (get_ret y x)) O RR -∗
        WP e @ s; τ; ⊤ {{ v, Φ v }}.

  End AtomicTriples.

End TotalTriples.


(* TODO: move to another file *)
Section FairLockSpec.

  Definition FL_st: Type := val * nat * bool.

  Definition fl_round: FL_st -> nat := fun '(_, r, _) => r. 

  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Record FairLockPre := {
    fl_c__cr: nat; fl_B: nat -> nat;
    fl_GS :> gFunctors -> Set;
    fl_LK `{FLG: fl_GS Σ} {HEAP: gen_heapGS loc val Σ}: FL_st -> iProp Σ;
    fl_d__h: Degree;
    fl_d__l: Degree;
    fl_d__m: Degree;
    fl_degs_lh: deg_lt fl_d__l fl_d__h;
    fl_degs_hm: deg_lt fl_d__h fl_d__m;
    fl_ι: namespace;
    fl_acq_lvls: gset Level;                                     
  }.


  Context {Σ: gFunctors}.
  (* Context {invs_inΣ: invGS_gen HasNoLc Σ}. *)
  
  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.
  
  Context `{EM: ExecutionModel heap_lang M}.
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).
  
  Context {FLP: FairLockPre}.
  
  Definition TAU_FL τ P Q L TGT c π (Φ: val -> iProp Σ) O RR: iProp Σ := 
    TAU τ P Q L fl_round TGT (fl_d__h FLP) (fl_d__l FLP)
      c
      (⊤ ∖ ↑(fl_ι FLP))
      π
      (fun _ _ => Φ #()) (* (fun y x => POST y x -∗? Φ (get_ret y x)) *)
      O RR
      (oGS := oGS). 
  
  Definition TLAT_FL τ P Q L TGT c e : iProp Σ := 
    TLAT τ P Q L          
      fl_round TGT
      (fl_d__h FLP) (fl_d__l FLP) (fl_d__m FLP)
      c (fl_B FLP)
      (↑ (fl_ι FLP)) e NotStuck
      (fun _ _ => None)
      (fun _ _ => #())
      (oGS := oGS).
  
  Definition acquire_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ :=
    ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.1.1 = lk ⌝. 
  Definition acquire_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ :=
    fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1 = x.1 /\ x.2 = false /\ y.2 = true⌝.
  Definition release_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ :=
    ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.2 = true /\ x.1.1 = lk⌝. 
  Definition release_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ :=
    fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1.2 = (x.1.2 + 1)%nat /\ y.2 = false /\ y.1.1 = x.1.1 ⌝.
  
  Record FairLock := {    
    fl_create: val; fl_acquire: val; fl_release: val;
    fl_is_lock `{FLG: fl_GS FLP Σ} {HEAP: gen_heapGS loc val Σ}: val -> nat -> iProp Σ;
    fl_is_lock_pers {FLG: fl_GS FLP Σ} lk c :> Persistent (fl_is_lock lk c (FLG := FLG));

    fl_create_spec: ⊢ ⌜ fl_c__cr FLP <= LIM_STEPS ⌝ -∗ ∀ τ c,
      {{{ ⌜ True ⌝ }}} fl_create #() @ τ {{{ lk, RET lk;
         ∃ FLG: fl_GS FLP Σ, fl_LK FLP (lk, 0, false) (FLG := FLG) ∗ fl_is_lock lk c (FLG := FLG) }}};

    fl_acquire_spec {FLG: fl_GS FLP Σ} (lk: val) c τ: (fl_is_lock (FLG := FLG)) lk c ⊢
        TLAT_FL τ 
        (acquire_at_pre lk (FLG := FLG))
        (acquire_at_post lk (FLG := FLG))
        (fl_acq_lvls FLP)
        (fun '(_, _, b) => b = false)
        c (fl_acquire lk);
                                     
    fl_release_spec {FLG: fl_GS FLP Σ} (lk: val) c τ: (fl_is_lock (FLG := FLG)) lk c ⊢
        TLAT_FL τ
        (release_at_pre lk (FLG := FLG))
        (release_at_post lk (FLG := FLG))
        ∅
        (fun _ => True%type)
        c (fl_release lk);
  }.
  
End FairLockSpec.


From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From trillium.fairness.lawyer.examples Require Import signal_map.


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
  (* Definition tau_codom Σ: Type := (((Tid * Phase) * gset SignalId) * gset Level) *  *)
  (*                                   (* (iProp Σ) *) *)
  (*                                   (ofe_mor val (iProp Σ)) *)
  Definition tau_codom Σ: Type := 
    Tid *' Phase *' (gset SignalId) *' (gset Level) *'
    (ofe_mor val (iProp Σ)) *' (ofe_mor (option nat) (iProp Σ)).

  Local Infix "**" := prodO (at level 10, left associativity). 

  (* Definition tau_codomO Σ: ofe := prodO (prodO (prodO (prodO Tid Phase) (gsetO SignalId)) (gsetR Level)) *)
  (*                                   (* ((iPropO Σ)) *) *)
  (*                                       (ofe_morO valO (iPropO Σ)) *)
  (* . *)
  Definition tau_codomO Σ: ofe := 
    Tid ** Phase ** (gsetO SignalId) ** (gsetR Level) ** 
    (ofe_morO valO (iPropO Σ)) ** (ofe_morO (optionR natO) (iPropO Σ)).
 
  Class TicketlockPreG Σ := {
      tl_tau_map_pre :> inG Σ (authUR (gmapUR nat (exclR $ tau_codomO Σ)));
      tl_tokens_pre :> inG Σ (authUR (gset_disjUR natO));
      tl_held_pre :> inG Σ (excl_authUR boolO);
      tl_ow_lb_pre :> inG Σ mono_natUR;
  }.

  Class TicketlockG Σ := {
      tl_pre :> TicketlockPreG Σ;
      tl_γ_tau_map: gname;
      tl_γ_tokens: gname;
      tl_γ_held: gname;
      tl_γ_ow_lb: gname;
  }.

  Definition tau_map_auth `{TicketlockG Σ} (M: gmap nat (tau_codom Σ)) :=
    own tl_γ_tau_map ((● (Excl <$> M)): authUR (gmapUR nat (exclR $ tau_codomO Σ))). 
  Definition ticket_tau `{TicketlockG Σ} (n: nat) (cd: tau_codom Σ) :=
    own tl_γ_tau_map ((◯ {[ n := Excl cd ]}): authUR (gmapUR nat _)).

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

  Lemma ow_exact_lb `{TicketlockG Σ} n:
    ow_exact n -∗ ow_exact n ∗ ow_lb n.
  Proof using.
    iIntros "EX".
    rewrite /ow_exact. rewrite mono_nat_auth_lb_op.
    rewrite /ow_lb -own_op.
    erewrite (mono_nat_lb_op_le_l n) at 1; [| reflexivity].
    by rewrite cmra_assoc.
  Qed.

  Definition tl_LK `{TicketlockG Σ} `{gen_heapGS loc val Σ}
    (st: FL_st): iProp Σ :=
    let '(lk, r, b) := st in
    ∃ (l__ow l__tk: loc),
      ⌜ lk = (#l__ow, #l__tk)%V ⌝ ∗ l__ow ↦{/ 2} #r ∗
      held_auth b.

  (* Right now we just assume that the resulting OM has all needed degrees and levels *)
  Context (d__h0 d__l0 d__m0 d__w: Degree). 
  Hypothesis (fl_degs_lh0: deg_lt d__l0 d__h0)
    (fl_degs_hw: deg_lt d__h0 d__w)
    (fl_degs_wm: deg_lt d__w d__m0). 
    
  Definition tl_ns := nroot .@ "tl".

  Program Definition TLPre: FairLockPre := {|
    fl_c__cr := 2;
    fl_B := fun c => max c 3;
    fl_GS := TicketlockG;
    fl_LK := fun Σ FLG HEAP => tl_LK;
    fl_degs_lh := fl_degs_lh0;
    fl_d__m := d__m0;
    (* fl_degs_hm := ltac:(etrans); *)
    fl_ι := tl_ns;
    fl_acq_lvls := ∅;
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
    let '(τ, π, Ob, L, Φ, RR) := cd in
    obls τ Ob (oGS := oGS) ∗ sgns_level_gt' Ob L (oGS := oGS) ∗
    (* TODO: add later credit ∗ *)
    tl_TAU τ (acquire_at_pre lk (FLP := TLPre) (FLG := TLG)) (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        L
        (fun '(_, _, b) => b = false)
        c π Φ Ob RR.

  Definition tau_map_interp `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) (TM: gmap nat (tau_codom Σ)): iProp Σ :=
    [∗ map] i ↦ cd ∈ TM,
      let Φ := cd.1.2 in
      (TAU_stored lk c cd ∗ ⌜ ow < i ⌝ ∨
       ((Φ #() ∨ ticket_token i) ∗ ⌜ ow = i ⌝) ∨
       ticket_token i ∗ ⌜ i < ow ⌝).
  
  Definition tl_inv_inner `{TicketlockG Σ} (tl: val) (c: nat): iProp Σ :=
    ∃ (l__ow l__tk: loc) (ow tk: nat) TM,
      ⌜ tl = (#l__ow, #l__tk)%V ⌝ ∗ ⌜ ow <= tk ⌝ ∗
      l__ow ↦{/ 2} #ow ∗ l__tk ↦ #tk ∗ ow_exact ow ∗
      tokens_auth tk ∗
      ⌜ dom TM = set_seq 0 tk ⌝ ∗ tau_map_auth TM ∗ tau_map_interp tl c ow TM.

  (* TODO: move *)
  Lemma GSet_inj_equiv:
    ∀ `{Countable K}, Inj equiv equiv (@GSet K _ _).
  Proof using. solve_proper. Qed.

  (* TODO: move *)
  Lemma GSet_Proper: 
    ∀ `{Countable K}, Proper (equiv ==> equiv) (@GSet K _ _).
  Proof using. solve_proper. Qed.

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
    rec: "tl_wait" "x" "lk" :=
      let: "o" := !(Fst "lk") in
      if: "x" = "o"
      then #() (* my turn *)
      else "tl_wait" "x" "lk"
  .

  Definition tl_acquire : val :=
    λ: "lk",
      let: "t" := get_ticket "lk" in
      wait "t" "lk"
  .

  Definition tl_release: val :=
      λ: "lk", FAA (Fst "lk") #1 
  .

  Definition tl_is_lock `{TicketlockG Σ} lk c := inv tl_ns (tl_inv_inner lk c).

  Context {TLG: TicketlockG Σ}.
  
  (* TODO: move, remove duplicates *)
  Ltac BMU_burn_cp :=
    iApply BMU_intro;
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
    iSplitR "CP";
    [| do 2 iExists _; iFrame; iPureIntro; done].   
  
  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS _ EM hGS (↑ nroot)}.
  
  Ltac MU_by_BMU :=
    iApply OBLS_AMU; [by rewrite nclose_nroot| ];
    iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH". 
  
  Ltac MU_by_burn_cp := MU_by_BMU; BMU_burn_cp.
  
  Ltac pure_step_hl := 
    iApply sswp_MU_wp; [done| ];
    iApply sswp_pure_step; [done| ]; simpl;
    iNext.
  
  Ltac pure_step := pure_step_hl; MU_by_burn_cp.   
  Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
  Ltac pure_steps := repeat (pure_step_cases; []).

  (* Definition mk_tcd (τ: Tid) (π: Phase) (R: gset SignalId) *)
  (*                   (Φ: ofe_mor val (iProp Σ)) (RR: ofe_mor (option nat) (iProp Σ)): *)
  (*   tau_codom Σ := *)
  (*   (τ, π, R, Φ, RR).  *)


  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma get_ticket_spec s (lk: val) c (τ: locale heap_lang) π (Φ: ofe_mor val (iProp Σ))
    (Ob: gset SignalId) (RR: ofe_mor (option nat) (iProp Σ))
    (LIM_STEPS': fl_B TLPre c <= LIM_STEPS):
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ⊢
        TAU_FL τ
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        ∅
        (fun '(_, _, b) => b = false)
        c π Φ
        Ob RR
        (oGS := oGS) (FLP := TLPre)
        -∗
        TLAT_pre τ ∅ d__m0 RR π Ob (oGS := oGS)
        -∗
        WP (get_ticket lk) @ s; τ; ⊤ {{ tv, ∃ (t o': nat), ⌜ tv = #t ⌝ ∗
            ow_lb o' ∗ cp_mul π d__h0 (t - o') (oGS := oGS) ∗
            let cd: tau_codom Σ := (τ, π, Ob, ∅, Φ, RR) in
            ticket_token t ∗ (⌜ t = o' ⌝ ∗ Φ #() ∨ ticket_tau t cd) }}.
  Proof using.
    iIntros "[#INV #EB]". rewrite /TLAT_FL /TLAT.
    iIntros "TAU PRE".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & _ & PH & CP)".
    rewrite /get_ticket.

    pure_step_hl. MU_by_BMU.
    iApply (BMU_lower _ 2).
    { simpl. lia. }
    iApply OU_BMU. iApply (OU_wand with "[-CP PH]").
    2: { (* TODO: can we remove phase restriction for exchange? *)
         iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         apply fl_degs_wm. }
    iIntros "[CPSw PH]". iDestruct (cp_mul_take with "CPSw") as "[CPSw CPw]". 
    iApply OU_BMU. iApply (OU_wand with "[-CPw PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         trans d__h0; eauto. }
    iIntros "[CPS PH]". BMU_burn_cp.

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
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & >OW & >TK & >EXACT & >TOKS & >%DOM__TM & TM & TAUS)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    rewrite /TAU_FL. rewrite TAU_elim. iMod "TAU" as (st) "[[ST %ST__lk] TAU]".
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_faa with "TK").
    iIntros "!> TK'". iNext. MU_by_BMU.
    iApply (BMU_lower _ 3).
    { simpl. lia. }
    iDestruct (cp_mul_take with "CPSw") as "[CPSw CPw]".
    apply Nat.le_sum in LEot as [d ->].
    iApply OU_BMU. iApply (OU_wand with "[-CPw PH]").
    2: { iApply (exchange_cp_upd with "[$] [$]").
         { apply (Nat.le_refl d). }
         { done. }
         { apply fl_degs_hw. }
         (* TODO: requires dynamic eb updates *)
         admit. }
    iIntros "[CPSh PH]".
    iDestruct (ow_exact_lb with "[$]") as "[EXACT LB]". 

    destruct (Nat.eq_0_gt_0_cases d) as [-> | QUEUE].
    2: { 
    
    
    { iNext.
      Set Printing Coercions.
    Abort.

    

  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma tl_acquire_spec (lk: val) c τ:
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ⊢
        TLAT_FL τ
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        ∅
        (fun '(_, _, b) => b = false)
        c (tl_acquire lk)
        (oGS := oGS)
        (FLP := TLPre).
  Proof using.    
    iIntros "[#INV #EB]". rewrite /TLAT_FL /TLAT.
    iIntros (Φ π Ob RR) "%LIM_STEPS' PRE TAU".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & _ & PH & CP)".
    rewrite /tl_acquire /get_ticket.

    pure_step_hl. MU_by_BMU.
    iApply (BMU_lower _ 2).
    { simpl. lia. }
    iApply OU_BMU. iApply (OU_wand with "[-CP PH]").
    2: { (* TODO: can we remove phase restriction for exchange? *)
         iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         apply fl_degs_wm. }
    iIntros "[CPSw PH]". iDestruct (cp_mul_take with "CPSw") as "[CPSw CPw]". 
    iApply OU_BMU. iApply (OU_wand with "[-CPw PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         trans d__h0; eauto. }
    iIntros "[CPS PH]". BMU_burn_cp.

    pure_steps.
    Set Printing Coercions.
    Set Printing All.
(FAA (Snd (Val lk)) (Val (LitV (LitInt (Zpos xH)))))
(FAA (Snd (Val lk)) (Val (LitV (LitInt (Zpos xH)))))
    wp_bind (Snd _)%E. 
    

    
  
End Ticketlock. 
