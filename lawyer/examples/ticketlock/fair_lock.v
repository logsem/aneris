From lawyer.examples Require Import obls_atomic.
From lawyer.obligations Require Import obligations_model  obligations_am obligations_em obligations_logic.
From lawyer Require Import sub_action_em program_logic.
From lawyer.obligations Require Import obligations_resources env_helpers.


(* Section FairLockSpec. *)

(*   Definition FL_st: Type := val * nat * bool. *)

(*   Definition fl_round: FL_st -> nat := fun '(_, r, _) => r.  *)

(*   Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}. *)
(*   Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.  *)
  
(*   Let Degree := ofe_car DegO. *)
(*   Let Level := ofe_car LevelO. *)

(*   Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}. *)
(*   Let OP := LocaleOP (Locale := locale heap_lang). *)
(*   Existing Instance OP. *)
(*   Let OM := ObligationsModel. *)
  
(*   Record FairLockPre := { *)
(*     fl_c__cr: nat; fl_B: nat -> nat; *)
(*     fl_GpreS :> gFunctors -> Set; *)
(*     fl_GS :> gFunctors -> Set; *)
(*     fl_LK {Σ: gFunctors} {FLG: fl_GS Σ} {HEAP: gen_heapGS loc val Σ}: FL_st -> iProp Σ; *)
(*     fl_d__h: Degree; *)
(*     fl_d__l: Degree; *)
(*     fl_d__m: Degree; *)
(*     fl_degs_lh: deg_lt fl_d__l fl_d__h; *)
(*     fl_degs_hm: deg_lt fl_d__h fl_d__m; *)
(*     fl_acq_lvls: gset Level;                                      *)
(*     fl_create: val; fl_acquire: val; fl_release: val; *)
(*   }. *)

(*   Definition fl_ι: namespace := nroot .@ "fair_lock". *)

(*   Context {Σ: gFunctors}. *)
  
(*   Let OAM := ObligationsAM.  *)
(*   Let ASEM := ObligationsASEM. *)
(*   (* Keeping the more general interface for future developments *) *)
(*   Context `{oGS': @asem_GS _ _ ASEM Σ}. *)
(*   Let oGS: ObligationsGS (OP := OP) Σ := oGS'. *)
(*   Existing Instance oGS. *)
  
(*   Context `{EM: ExecutionModel heap_lang M}. *)
(*   Context `{hGS: @heapGS Σ _ EM}. *)
(*   Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS). *)
  
(*   Context {FLP: FairLockPre}. *)

(*   Definition TAU_FL τ P Q L c π q Φ O fg: iProp Σ :=   *)
(*     TAU τ P Q L c (⊤ ∖ ↑fl_ι) π q Φ O fg (ST := FL_st) (oGS' := oGS'). *)

(*   (* Definition TAU_FL τ P Q L (* TGT *) c π q *) *)
(*   (*   Φ *) *)
(*   (*   O *) *)
(*   (*   fg: iProp Σ :=  *) *)
(*   (*   TAU τ P Q L (* fl_round *) *) *)
(*   (*     (* TGT *) *) *)
(*   (*     (* (fl_d__h FLP) (fl_d__l FLP) *) *) *)
(*   (*     c *) *)
(*   (*     (⊤ ∖ ↑fl_ι) *) *)
(*   (*     π q *) *)
(*   (*     Φ *) *)
(*   (*     O *) *)
(*   (*     (* RR *) *) *)
(*   (*     (* (fl_FG_RR RR π) *) *) *)
(*   (*     fg *) *)
(*   (*     (oGS' := oGS'). *) *)
  
(*   Definition acq_FG_RR (RR: option nat -> iProp Σ) π: AbortClause (ST := FL_st) := *)
(*     AC_RR (fl_d__l FLP) π *)
(*       (fun '(_, n, _) => n) (fun '(_, _, b) => (⌜ b = true ⌝)%I) *)
(*       RR (fl_d__h FLP) (oGS' := oGS'). *)
  
(*   Definition TLAT_FL τ P Q L (* TGT *) fg (POST: FL_st -> FL_st -> option (iProp Σ)) *)
(*     get_ret c e : iProp Σ :=  *)
(*     TLAT τ P Q L *)
(*       (* fl_round *) *)
(*       (* TGT *) *)
(*       (* (fl_d__h FLP) (fl_d__l FLP) (fl_d__m FLP) *) *)
(*       (fl_d__m FLP) *)
(*       c (fl_B FLP) *)
(*       (↑ fl_ι) e NotStuck *)
(*       (* (fl_d__h FLP) (fl_d__l FLP)  *) *)
(*       fg *)
(*       POST *)
(*       get_ret *)
(*       (oGS' := oGS'). *)
  
(*   Definition TLAT_FL_RR τ P Q L TGT (POST: FL_st -> FL_st -> option (iProp Σ)) *)
(*     get_ret c e : iProp Σ :=  *)
(*     TLAT_RR τ P Q L *)
(*       (fl_d__m FLP)  *)
(*       c (fl_B FLP) *)
(*       (↑ fl_ι) e NotStuck *)
(*       (fl_d__h FLP) (fl_d__l FLP) *)
(*       fl_round *)
(*       TGT *)
(*       POST *)
(*       get_ret *)
(*       (oGS' := oGS'). *)
  
(*   Definition acquire_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ := *)
(*     ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.1.1 = lk ⌝.  *)
(*   Definition acquire_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ := *)
(*     fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1 = x.1 /\ x.2 = false /\ y.2 = true⌝. *)
(*   Definition release_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ := *)
(*     ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.2 = true /\ x.1.1 = lk⌝.  *)
(*   Definition release_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ := *)
(*     fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1.2 = (x.1.2 + 1)%nat /\ y.2 = false /\ y.1.1 = x.1.1 ⌝. *)
    
(* End FairLockSpec. *)


(* Section FairLockDef. *)

(*   Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}. *)
(*   Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.  *)
  
(*   Let Degree := ofe_car DegO. *)
(*   Let Level := ofe_car LevelO. *)

(*   Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}. *)
(*   Let OP := LocaleOP (Locale := locale heap_lang). *)
(*   Existing Instance OP. *)
(*   Let OM := ObligationsModel. *)

(*   Context {FLP: FairLockPre}. *)

(*   Record FairLock := {     *)

(*     fl_is_lock `{FLG: fl_GS FLP Σ} {HEAP: gen_heapGS loc val Σ} *)
(*       (ASEM := ObligationsASEM) {oGS': @asem_GS _ _ ASEM Σ}: val -> nat -> iProp Σ; *)
(*     fl_is_lock_pers {Σ} {FLG: fl_GS FLP Σ} {HEAP: gen_heapGS loc val Σ} *)
(*       (ASEM := ObligationsASEM) {oGS': @asem_GS _ _ ASEM Σ} *)
(*       lk c :: Persistent (fl_is_lock lk c (FLG := FLG) (oGS' := oGS')); *)

(*     fl_release_token `{FLG: fl_GS FLP Σ}: iProp Σ; *)

(*     fl_create_spec {Σ} {FLG_PRE: fl_GpreS FLP Σ} *)
(*         (ASEM := ObligationsASEM) {oGS': @asem_GS _ _ ASEM Σ} `{EM: ExecutionModel heap_lang M} {hGS : heapGS Σ EM} *)
(*       (oGS: ObligationsGS (OP := OP) Σ := oGS'): *)
(*       ⊢ ⌜ fl_c__cr FLP <= LIM_STEPS ⌝ -∗ ∀ τ π c, *)
(*         {{{ cp π (fl_d__m FLP) ∗ th_phase_eq τ π }}} *)
(*             fl_create FLP #() @ τ *)
(*         {{{ lk, RET lk; ∃ FLG: fl_GS FLP Σ, fl_LK _ (lk, 0, false) (FLG := FLG) ∗ fl_is_lock lk c (FLG := FLG) (oGS' := oGS') ∗ th_phase_eq τ π }}}; *)

(*     fl_acquire_spec {Σ} {FLG: fl_GS FLP Σ} *)
(*         (ASEM := ObligationsASEM) {oGS': @asem_GS _ _ ASEM Σ} `{EM: ExecutionModel heap_lang M} {hGS : heapGS Σ EM} *)
(*       (oGS: ObligationsGS (OP := OP) Σ := oGS') *)
(*       (lk: val) c τ: *)
(*       (fl_is_lock (FLG := FLG) (oGS' := oGS')) lk c ⊢ *)
(*         TLAT_FL_RR τ *)
(*         (acquire_at_pre lk (FLG := FLG)) *)
(*         (acquire_at_post lk (FLG := FLG)) *)
(*         (fl_acq_lvls FLP) *)
(*         (fun '(_, _, b) => ⌜ b = true ⌝) *)
(*         (fun _ _ => Some $ fl_release_token (FLG := FLG)) *)
(*         (fun _ _ => #()) *)
(*         c (fl_acquire FLP lk) *)
(*         (oGS' := oGS') (FLP := FLP); *)
                                     
(*     fl_release_spec {Σ} {FLG: fl_GS FLP Σ} *)
(*         (ASEM := ObligationsASEM) {oGS': @asem_GS _ _ ASEM Σ} `{EM: ExecutionModel heap_lang M} {hGS : heapGS Σ EM} *)
(*       (oGS: ObligationsGS (OP := OP) Σ := oGS') *)
(*       (lk: val) c τ: (fl_is_lock (FLG := FLG) (oGS' := oGS')) lk c ∗ fl_release_token (FLG := FLG) ⊢ *)
(*         TLAT_FL τ *)
(*         (release_at_pre lk (FLG := FLG)) *)
(*         (release_at_post lk (FLG := FLG)) *)
(*         ∅ *)
(*         (* (fun _ => True%type) *) *)
(*         AC_none *)
(*         (fun _ _ => None) *)
(*         (fun _ '(_, r, _) => #r) *)
(*         c (fl_release FLP lk) *)
(*         (oGS' := oGS') (FLP := FLP); *)
(*   }. *)

(* End FairLockDef. *)


Section FairLockSpec.

  Definition FL_st: Type := val * nat * bool.

  Definition fl_round: FL_st -> nat := fun '(_, r, _) => r. 

  Context `{OP: OP_HL DegO LvlO LIM_STEPS}.
  Existing Instance om_hl_OP.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).
  Context `{EM: ExecutionModel heap_lang M}.

  
  Record FairLockPre := {
    fl_c__cr: nat; fl_B: nat -> nat;
    fl_GpreS : gFunctors -> Set;
    fl_GS : gFunctors -> Set;
    fl_LK `{FLG: fl_GS Σ} {OHE: OM_HL_Env OP EM Σ}: FL_st -> iProp Σ;
    fl_d__h: Degree;
    fl_d__l: Degree;
    fl_d__m: Degree;
    fl_degs_lh: deg_lt fl_d__l fl_d__h;
    fl_degs_hm: deg_lt fl_d__h fl_d__m;
    fl_acq_lvls: gset Level;
    fl_create: val; fl_acquire: val; fl_release: val;
  }.

  Definition fl_ι: namespace := nroot .@ "fair_lock".

  Context {Σ: gFunctors}.
  Context {OHE: OM_HL_Env OP EM Σ}.
  
  (* Let OAM := ObligationsAM.  *)
  (* Let ASEM := ObligationsASEM. *)
  (* (* Keeping the more general interface for future developments *) *)
  (* Context `{oGS': @asem_GS _ _ ASEM Σ}. *)
  (* Let oGS: ObligationsGS (OP := OP) Σ := oGS'. *)
  (* Existing Instance ohe_oGS'. *)
  
  (* Context `{hGS: @heapGS Σ _ EM}. *)
  (* Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS). *)
  
  Context {FLP: FairLockPre}.

  Definition TAU_FL τ P Q L c π q Φ O fg: iProp Σ :=  
    TAU τ P Q L c (⊤ ∖ ↑fl_ι) π q Φ O fg (ST := FL_st) (oGS' := ohe_oGS').

  Definition acq_FG_RR (RR: option nat -> iProp Σ) π: AbortClause (ST := FL_st) :=
    AC_RR (fl_d__l FLP) π
      (fun '(_, n, _) => n) (fun '(_, _, b) => (⌜ b = true ⌝)%I)
      RR (fl_d__h FLP) (oGS' := ohe_oGS').
  
  Definition TLAT_FL τ P Q L (* TGT *) fg (POST: FL_st -> FL_st -> option (iProp Σ))
    get_ret c e : iProp Σ := 
    TLAT τ P Q L
      (fl_d__m FLP)
      c (fl_B FLP)
      (↑ fl_ι) e NotStuck
      fg
      POST
      get_ret
      (oGS' := ohe_oGS').
  
  Definition TLAT_FL_RR τ P Q L TGT (POST: FL_st -> FL_st -> option (iProp Σ))
    get_ret c e : iProp Σ := 
    TLAT_RR τ P Q L
      (fl_d__m FLP) 
      c (fl_B FLP)
      (↑ fl_ι) e NotStuck
      (fl_d__h FLP) (fl_d__l FLP)
      fl_round
      TGT
      POST
      get_ret
      (oGS' := ohe_oGS').
  
  Definition acquire_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ :=
    ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.1.1 = lk ⌝. 
  Definition acquire_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ :=
    fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1 = x.1 /\ x.2 = false /\ y.2 = true⌝.
  Definition release_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ :=
    ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.2 = true /\ x.1.1 = lk⌝. 
  Definition release_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ :=
    fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1.2 = (x.1.2 + 1)%nat /\ y.2 = false /\ y.1.1 = x.1.1 ⌝.
    
End FairLockSpec.
  

Section FairLockDef.

  (* Context `{OP: OP_HL DegO LvlO LIM_STEPS}. *)
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Context {FLP: FairLockPre}.

  Record FairLock := {    

    fl_is_lock `{FLG: fl_GS FLP Σ} {OHE: OM_HL_Env OP EM Σ}:
      val -> nat -> iProp Σ;

    fl_is_lock_pers `{FLG: fl_GS FLP Σ} {OHE: OM_HL_Env OP EM Σ}
      lk c :: Persistent (fl_is_lock lk c (FLG := FLG));

    fl_release_token `{FLG: fl_GS FLP Σ}: iProp Σ;

    fl_create_spec `{FLG_PRE: fl_GpreS FLP Σ} {OHE: OM_HL_Env OP EM Σ}
      :
      ⊢ ⌜ fl_c__cr FLP <= LIM_STEPS ⌝ -∗ ∀ τ π c,
        {{{ cp π (fl_d__m FLP) ∗ th_phase_eq τ π }}}
            fl_create FLP #() @ τ
        {{{ lk, RET lk; ∃ FLG: fl_GS FLP Σ, fl_LK _ (lk, 0, false) (FLG := FLG) ∗ fl_is_lock lk c (FLG := FLG) ∗ th_phase_eq τ π }}};

    fl_acquire_spec `{FLG: fl_GS FLP Σ} {OHE: OM_HL_Env OP EM Σ}
      (lk: val) c τ:
      (fl_is_lock (FLG := FLG)) lk c ⊢
        TLAT_FL_RR τ
        (acquire_at_pre lk (FLG := FLG))
        (acquire_at_post lk (FLG := FLG))
        (fl_acq_lvls FLP)
        (fun '(_, _, b) => ⌜ b = true ⌝)
        (fun _ _ => Some $ fl_release_token (FLG := FLG))
        (fun _ _ => #())
        c (fl_acquire FLP lk)
        (FLP := FLP);
                                     
    fl_release_spec `{FLG: fl_GS FLP Σ} {OHE: OM_HL_Env OP EM Σ}
      (lk: val) c τ: (fl_is_lock (FLG := FLG)) lk c ∗ fl_release_token (FLG := FLG) ⊢
        TLAT_FL τ
        (release_at_pre lk (FLG := FLG))
        (release_at_post lk (FLG := FLG))
        ∅
        AC_none
        (fun _ _ => None)
        (fun _ '(_, r, _) => #r)
        c (fl_release FLP lk)
        (FLP := FLP);
  }.

End FairLockDef.
