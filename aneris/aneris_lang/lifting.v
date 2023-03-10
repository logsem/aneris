From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre lifting ectx_lifting atomic.
From aneris.aneris_lang Require Import aneris_lang base_lang.
From aneris.aneris_lang.state_interp Require Import
     state_interp state_interp_events.
From stdpp Require Import binders.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
    [head_step]. The tactic will discharge head-reductions starting from values,
    and simplifies hypothesis related to conversions from and to values, and
    finite map operations. This tactic is slightly ad-hoc and tuned for proving
    our lifting lemmas. *)
Ltac inv_head_step :=
  repeat
    match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : aneris_to_val _ = Some _ |- _ => apply to_base_aneris_val in H
    | H : base_lang.head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
      inversion H; subst; clear H
    | H : head_step ?e _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
    | H: socket_step _ ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
    end.

Local Ltac solve_exec_safe :=
  intros;
  repeat match goal with
         | H: _ ∧ _ |- _ => destruct H as [??]
         end;
  simplify_eq;
  do 3 eexists; eapply (LocalStepPureS _ ∅); econstructor; eauto.
Local Ltac solve_exec_puredet :=
  simpl; intros; inv_head_step;
  first (by repeat match goal with
                   | H: _ ∧ _ |- _ => destruct H as [??]; simplify_eq
                   | H : to_val _ = Some _ |- _ =>
                     rewrite to_of_val in H; simplify_eq
                   end);
  try by match goal with
         | H : socket_step _ _ _ _ _ _ _ |- _ =>
           inversion H
         end.
Local Ltac solve_pure_exec :=
  simplify_eq; rewrite /PureExec; intros;
  apply nsteps_once, pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

#[global] Instance into_val_val n v : IntoVal (mkExpr n (Val v)) (mkVal n v).
Proof. done. Qed.
#[global] Instance as_val_val n v : AsVal (mkExpr n (Val v)).
Proof. by exists (mkVal n v). Qed.

#[global] Instance into_val_base_val v : IntoVal (Val v) v.
Proof. done. Qed.
#[global] Instance as_val_base_val v : AsVal (Val v).
Proof. by exists v. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; inv_head_step; try naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; inv_head_step;
       rewrite /aneris_to_val /is_Some /=; eexists; by
         match goal with
         | H: _ = _ |- _ => rewrite -H
         end
    ].

Lemma aneris_base_fill K ip e :
  mkExpr ip (fill (Λ := base_ectxi_lang) K e) =
  fill (Λ := aneris_ectxi_lang) K (mkExpr ip e).
Proof.
  revert e; induction K as [|k K IHK] using rev_ind; first done.
  intros e.
  rewrite !fill_app /= -IHK /=; done.
Qed.

#[global] Instance aneris_pure_exec_fill
         (K : list ectx_item) ip (φ : Prop) (n : nat) e1 e2 :
  PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
  @PureExec aneris_lang φ n
            (mkExpr ip (@fill base_ectxi_lang K e1))
            (mkExpr ip (@fill base_ectxi_lang K e2)).
Proof.
  intros.
  rewrite !aneris_base_fill.
  eapply pure_exec_ctx; first apply _; done.
Qed.

#[global] Instance binop_atomic n s op v1 v2 :
  Atomic s (mkExpr n (BinOp op (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
#[global] Instance alloc_atomic lbl n s v : Atomic s (mkExpr n (Alloc lbl (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance load_atomic n s v : Atomic s (mkExpr n (Load (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance store_atomic n s v1 v2 : Atomic s (mkExpr n (Store (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
#[global] Instance cmpxchg_atomic n s v0 v1 v2 :
  Atomic s (mkExpr n (CAS (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
#[global] Instance fork_atomic n s e : Atomic s (mkExpr n (Fork e)).
Proof. solve_atomic. Qed.
#[global] Instance skip_atomic n s : Atomic s (mkExpr n Skip).
Proof. solve_atomic. Qed.
#[global] Instance rec_atomic n s f x e: Atomic s (mkExpr n (Rec f x e)).
Proof. solve_atomic. Qed.
#[global] Instance injr_atomic n s v : Atomic s (mkExpr n (InjR (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance injl_atomic n s v : Atomic s (mkExpr n (InjL (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance fst_atomic n s v : Atomic s (mkExpr n (Fst (Val v))).
Proof. solve_atomic. Qed.
#[global] Instance snd_atomic n s v : Atomic s (mkExpr n (Snd (Val v))).
Proof. solve_atomic. Qed.

#[global] Instance newsocket_atomic n s :
  Atomic s (mkExpr n (NewSocket #())).
Proof. solve_atomic. Qed.
#[global] Instance socketbind_atomic n v0 v1  s :
  Atomic s (mkExpr n (SocketBind (Val v0) (Val v1))).
Proof. solve_atomic. Qed.
#[global] Instance sendto_atomic n v0 v1 v2 s :
  Atomic s (mkExpr n (SendTo (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.

#[global] Instance setreceivetimeout_atomic n v0 v1 v2 s:
    Atomic s (mkExpr n (SetReceiveTimeout (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.

#[global] Instance receive_from_stutteringatomic n sh s :
  StutteringAtomic s (mkExpr n (ReceiveFrom (Val $ LitV $ sh))).
Proof.
  apply strongly_stutteringatomic_stutteringatomic,
    ectx_language_stutteringatomic.
  - inversion 1; inv_head_step; try naive_solver; [].
    rewrite insert_id; last done.
    match goal with
      |- context [state_heaps ?st] => by destruct st; eauto
    end.
  - apply ectxi_language_sub_redexes_are_values; intros [] **; inv_head_step;
      rewrite /aneris_to_val /is_Some /=; eexists; by
          match goal with
          | H: _ = _ |- _ => rewrite -H
          end.
Qed.

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

#[global] Instance pure_rec n f x erec :
  PureExec True 1 (mkExpr n (Rec f x erec)) (mkExpr n (Val $ RecV f x erec)).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_pairc n v1 v2:
  PureExec True 1 (mkExpr n (Pair (Val v1) (Val v2)))
           (mkExpr n (Val $ PairV v1 v2)).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injlc n v :
  PureExec True 1 (mkExpr n (InjL $ Val v)) (mkExpr n (Val $ InjLV v)).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injrc n v :
  PureExec True 1 (mkExpr n (InjR $ Val v)) (mkExpr n (Val $ InjRV v)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_beta n f x erec v1 v2 `{!AsRecV v1 f x erec} :
  PureExec True 1 (mkExpr n (App (Val v1) (Val v2)))
           (mkExpr n (subst' x v2 (subst' f v1 erec))).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

#[global] Instance pure_unop n op v v' :
  PureExec (un_op_eval op v = Some v') 1 (mkExpr n (UnOp op (Val v)))
           (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_binop n op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1
           (mkExpr n (BinOp op (Val v1) (Val v2))) (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_if_true n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool true) e1 e2)) (mkExpr n e1).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_if_false n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool false) e1 e2))
           (mkExpr n e2).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_fst n v1 v2 :
  PureExec True 1 (mkExpr n (Fst (PairV v1 v2))) (mkExpr n (Val v1)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_snd n v1 v2  :
  PureExec True 1 (mkExpr n (Snd (PairV v1 v2))) (mkExpr n (Val v2)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_find_from n v0 v1 n1 v2 v' :
  PureExec (index n1 v2 v0 = v' ∧ Z.of_nat n1 = v1) 1
           (mkExpr n (FindFrom (Val $ LitV $ LitString v0)
                       (Val $ LitV $ LitInt v1)
                       (Val $ LitV $ LitString v2)))
           (mkExpr n (of_val (option_nat_to_val v'))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_substring n v0 v1 n1 v2 n2 v' :
  PureExec (substring n1 n2 v0 = v' ∧ Z.of_nat n1 = v1 ∧ Z.of_nat n2 = v2) 1
           (mkExpr
              n (Substring
                   (LitV $ LitString v0) (LitV $ LitInt v1) (LitV $ LitInt v2)))
           (mkExpr n (of_val (LitV $ LitString v'))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inl n v e1 e2  :
  PureExec True 1 (mkExpr n (Case (Val $ InjLV v) e1 e2))
           (mkExpr n (App e1 (Val v))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inr n v e1 e2 :
  PureExec True 1 (mkExpr n (Case (Val $ InjRV v) e1 e2))
           (mkExpr n (App e2 (Val v))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_make_address n v1 v2 :
  PureExec True 1
           (mkExpr n (MakeAddress (LitV (LitString v1)) (LitV (LitInt (v2)))))
           (mkExpr
              n (LitV (LitSocketAddress (SocketAddressInet v1 (Z.to_pos v2))))).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_get_address_info n ip p :
  PureExec True 1
           (mkExpr n (GetAddressInfo (LitV (LitSocketAddress (SocketAddressInet ip p)))))
           (mkExpr n (PairV #ip #(Zpos p))).
Proof. solve_pure_exec. Qed.

Opaque aneris_state_interp.

Section primitive_laws.
  Context `{anerisG Mdl Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : aneris_val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.
  Implicit Types σ : base_lang.state.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types mh : messages_history.

  #[global] Instance aneris_lang_allows_stuttering :
    AllowsStuttering (aneris_to_trace_model Mdl) Σ.
  Proof.
    refine ({| stuttering_label := () |}).

    iIntros (ex atr c δ ? ? Hval Hc Hδ) "(? & ? & ? & ? & Hauth)".
    rewrite /state_interp /=.
    rewrite (last_eq_trace_ends_in ex c) //=.
    rewrite (last_eq_trace_ends_in atr δ) //=.
    rewrite aneris_events_state_interp_same_tp; [| |done|done]; last first.
    { eapply extend_valid_exec; eauto. }
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro.
    rewrite -message_history_evolution_id; iFrame.
    iPureIntro; apply user_model_evolution_id.
  Qed.

  #[global] Instance aneris_lang_allows_pure_step :
    AllowsPureStep (aneris_to_trace_model Mdl) Σ.
  Proof.
    refine ({| pure_label := () |}).

    iIntros (ex atr tp tp' σ δ ? ? ? Hex Hδ) "(?&?&?&?&Hauth)".
    rewrite /state_interp /=.
    rewrite (last_eq_trace_ends_in ex (tp, σ)) //=.
    rewrite (last_eq_trace_ends_in atr δ) //=.
    rewrite aneris_events_state_interp_pure; [| |done|done]; last first.
    { eapply extend_valid_exec; eauto. }
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro.
    rewrite -message_history_evolution_id; iFrame.
    iPureIntro; apply user_model_evolution_id.
  Qed.

  Lemma wp_fork n k E tid e Φ :
    ▷ Φ (mkVal n #()) ∗ (∀ tid', ▷ WP (mkExpr n e) @ k; (n, tid'); ⊤ {{ _, True }}) ⊢
    WP (mkExpr n (Fork e)) @ k; (n, tid); E {{ Φ }}.
  Proof.
    iIntros "[HΦ He]". iApply wp_lift_atomic_head_step; [done|].
    iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hlocale) "(?&?&?&%&Hauth) !>".
    iSplit.
    - iPureIntro. solve_exec_safe.
    - iIntros (e2 σ2 efs Hstep).
      assert (Hval: valid_exec (ex :tr[Some $ locale_of tp1 $ ectx_language.fill K (mkExpr n (Fork e))]:
                                  (tp1 ++ ectx_language.fill K e2 :: tp2 ++ efs, σ2))).
      { eapply extend_valid_exec; [done|done|]. econstructor 1; last econstructor; eauto. }
      inv_head_step.
      rewrite (last_eq_trace_ends_in _ _ Hex).
      iExists (trace_last atr), ().
      iIntros "!>".
      iMod (steps_auth_update_S with "Hauth") as "Hauth".
      iIntros "!>". iFrame.
      rewrite ectx_language.locale_fill /= Hlocale // in Hval.
      rewrite aneris_events_state_interp_pure; [|done|done|done].
      rewrite -message_history_evolution_id; iFrame; eauto.
      iSplit.
      { iPureIntro; apply user_model_evolution_id. }
      eauto.
  Qed.

  Lemma wp_alloc_gen n lblo evs k E ζ v :
    {{{ ▷ is_node n ∗ ▷ match lblo with Some lbl => alloc_evs lbl evs | _ => True end }}}
      (mkExpr n (Alloc lblo (Val v))) @ k; ζ; E
    {{{ l, RET (mkVal n #l); l ↦[n] v ∗
        match lblo with
          Some lbl =>
          ∃ h (σ : state),
          ⌜valid_allocObs n l σ h⌝ ∗
          alloc_evs lbl (evs ++ [allocObs n lbl l v σ h])
       | _ => True end }}}.
  Proof.
    iIntros (Φ) "[>Hn Haevs] HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (is_node_heap_valid with "Hσ Hn") as (h) "%".
    iSplitR; [by iPureIntro; do 3 eexists; eapply LocalStepS; eauto | ].
    iIntros (v2 σ2 efs Hstep).
    destruct lblo as [lbl|].
    - pose proof (conj Hstep I) as Hstep'.
      inv_head_step. iNext.
      destruct Hstep' as [Hstep' _].
      iMod (aneris_state_interp_alloc_heap with "Hn Hσ") as "[Hσ Hl]"; [done..|].
      iMod (aneris_events_state_interp_alloc_triggered with "Haevs Hevs") as "[Hevs Haevs]";
      [done|done|done| |].
      { eexists _, _, _, _; eauto. }
      iExists (trace_last atr), ().
      iMod (steps_auth_update _ (S (trace_length ex)) with "Hauth")
        as "[Hauth _]"; [by eauto|].
      iIntros "!>".
      rewrite -message_history_evolution_id; iFrame.
      iSplit; [done|].
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      iApply "HΦ"; eauto with iFrame.
    - pose proof Hex as Htrig.
      eapply aneris_events_state_interp_no_triggered in Htrig;
        [|done|done|done|done|done].
      inv_head_step. iNext.
      iMod (aneris_state_interp_alloc_heap with "Hn Hσ") as "[Hσ Hl]"; [done..|].
      iMod (steps_auth_update_S with "Hauth") as "Hauth".
      iExists (trace_last atr), (). iIntros "!>".
      rewrite -message_history_evolution_id Htrig; iFrame.
      iSplit; [done|].
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      iApply "HΦ"; iFrame; done.
  Qed.

  Lemma wp_alloc n k E ζ v :
    {{{ ▷ is_node n }}}
      (mkExpr n (ref (Val v))) @ k; ζ; E
    {{{ l, RET (mkVal n #l); l ↦[n] v }}}.
  Proof.
    iIntros (Φ) "Hn HΦ".
    iApply (wp_alloc_gen _ None [] with "[$Hn //]").
    iNext. iIntros (?) "[? _]"; by iApply "HΦ".
  Qed.

  Lemma wp_alloc_tracked n lbl evs k E ζ v :
    {{{ ▷ is_node n ∗ ▷ alloc_evs lbl evs }}}
      (mkExpr n (ref<<lbl>> (Val v))) @ k; ζ; E
    {{{ l h (σ : state), RET (mkVal n #l); l ↦[n] v ∗
          ⌜valid_allocObs n l σ h⌝ ∗
          alloc_evs lbl (evs ++ [allocObs n lbl l v σ h]) }}}.
  Proof.
    iIntros (Φ) "Hn HΦ".
    iApply (wp_alloc_gen _ (Some lbl) with "[$Hn //]").
    iNext. iIntros (?) "[? Hevs]".
    iDestruct "Hevs" as (? ?) "[% ?]".
    iApply "HΦ"; iFrame; done.
  Qed.

  Lemma wp_load n k E ζ l q v :
    {{{ ▷ l ↦[n]{q} v }}}
      (mkExpr n (Load #l)) @ k; ζ; E
    {{{ RET (mkVal n v); l ↦[n]{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists; eapply LocalStepS; eauto; eapply LoadS; eauto. }
    iIntros (v2 σ2 efs Hstep).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    rewrite insert_id //. rewrite insert_id //= in Htrig.
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    destruct σ; iFrame. iModIntro. iExists (trace_last atr), ().
    rewrite -message_history_evolution_id Htrig; iFrame.
    iSplit; [done|].
    iSplit; [iPureIntro; apply user_model_evolution_id|].
    iApply "HΦ"; done.
  Qed.

  Lemma wp_store n k E ζ l v1 v2 :
    {{{ ▷ l ↦[n] v1 }}}
      (mkExpr n (Store #l (Val v2))) @ k; ζ; E
    {{{ RET (mkVal n #()); l ↦[n] v2 }}}.
  Proof. 
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit. { iPureIntro; do 3 eexists. eapply LocalStepS; eauto. econstructor. eauto. }
    iIntros (? ? ? ?).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    iMod (aneris_state_interp_heap_update with "[$Hσ $Hl]") as "[Hσ Hl]";
      [done|].
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro. iExists (trace_last atr), ().
    rewrite -message_history_evolution_id Htrig; iFrame.
    iSplit; first done.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply "HΦ"; done.
  Qed.

  Lemma wp_cas_fail n k E ζ l q v v1 v2 :
    v ≠ v1 →
    {{{ ▷ l ↦[n]{q} v }}}
      (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; ζ; E
    {{{ RET (mkVal n #false); l ↦[n]{q} v }}}.
  Proof.
    iIntros (Heq Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists. eapply LocalStepS; eauto. by econstructor. }
    iIntros (? ? ? ?).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
     inv_head_step. iNext.
    rewrite insert_id //. rewrite insert_id // in Htrig.
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    destruct σ; iFrame. iModIntro.
    iExists (trace_last atr), ().
    rewrite -message_history_evolution_id Htrig; iFrame.
    iSplit; first done.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply "HΦ"; done.
  Qed.

  Lemma wp_cas_suc n k E l v1 v2 :
    {{{ ▷ l ↦[n] v1 }}}
      (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; E
    {{{ RET (mkVal n #true); l ↦[n] v2 }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 3 eexists. eapply LocalStepS; eauto. by econstructor. }
    iIntros (? ? ? ?).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    iMod (aneris_state_interp_heap_update with "[$Hσ $Hl]") as "[Hσ Hl]";
      [done|].
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro. iExists (trace_last atr), ().
    rewrite -message_history_evolution_id Htrig; iFrame.
    iSplit; first done.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply "HΦ"; done.
  Qed.

  Lemma wp_rand n k E (u : Z) :
    {{{ ▷ is_node n ∗ ⌜(0 < u)⌝%Z }}}
      (mkExpr n (Rand #u)) @ k; E
    {{{ (r : Z), RET (mkVal n #r); ⌜(r >= 0) ∧ (r < u)⌝%Z }}}.
  Proof.
    iIntros (Φ) "(> #Hin & %Hm) HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & %Hve & Hsteps) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (is_node_heap_valid with "Hσ Hin") as (h) "%Hlookup". simpl in Hlookup.
    iSplit.
    { iPureIntro; do 3 eexists. eapply LocalStepS; eauto.
      eapply (RandS _ 0 h); lia. }
    iIntros (? ? ? ?).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig; eauto.
    inv_head_step. iNext.
    iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
    iModIntro. iExists (trace_last atr), ().
    iSplit; [done|].
    (* iSplit; [ iPureIntro; apply user_model_evolution_id |]. *)
    rewrite -message_history_evolution_id; iFrame.
    (* iSplit; first done. *)
    rewrite Htrig.
    assert (<[n := h']> (state_heaps σ) = (state_heaps σ)) as ->.
    { apply insert_id; done. }
    iFrame. iSplitR "HΦ". iPureIntro; apply user_model_evolution_id.
    iApply "HΦ"; done.
  Qed.

  Lemma wp_start ip k E ζ e Φ :
    ▷ is_node "system" ∗
    ▷ free_ip ip ∗
    ▷ Φ (mkVal "system" #()) ∗
    ▷ (∀ tid, is_node ip -∗ WP (mkExpr ip e) @ k; (ip, tid); ⊤ {{ _, True }})
    ⊢ WP mkExpr "system" (Start (LitString ip) e) @ k; ζ; E {{ Φ }}.
  Proof.
    iIntros "(>Hnode & >Hfip & HΦ & Hwp)".
    iApply (wp_lift_head_step with "[-]"); first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(Hevs & Hσ & Hm & % & Hauth) /=".
    iDestruct (is_node_heap_valid with "Hσ Hnode") as %[h Hsome].
    iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip") as %[Hnone _].
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
      first set_solver; auto.
    iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip")
      as "(% & %)".
    iModIntro; iSplit.
    { iPureIntro. do 3 eexists. apply AssignNewIpStepS; eauto. set_solver. }
    iNext. iIntros (e2 σ2 efs Hstep). iMod "Hmk" as "_".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step.
    iMod (aneris_state_interp_alloc_node with "[$]") as "(%Hcoh & Hn & Hσ)".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro.
    simplify_eq /=.
    iExists (trace_last atr), ().
    rewrite -message_history_evolution_new_ip; last done.
    rewrite Htrig; iFrame.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iSplitL "HΦ"; [by iApply wp_value|].
    iSplitL; [ by iApply ("Hwp" with "[$]")|done].
  Qed. 

  Lemma wp_new_socket ip s E ζ :
    {{{ ▷ is_node ip }}}
      (mkExpr ip (NewSocket #())) @ s; ζ; E
    {{{ sh, RET (mkVal ip (LitV (LitSocket sh)));
        sh ↪[ip] (mkSocket None true) }}}.
  Proof.
    iIntros (Φ) ">Hn HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (is_node_valid_sockets with "Hσ Hn") as (?) "%".
    iSplitR.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      apply newsocket_fresh. }
    set (sock := {| saddress := None;
                    sblock := true |}).
    iIntros (????).
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step. iNext.
    iMod (aneris_state_interp_alloc_socket sock with "Hn Hσ")
      as "[Hσ Hsh]"; try done.
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro.
    iExists (trace_last atr), ().
    rewrite -message_history_evolution_new_socket; [|done|done].
    iSplitR; first done.
    rewrite Htrig; iFrame.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply "HΦ"; done.
  Qed.

  Lemma wp_socketbind_groups
        E ζ sh skt k sa :
    saddress skt = None →
    {{{ ▷ unbound {[sa]} ∗
        ▷ sh ↪[ip_of_address sa] skt }}}
      (mkExpr (ip_of_address sa)
              (SocketBind (Val $ LitV $ LitSocket sh)
                          (Val $ LitV $ LitSocketAddress sa))) @ k; ζ; E
   {{{ RET (mkVal (ip_of_address sa) #0);
       sh ↪[ip_of_address sa] (skt<| saddress := Some sa |>) }}}.
  Proof.
    iIntros (? Φ) "(>Hp & >Hsh) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale)
            "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]". 
    iDestruct (aneris_state_interp_unbound_valid with "Hσ Hp") as "%HP".
    apply HSn.     
    iSplit.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step.
    iMod (aneris_state_interp_socketbind with "Hσ Hsh Hp")
      as "(Hσ & Hsh)"; [set_solver..|].
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro.
    iExists (trace_last atr), ().
    rewrite -message_history_evolution_socketbind; [|done|done].
    iSplitR; [done|].
    rewrite Htrig; iFrame.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_socketbind A E ζ sh skt k a :
    saddress skt = None →
    {{{ ▷ unbound {[a]} ∗
        ▷ sh ↪[ip_of_address a] skt }}}
      (mkExpr (ip_of_address a)
              (SocketBind (Val $ LitV $ LitSocket sh)
                          (Val $ LitV $ LitSocketAddress a))) @ k; ζ; E
   {{{ RET (mkVal (ip_of_address a) #0);
       sh ↪[ip_of_address a] (skt<| saddress := Some a |>) }}}.
  Proof.
    iIntros (? Φ) "(>Hp & >Hsh) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale)
            "(Hevs & Hσ & Hm & % & Hauth) !> /=".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iDestruct (aneris_state_interp_unbound_valid with "Hσ Hp") as "%HP".
    apply HSn.   
    iSplit.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step.
    iMod (aneris_state_interp_socketbind with "Hσ Hsh Hp")
      as "(Hσ & Hsh)"; [set_solver..|].
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iModIntro.
    iExists (trace_last atr), ().
    rewrite -message_history_evolution_socketbind; [|done|done].
    iSplitR; [done|].
    rewrite Htrig; iFrame.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply ("HΦ"). iFrame.
  Qed.

  Lemma wp_send_gen_groups φ mbody (is_dup : bool) sh skt saT sagT saR sagR strck rtrck evs k E ζ R T
        (Ψ1 Ψ2 : state → iProp Σ) :
    let msg := mkMessage saT saR mbody  in
    saddress skt = Some saT ->
    {{{ ▷ saT ∈g sagT ∗
        ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip_of_address saT] skt ∗
        ▷ sagT ⤳*[strck, rtrck] (R, T) ∗
        (if is_dup then ⌜set_Exists (λ m, m ≡g{sagT, sagR} msg) T⌝
         else (∃ m', ⌜msg ≡g{sagT,sagR} m'⌝ ∗ ▷ sagR ⤇* φ ∗ (▷ φ m'))) ∗
        if strck then
          ▷ sendon_evs_groups sagT evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
          ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                              aneris_state_interp σ δ ∗ Ψ2 σ)
        else True }}}
      (mkExpr (ip_of_address saT)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #saR)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address saT) #(String.length mbody));
        sh ↪[ip_of_address saT] skt ∗
        sagT ⤳*[strck, rtrck] (R, {[ msg ]} ∪ T) ∗
        if strck then
          ∃ st skts r,
            ⌜valid_sendonObs saT st sh skts skt r⌝ ∗
            sendon_evs_groups sagT  (evs ++ [sendonObs saT st sh mbody saR skt]) ∗
            Ψ1 st ∗ Ψ2 (sendonObs saT st sh mbody saR skt).(post_state) else True }}}.
  Proof.
    iIntros (msg Hskt Φ) "(>#HinT & >#HinR & >Hsh & >Hrt & Hmsg & Htrck) HΦ".
    iDestruct (elem_of_group_unfold with "HinT") as "[%HinT #HsagT]".
    iDestruct (elem_of_group_unfold with "HinT") as "[%HinR #HsagR]".
    iAssert (▷ if is_dup then ⌜set_Exists (λ m, m ≡g{sagT, sagR} msg) T⌝
               else (∃ m', ⌜msg ≡g{sagT,sagR} m'⌝ ∗ sagR ⤇* φ ∗ φ m'))%I with "[Hmsg]" as "Hmsg".
    { destruct is_dup; iNext; done. }
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iSplitR.
    { iPureIntro; do 3 eexists. eapply SocketStepS; eauto.
        by econstructor; naive_solver. }
    iAssert (|={E}=>
             aneris_state_interp σ (trace_messages_history ex) ∗
             ▷ if strck then
               sendon_evs_groups sagT evs ∗
               Ψ1 σ ∗
               (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                                 aneris_state_interp σ δ ∗ Ψ2 σ)
             else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
    { destruct strck; last by iFrame.
      iDestruct "Htrck" as "($&H&$)".
      iMod ("H" with "Hσ") as "[$ $]"; done. }
    iModIntro.
    iIntros (v2' ? ? Hstep).
    pose proof (λ a b c d f g h i j k,
                aneris_events_state_interp_send_untracked sagT b c d f g h _ i _ _ _ _ (Some ζ) j k Hstep)
      as Huntracked.
    pose proof (λ a b c d f g h i,
                aneris_events_state_interp_send_triggered sagT b c d f _ g _ _ _ _ (Some ζ) h i Hstep)
      as Htriggered.
    inv_head_step; iNext.
    rewrite (insert_id (state_sockets σ)); last done.
    rewrite (insert_id (state_sockets σ)) in Huntracked; last done.
    rewrite (insert_id (state_sockets σ)) in Htriggered; last done.
    destruct is_dup; last first.
    - iDestruct "Hmsg" as (m' Hmeq) "Hmsg".
      iDestruct "Hmsg" as "[#Hφ Hmsg]".
      iMod (aneris_state_interp_send sh saT sagT _ _ _ _ skt
            with "[$HinT] [$HinR] [$Hsh] [$Hrt] [$Hφ] [$Hmsg] [$Hσ]")
        as "(%Hmhe & Hσ & Hsh & Hrt)"; [set_solver..| done | ].
      iAssert (|={E}=>
             aneris_state_interp _ _ ∗
             if strck then
               sendon_evs_groups sagT _ ∗ Ψ1 σ ∗ Ψ2 _
             else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
      { destruct strck; last by iFrame "Hσ".
        iDestruct "Htrck" as "($&$&H)".
        iMod ("H" with "Hσ") as "[$ $]"; done. }
      rewrite - /msg.
      iExists (trace_last atr), ().
      destruct strck; last first.
      { iModIntro.
        rewrite -Hmhe.
        iFrame.
        iSplitR; [done|].
        iDestruct (Huntracked with "Hrt Hevs") as "[$ Hrt]";
          [done..|set_solver|].
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        iApply ("HΦ" with "[$]"); done. }
      iDestruct "Htrck" as "(Hevs' & ? & ?)".
      iMod (Htriggered with "Hevs' Hevs") as "[Hevs' Hevs]";
        [done..|set_solver|].
      iModIntro.
      rewrite -Hmhe.
      iFrame.
      iSplitR; [done|].
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      iApply "HΦ"; iFrame "Hrt Hsh"; eauto with iFrame.
    - iDestruct "Hmsg" as %?.
      iMod (aneris_state_interp_send_duplicate with
                "[$HinT] [$HinR] [$Hsh] [$Hrt] [$Hσ]")
        as "(%Hmhe & Hσ & Hsh & Hrt)"; [set_solver..|].
      iAssert (|={E}=>
             aneris_state_interp _ _ ∗
             if strck then
               sendon_evs_groups sagT _ ∗ Ψ1 σ ∗ Ψ2 _
             else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
      { destruct strck; last by iFrame "Hσ".
        iDestruct "Htrck" as "($&$&H)".
        iMod ("H" with "Hσ") as "[$ $]"; done. }
      rewrite - /msg.
      iExists (trace_last atr), ().
      destruct strck; last first.
      { iModIntro.
        rewrite /= -Hmhe.
        destruct (trace_messages_history ex).
        iFrame.
        iSplitR; [done|].
        iDestruct (Huntracked with "Hrt Hevs") as "[$ Hrt]";
          [done..|set_solver|].
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        iApply ("HΦ" with "[$]"); done. }
      iDestruct "Htrck" as "(Hevs' & ? & ?)".
      iMod (Htriggered with "Hevs' Hevs") as "[Hevs' Hevs]";
        [done..|set_solver|].
      iModIntro.
      rewrite /= -Hmhe.
      destruct (trace_messages_history ex).
      iFrame.
      iSplitR; [done|].
      iSplit; [ iPureIntro; apply user_model_evolution_id |].
      iApply "HΦ"; iFrame "Hrt Hsh"; eauto with iFrame.
  Qed.

  Lemma wp_send_gen φ mbody (is_dup : bool) sh skt a strck rtrck evs to k E
        ζ R T
    (Ψ1 Ψ2 : state → iProp Σ):
    let msg := mkMessage a to mbody in
    saddress skt = Some a ->
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, rtrck] (R, T) ∗
        ▷ to ⤇ φ ∗
        (if is_dup then ⌜msg ∈ T⌝ else ▷ φ msg) ∗
        if strck then
          ▷ sendon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
          ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                              aneris_state_interp σ δ ∗ Ψ2 σ)
        else True
    }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[strck, rtrck] (R, {[ msg ]} ∪ T) ∗
        if strck then
          ∃ st skts r,
            ⌜valid_sendonObs a st sh skts skt r⌝ ∗
            sendon_evs a (evs ++ [sendonObs a st sh mbody to skt]) ∗
            Ψ1 st ∗ Ψ2 (sendonObs a st sh mbody to skt).(post_state) else True }}}.
  Proof.
    iIntros (msg Hskt Φ) "(Hskt & Hrt & #Hφ & Hmsg & Htrck) HΦ".
    iAssert (▷ socket_address_group_own {[a]})%I as "#Ha".
    { iDestruct "Hrt" as "[(%send & %recv & _ & _ & _ & $ & _) _]". }
    iAssert (if is_dup then ⌜set_Exists (λ m, m ≡g{{[a]}, {[to]}} msg) T⌝ else (∃ m', ⌜msg ≡g{{[a]},{[to]}} m'⌝ ∗ ▷ {[to]} ⤇* (from_singleton φ) ∗
      (▷ (from_singleton φ) m')) )%I with "[Hmsg]"
      as "Hmsg".
    { destruct is_dup.
      - iDestruct "Hmsg" as %Hmsg. iPureIntro.
        exists msg. split; [done|]. apply message_group_equiv_refl; set_solver.
      - iExists msg.
        iSplit; [| iFrame "#∗" ].
        iPureIntro. apply message_group_equiv_refl; set_solver. }
    iAssert (▷ socket_address_group_own {[to]})%I as "#Hto".
    { iNext. by iDestruct "Hφ" as (γ) "[H _]". }
    iDestruct "Hrt" as "[Hrt Hown]".
    iApply (wp_send_gen_groups (from_singleton φ) _ is_dup _ _ _ _ _ {[to]}
              with "[$Hskt $Hrt $Hmsg $Htrck]"); [set_solver..| | ].
    { iSplit; iSplit;
        [ iPureIntro; set_solver | eauto | iPureIntro; set_solver | eauto ]. }
    iIntros "!> (Hskt & Hrt & Htrck)". iApply "HΦ".
    iFrame.
  Qed.

  Lemma wp_send_groups φ mbody sh skt saT sagT saR sagR rtrck k E ζ R T m' :
    let msg := mkMessage saT saR mbody in
    saddress skt = Some saT ->
    msg ≡g{sagT,sagR} m' →
    {{{ ▷ saT ∈g sagT ∗
        ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip_of_address saT] skt ∗
        ▷ sagT ⤳*[false, rtrck] (R, T) ∗
        ▷ sagR ⤇* φ ∗
        ▷ φ m' }}}
      (mkExpr (ip_of_address saT)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #saR)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address saT) #(String.length mbody));
        sh ↪[ip_of_address saT] skt ∗
        sagT ⤳*[false, rtrck] (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (msg Hskt Hmeq Φ) "(>HsagT & >HsagR & >Hsh & >Hrt & #Hφ & Hmsg) HΦ".
    iApply (wp_send_gen_groups _ _ false _ _ _ _ _ _ false _ inhabitant _ _ ζ _ _ (λ _, True) (λ _, True)
              with "[-HΦ]")%I; [set_solver..| iFrame "#"; eauto with iFrame | ].
    iNext. iIntros "(?&?&_)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send φ mbody sh skt a to rtrck k E ζ R T:
    let msg := mkMessage a to mbody  in
    saddress skt = Some a ->
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[false, rtrck] (R, T) ∗
        ▷ to ⤇ φ ∗
        ▷ φ msg }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[false, rtrck] (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (msg Hskt Φ) "(>Hsh & >Hrt & #Hφ & Hmsg) HΦ".
    iApply (wp_send_gen _ _ false _ _ _ false _ inhabitant _ _ _ ζ _ _ (λ _, True) (λ _, True)
              with "[-HΦ]")%I; first done.
    - iFrame; eauto.
    - iNext. iIntros "(?&?&_)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_duplicate_groups mbody sh skt saT sagT saR sagR rtrck k E ζ R T φ :
    let msg := mkMessage saT saR mbody in
    saddress skt = Some saT ->
    set_Exists (λ m, m ≡g{sagT,sagR} msg) T →
    {{{ ▷ saT ∈g sagT ∗
        ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip_of_address saT] skt ∗
        ▷ sagT ⤳*[false, rtrck] (R, T) ∗
        ▷ sagR ⤇* φ }}}
      (mkExpr (ip_of_address saT)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #saR)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address saT) #(String.length mbody));
        sh ↪[ip_of_address saT] skt ∗
        sagT ⤳*[false, rtrck] (R, {[msg]} ∪ T) }}}.
  Proof.
    iIntros (msg Hskt Hmsg Φ) "(>HsagT & >HsagR & >Hsh & >Hrt & HΨ) HΦ".
    iApply (wp_send_gen_groups φ _ true _ _ _ _ _ _ false _ inhabitant _ _ ζ _ _ (λ _, True) (λ _, True) with "[-HΦ]")%I; [try set_solver..| by iFrame | ].
    iNext. iIntros "(?&?&_)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_duplicate mbody sh skt a to rtrck k E ζ R T φ :
    let msg := mkMessage a to mbody in
    saddress skt = Some a ->
    msg ∈ T →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[false, rtrck] (R, T) ∗
        ▷ to ⤇ φ }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[false, rtrck] (R, T) }}}.
  Proof.
    iIntros (msg Hskt Hmsg Φ) "(>Hsh & >Hrt & #Hφ) HΦ".
    iApply (wp_send_gen φ _ true _ _ _ false _ inhabitant _ _ _ ζ _ _ (λ _, True) (λ _, True)
              with "[-HΦ]")%I; first done.
    - iFrame "#∗"; eauto.
    - rewrite subseteq_union_1_L; last set_solver.
      iNext. iIntros "(?&?&_)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_tracked_groups φ mbody sh skt saT sagT saR sagR rtrck evs k E ζ R T
        (Ψ1 Ψ2 : state → iProp Σ) m' :
    let msg := mkMessage saT saR mbody  in
    msg ≡g{sagT,sagR} m' →
    saddress skt = Some saT ->
    {{{ ▷ saT ∈g sagT ∗
        ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip_of_address saT] skt ∗
        ▷ sagT ⤳*[true, rtrck] (R, T) ∗
        ▷ sagR ⤇* φ ∗
        ▷ φ m' ∗
        ▷ sendon_evs_groups sagT evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ)
    }}}
      (mkExpr (ip_of_address saT)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #saR)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address saT) #(String.length mbody));
        sh ↪[ip_of_address saT] skt ∗
        sagT ⤳*[true, rtrck] (R, {[ msg ]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs saT st sh skts skt r⌝ ∗
          sendon_evs_groups sagT (evs ++ [sendonObs saT st sh mbody saR skt]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs saT st sh mbody saR skt).(post_state) }}}.
  Proof.
    iIntros (msg Hmeq Hskt Φ) "(>HsagT & >HsagR & >Hsh & >Hrt & #Hφ & Hmsg & Hevs) HΦ".
    iApply (wp_send_gen_groups _ _ false _ _ _ _ _ _ true _ _ _ _ ζ _ _ Ψ1 Ψ2
              with "[$HsagT $HsagR $Hsh $Hrt Hmsg $Hevs]")%I;
      [set_solver..| eauto with iFrame |].
    iNext. iIntros "(?&?&?)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_tracked φ mbody sh skt a rtrck evs to k E ζ R T
    (Ψ1 Ψ2 : state → iProp Σ) :
    let msg := mkMessage a to mbody  in
    saddress skt = Some a ->
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[true, rtrck] (R, T) ∗
        ▷ to ⤇ φ ∗
        ▷ φ msg ∗
        ▷ sendon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ)
    }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[true, rtrck] (R, {[ msg ]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs a st sh skts skt r⌝ ∗
          sendon_evs a (evs ++ [sendonObs a st sh mbody to skt]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs a st sh mbody to skt).(post_state) }}}.
  Proof.
    iIntros (msg Hskt Φ) "(>Hsh & >Hrt & #Hφ & Hmsg & Hevs) HΦ".
    iApply (wp_send_gen _ _ false _ _ _ true _ _ _ _ _ ζ _ _ Ψ1 Ψ2
              with "[-HΦ]")%I; first done.
    - iFrame; eauto.
    - iNext. iIntros "(?&?&?)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_duplicate_tracked_groups mbody sh skt saT sagT saR sagR rtrck evs
        k E ζ R T (Ψ1 Ψ2 : state → iProp Σ) φ :
    let msg := mkMessage saT saR mbody  in
    saddress skt = Some saT ->
    set_Exists (λ m, m ≡g{sagT,sagR} msg) T →
    {{{ ▷ saT ∈g sagT  ∗
        ▷ saR ∈g sagR  ∗
        ▷ sh ↪[ip_of_address saT] skt ∗
        ▷ sagT ⤳*[true, rtrck] (R, T) ∗
        ▷ sagR ⤇* φ ∗
        ▷ sendon_evs_groups sagT evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (mkExpr (ip_of_address saT)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #saR)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address saT) #(String.length mbody));
        sh ↪[ip_of_address saT] skt ∗
        sagT ⤳*[true, rtrck] (R, {[msg]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs saT st sh skts skt r⌝ ∗
          sendon_evs_groups sagT (evs ++ [sendonObs saT st sh mbody saR skt]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs saT st sh mbody saR skt).(post_state) }}}.
  Proof.
    iIntros (msg Hskt Hmsg Φ) "(>HsagT & >HsagR & >Hsh & >Hrt & Hφ & Hevs) HΦ".
    iApply (wp_send_gen_groups φ _ true _ _ _ _ _ sagR true _ _ _ _ ζ _ _ Ψ1 Ψ2
              with "[-HΦ]")%I; [set_solver..| by eauto with iFrame |].
    iNext. iIntros "(?&?&?)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_send_duplicate_tracked mbody sh skt a rtrck evs to k E ζ R T φ
        (Ψ1 Ψ2 : state → iProp Σ) :
    let msg := mkMessage a to mbody  in
    saddress skt = Some a ->
    msg ∈ T →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[true, rtrck] (R, T) ∗
        ▷ to ⤇ φ ∗
        ▷ sendon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; ζ; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳[true, rtrck] (R, T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs a st sh skts skt r⌝ ∗
          sendon_evs a (evs ++ [sendonObs a st sh mbody to skt]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs a st sh mbody to skt).(post_state) }}}.
  Proof.
    iIntros (msg Hskt Hmsg Φ) "(>Hsh & >Hrt & Hφ & Hevs) HΦ".
    iApply (wp_send_gen φ _ true _ _ _ true _ _ _ _ _ ζ _ _ Ψ1 Ψ2
              with "[-HΦ]")%I; first done.
    - iFrame; eauto.
    - rewrite subseteq_union_1_L; last set_solver.
      iNext. iIntros "(?&?&?)". iApply "HΦ"; iFrame.
  Qed.

  Lemma wp_receivefrom_gen_groups'
        (Ψo : option (socket_interp Σ)) k saR sagR strck rtrck E sh skt ζ R T evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    saddress skt = Some saR →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip_of_address saR] skt ∗
        ▷ sagR ⤳*[strck, rtrck] (R, T) ∗
        match Ψo with Some Ψ => sagR ⤇* Ψ | _ => True end ∗
        if rtrck then
          ▷ receiveon_evs_groups sagR evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
          ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                              aneris_state_interp σ δ ∗ Ψ2 σ)
        else True }}}
      (mkExpr (ip_of_address saR)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address saR) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address saR] skt ∗ sagR ⤳*[strck, rtrck] (R, T) ∗ ⌜sblock skt = false⌝) ∨
         (∃ msg sagT,
            ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                              (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
            ⌜m_destination msg = saR⌝ ∗
            m_sender msg ∈g sagT ∗
            sh ↪[ip_of_address saR] skt ∗
            sagR ⤳*[strck, rtrck] ({[msg]} ∪ R, T) ∗
            ((⌜set_Forall (λ m', ¬ msg ≡g{sagT, sagR} m') R⌝ ∗
               ∃ msg', ⌜msg ≡g{sagT, sagR} msg'⌝ ∗
                        match Ψo with
                          Some Ψ => Ψ msg'
                        | _ => ∃ φ, sagR ⤇* φ ∗ φ msg' end) ∨
           ⌜set_Exists (λ m', msg ≡g{sagT, sagR} m') R⌝) ∗
          if rtrck then
          ∃ st skts r,
            ⌜valid_receiveonObs saR st sh msg skts skt r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st sh msg skts skt r).(post_state) else True))
    }}}.
  Proof.
    iIntros (Hskt Φ) "(>#HinR & >Hsh & >Hrt & #HΨ & Htrck) HΦ /=".
    iDestruct (elem_of_group_unfold with "HinR") as "[%HsagR _]".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(Hevs & Hσ & Hm & % & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    destruct (decide (r = [])) as [-> | Hneq].
    - iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro.
        destruct (sblock skt) eqn:?.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ b c d f g h, aneris_events_state_interp_no_triggered' b c d _ f _ _ _ _ (Some ζ) g h Hstep)
        as Hnotriggered.
      inv_head_step; [| |].
      + assert (length (r ++ [m]) = length ([] : list message)) as Hdone; first by f_equal.
        rewrite app_length /= in Hdone. lia.
      + rewrite (insert_id (state_sockets σ)); last done.
        rewrite (insert_id (state_sockets σ)) in Hnotriggered; last done.
        iNext.
        iMod "Hmk".
        iModIntro.
        iExists (trace_last atr), ().
        rewrite -message_history_evolution_id; iFrame.
        rewrite Hnotriggered;
           [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
             by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) | by intros ? (?&?&?&?&?&?&?&?&?)].
        iFrame.
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        iApply wp_value.
        iApply "HΦ". iLeft. eauto with iFrame.
      + rewrite (insert_id (state_sockets σ)); last done.
        rewrite (insert_id (state_sockets σ)) in Hnotriggered; last done.
        iNext. iMod "Hmk".
        iModIntro.
        iExists (trace_last atr), ().
        rewrite -message_history_evolution_id; iFrame.
        rewrite Hnotriggered;
          [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
             by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) | by intros ? (?&?&?&?&?&?&?&?&?)].
        iFrame.
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        iApply ("IH" with "[$] [$] [$] [$]").
    - iClear "IH".
      iAssert (|={E}=>
               aneris_state_interp σ (trace_messages_history ex) ∗
               ▷ if rtrck then
                   receiveon_evs_groups sagR evs ∗
                   Ψ1 σ ∗
                   (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                                     aneris_state_interp σ δ ∗ Ψ2 σ)
                 else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
      { destruct rtrck; last by iFrame.
        iDestruct "Htrck" as "($&H&$)".
        iMod ("H" with "Hσ") as "[$ $]"; done. }
      iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro. apply last_is_Some in Hneq as [m Hneq].
        apply last_Some in Hneq as [? ->].
        destruct (sblock skt) eqn:?.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ a b c d f g h i j k,
                  aneris_events_state_interp_receive_untracked sagR b c d f g h _ i _ _ _ _ (Some ζ) j k Hstep)
        as Huntracked.
      pose proof (λ a b c d f g h i,
                  aneris_events_state_interp_receive_triggered sagR b c d f _ g _ _ _ _ (Some ζ) h i Hstep)
        as Htriggered.
      inv_head_step.
      iPoseProof (aneris_state_interp_receive_some saR sagR _ _ _ _
                      with "HinR [HΨ//] [$Hσ] [$Hsh] [$Hrt]")
          as (R' sagT) "(HinT & #HownT & %Hhist & %HR & Hrt & Hrest)"; [try set_solver..|].
      destruct (set_Forall_Exists_message_group_equiv_dec sagT sagR m R)
        as [Hdec | Hdec]; last first.
      + destruct Hdec as [m' [Hmin' Hm']].
        iNext.
        iMod "Hmk".
        iDestruct "Hrt" as "[ (%Hm & Hrt) | %Hm ]".
        { specialize (Hm m' Hmin').
          done. }
        iMod "Hrest" as "(Hσ & Hsh & Ha)".
        destruct rtrck.
        * iDestruct "Htrck" as "(Hrevs&HΨ1&HΨ2)".
          iMod ("HΨ2" with "Hσ") as "[Hσ HΨ2]".
          iMod (Htriggered with "Hrevs Hevs") as "[Hevs Hrevs]";
            [set_solver..|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m, sagT.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          subst.
          iFrame.
          iSplitR.
          { by iRight. }
          eauto with iFrame.
        * iDestruct (Huntracked with "Ha Hevs") as "[Hevs Ha]";
            [done..|set_solver|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m, sagT.
          iSplit; first done.
          iSplit; first done.
          iSplit; first done.
          subst.
          iFrame.
          by iRight.
      + iDestruct "Hrt" as "[ (%Hm & (%m' & %Hmeq & Hrt)) | %Hm ]"; last first.
        { destruct Hm as [m' [Hmin Hmeq]].
          pose proof (Hdec m' Hmin).
          done. }
        iNext.
        iMod "Hrest" as "(Hσ & Hsh & Ha)".
        iMod "Hmk".
        destruct rtrck.
        * iDestruct "Htrck" as "(Hrevs&HΨ1&HΨ2)".
          iMod ("HΨ2" with "Hσ") as "[Hσ HΨ2]".
          iMod (Htriggered with "Hrevs Hevs") as "[Hevs Hrevs]";
            [done..|set_solver|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ".
          iRight.
          iExists m, sagT.
          iSplit; [done|].
          iSplit; [done|].
          iSplit; [done|].
          subst. iFrame.
          iSplitL "Hrt".
          { iLeft. iSplit;[done|].
            iExists m'. by iFrame. }
          eauto with iFrame.
        * iDestruct (Huntracked with "Ha Hevs") as "[Hevs Ha]";
            [done..|set_solver|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m, sagT.
          iSplit; [done|].
          iSplit; [done|].
          iSplit; [done|].
          subst. iFrame.
          iLeft. iSplit;[done|].
          iExists m'. by iFrame.
  Qed.

  Lemma wp_receivefrom_gen'
          (Ψ : socket_interp Σ) k a strck rtrck E ζ sh skt R T evs
          (Ψ1 Ψ2 : state → iProp Σ):
    saddress skt = Some a →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, rtrck] (R, T) ∗
        a ⤇ Ψ ∗
        if rtrck then
          ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
          ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                              aneris_state_interp σ δ ∗ Ψ2 σ)
          else True }}}
      (mkExpr (ip_of_address a)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address a) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address a] skt ∗
          a ⤳[strck, rtrck] (R, T) ∗ ⌜sblock skt = false⌝) ∨
         (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip_of_address a] skt ∗
            a ⤳[strck, rtrck] ({[ msg ]} ∪ R, T) ∗ Ψ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, rtrck] (R, T)) ∗
          if rtrck then
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state) else True))
    }}}.
  Proof.
    iIntros (Hskt Φ) "(>Hsh & >Hrt & #HΨ & Htrck) HΦ /=".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(Hevs & Hσ & Hm & % & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    destruct (decide (r = [])) as [-> | Hneq].
    -  iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro.
        destruct (sblock skt) eqn:?.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ b c d f g h, aneris_events_state_interp_no_triggered' b c d _ f _ _ _ _ (Some ζ) g h Hstep)
        as Hnotriggered.
      inv_head_step; [| |].
      + assert (length (r ++ [m]) = length ([] : list message)) as Hdone; first by f_equal.
        rewrite app_length /= in Hdone. lia.
      + rewrite (insert_id (state_sockets σ)); last done.
        rewrite (insert_id (state_sockets σ)) in Hnotriggered; last done.
        iNext.
        iMod "Hmk".
        iModIntro.
        iExists (trace_last atr), ().
        rewrite -message_history_evolution_id; iFrame.
        rewrite Hnotriggered;
           [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
             by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) | by intros ? (?&?&?&?&?&?&?&?&?)].
        iFrame.
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        iApply wp_value.
        iApply "HΦ". iLeft. eauto with iFrame.
      + rewrite (insert_id (state_sockets σ)); last done.
        rewrite (insert_id (state_sockets σ)) in Hnotriggered; last done.
        iNext. iMod "Hmk".
        iModIntro.
        iExists (trace_last atr), ().
        rewrite -message_history_evolution_id; iFrame.
        rewrite Hnotriggered;
          [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
             by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) | by intros ? (?&?&?&?&?&?&?&?&?)].
        iFrame.
        iSplit; [ iPureIntro; apply user_model_evolution_id |].
        iApply ("IH" with "[$] [$] [$] [$]").
    - iClear "IH".
      iAssert (|={E}=>
               aneris_state_interp σ (trace_messages_history ex) ∗
               ▷ if rtrck then
                   receiveon_evs a evs ∗
                   Ψ1 σ ∗
                   (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                                     aneris_state_interp σ δ ∗ Ψ2 σ)
                 else True)%I with "[Hσ Htrck]" as ">[Hσ Htrck]".
      { destruct rtrck; last by iFrame.
        iDestruct "Htrck" as "($&H&$)".
        iMod ("H" with "Hσ") as "[$ $]"; done. }
      iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro. apply last_is_Some in Hneq as [m Hneq].
        apply last_Some in Hneq as [? ->].
        destruct (sblock skt) eqn:?.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail.
        - do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2; fail. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ a b c d f g h i j k,
                  aneris_events_state_interp_receive_untracked {[a]} b c d f g h _ i _ _ _ _ (Some ζ) j k Hstep)
        as Huntracked.
      pose proof (λ a b c d f g h i,
                  aneris_events_state_interp_receive_triggered {[a]} b c d f _ g _ _ _ _ (Some ζ) h i Hstep)
        as Htriggered.
      inv_head_step.
      simpl.
      iDestruct "Hrt" as "[Hrt #Hown]".
      iDestruct (messages_mapsto_observed with "Hrt")
        as "[Hrt (%As & %Ar & _ & _ & #Hvalid & _)]".
      iPoseProof (aneris_state_interp_receive_some a {[a]} _ _ _ _
                                                   (Some (from_singleton Ψ))
                      with "[] [$HΨ] [$Hσ] [$Hsh] [$Hrt]")
        as (R' sagT) "(% & [%Hhst #Hin] & %Hhist & %HR & Hrt & Hrest)";
        [try set_solver..| | ].
      { iSplit; [ iPureIntro; try set_solver | iApply "Hvalid" ]. }
      destruct (decide (m ∈ R)) as [Hin | Hin].
      + iNext.
        iMod "Hmk".
        iDestruct "Hrt" as "[ (%Hm & Hrt) | % ]".
        { specialize (Hm m Hin).
          assert (false).
          { apply Hm. apply message_group_equiv_refl. set_solver. set_solver. }
          done. }
        assert (R = R') as <- by set_solver.
        iMod "Hrest" as "(Hσ & Hsh & Ha)".
        destruct rtrck.
        * iDestruct "Htrck" as "(Hrevs&HΨ1&HΨ2)".
          iMod ("HΨ2" with "Hσ") as "[Hσ HΨ2]".
          iMod (Htriggered with "Hrevs Hevs") as "[Hevs Hrevs]"; [done|done|set_solver|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh".
          { by iRight; iFrame; iFrame "#". }
          eauto with iFrame.
        * iDestruct (Huntracked with "Ha Hevs") as "[Hevs Ha]"; [done|done|set_solver|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh".
          { by iRight; iFrame; iFrame "#". }
          eauto with iFrame.
      + iDestruct "Hrt" as "[ (%Hm & (%m' & %Hmeq & Hrt)) | %Hm ]"; last first.
        { destruct Hm as [m' [Hmin Hmeq]].
          iAssert (⌜sagT = {[m_sender m']}⌝)%I as %->.
          {
            iDestruct (big_sepS_elem_of with "Hown") as "Hown_m"; [done|].
            destruct Hmeq as (Hm11 & Hm12 & _).
            iApply (socket_address_group_own_agree with "Hin Hown_m");
              set_solver.
          }
          assert (m = m').
          { destruct m, m'. rewrite /message_group_equiv in Hmeq.
            simpl in *.
            destruct Hmeq as (Hm11 & Hm12 & Hm21 & Hm22 & <-).
            (* destruct Hmeq as (<- & <- & <- & Hm1 & Hm2). *)
            assert (m_sender = m_sender0) as <- by set_solver.
            assert (m_destination = m_destination0) as <- by set_solver.
            done. }
          set_solver.
        }
        iAssert (▷ socket_address_group_own {[m_sender m']})%I as "#>Hown'".
        { iNext. iDestruct "Hrt" as "[$ Hrt]". }
        iAssert (⌜m_sender m = m_sender m'⌝)%I as %Hsender.
        {
          destruct Hmeq as (Hm11 & Hm12 & _).
          iDestruct (socket_address_group_own_agree with "Hin Hown'")
            as %->; [set_solver.. |].
          iPureIntro. set_solver. }
        assert (m = m') as <-.
        {
          destruct m. destruct m'. simpl in *.
          destruct Hmeq as (Hm11 & Hm12 & Hm21 & Hm22 & Hprot).
          repeat f_equiv; eauto. set_solver. }
        iNext.
        iMod "Hrest" as "(Hσ & Hsh & Ha)".
        iMod "Hmk".
        destruct rtrck.
        * iDestruct "Htrck" as "(Hrevs&HΨ1&HΨ2)".
          iMod ("HΨ2" with "Hσ") as "[Hσ HΨ2]".
          iMod (Htriggered with "Hrevs Hevs") as "[Hevs Hrevs]"; [done|done|set_solver|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ".
          iRight.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh Hrt".
          { subst. iLeft.
            iFrame "Ha". iFrame.
            iDestruct "Hrt" as "[_ $]". iSplit; [done|].
            iApply big_sepS_union; [set_solver|].
            iFrame "#". iApply big_sepS_singleton. eauto. }
          eauto with iFrame.
        * iDestruct (Huntracked with "Ha Hevs") as "[Hevs Ha]"; [done|done|set_solver|].
          iModIntro.
          iExists (trace_last atr), ().
          rewrite Hhist.
          iFrame.
          iSplit; [ iPureIntro; apply user_model_evolution_id |].
          iApply wp_value.
          iApply "HΦ". iRight; eauto.
          iExists m.
          iSplit; first done.
          iSplit; first done.
          iSplitL "Ha Hsh Hrt".
          { subst. iLeft.
            iFrame "Ha". iFrame.
            iDestruct "Hrt" as "[_ $]". iSplit; [done|].
            iApply big_sepS_union; [set_solver|].
            iFrame "#". iApply big_sepS_singleton. eauto. }
          eauto with iFrame.
  Qed.

  Lemma wp_receivefrom_nb_gen_groups
        (Ψo : option (socket_interp Σ)) k saR sagR strck E ζ sh skt R T :
    saddress skt = Some saR →
    sblock skt = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip_of_address saR] skt ∗
        ▷ sagR ⤳*[strck, false] (R, T) ∗
        match Ψo with Some Ψ => sagR ⤇* Ψ | _ => True end }}}
      (mkExpr (ip_of_address saR)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address saR) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address saR] skt ∗
          sagR ⤳*[strck, false] (R, T) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip_of_address saR] skt ∗
          sagR ⤳*[strck, false] ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT,sagR} m') R⌝ ∗
             ∃ msg', ⌜msg ≡g{sagT,sagR} msg'⌝ ∗
                     match Ψo with
                       Some Ψ => Ψ msg'
                     | _ => ∃ φ, sagR ⤇* φ ∗ φ msg' end) ∨
            ⌜set_Exists (λ m', msg ≡g{sagT,sagR} m') R⌝)))) }}}.
  Proof.
    iIntros (Hskt Hblk Φ) "(>HinR & >Hsh & >Hrt & #HΨ) HΦ /=".
    iApply (wp_receivefrom_gen_groups' Ψo _ _ _ _ false _ _ _ _ _ _ [] (λ _, True) (λ _, True)
              with "[$HinR $Hsh $Hrt $HΨ] [HΦ]")%I; [set_solver..|].
    iNext.
    iIntros (?) "[(?&?&?&?)|H]"; iApply "HΦ"; first by iLeft; iFrame.
    iRight.
    iDestruct "H" as (msg' sagT ? ?) "(HownT & $ & Hrt & [[H|H] _])";
      iExists msg', sagT; iFrame; done.
  Qed.

  Lemma wp_receivefrom_nb_gen
        (Ψ : socket_interp Σ) k a strck E ζ sh skt R T :
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, false] (R, T) ∗
        a ⤇ Ψ }}}
      (mkExpr (ip_of_address a)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address a) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address a] skt ∗
          a ⤳[strck, false] (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip_of_address a] skt ∗
            a ⤳[strck, false] ({[ msg ]} ∪ R, T) ∗ Ψ msg) ∨
            ⌜msg ∈ R⌝ ∗ sh ↪[ip_of_address a] skt ∗
            a ⤳[strck, false] (R, T))))) }}}.
  Proof.
    iIntros (Hskt Hblk Φ) "(>Hsh & >Hrt & #HΨ) HΦ /=".
    iApply (wp_receivefrom_gen' Ψ _ _ _ false _ _ _ _ _ _ [] (λ _, True) (λ _, True)
              with "[$Hsh $Hrt $HΨ] [HΦ]")%I; [done|].
    iNext.
    iIntros (?) "[(?&?&?&?)|H]"; iApply "HΦ"; first by iLeft; iFrame.
    iDestruct "H" as (? ? ?) "[[H|H] _]"; eauto 10.
  Qed.

  Lemma wp_receivefrom_nb_groups k saR sagR E ζ sh skt R T :
    let ip := ip_of_address saR in
    saddress skt = Some saR →
    sblock skt = false →
    {{{ ▷ saR ∈g sagR ∗ ▷ sh ↪[ip] skt ∗ ▷ sagR ⤳* (R, T) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ sagR ⤳* (R, T))) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip] skt ∗ sagR ⤳* ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT,sagR} m') R⌝ ∗
             ∃ msg', ⌜msg ≡g{sagT,sagR} msg'⌝ ∗ ∃ φ, sagR ⤇* φ ∗ φ msg') ∨
           ⌜set_Exists (λ m', msg ≡g{sagT,sagR} m') R⌝)) }}}.
  Proof.
    iIntros (? ? Hs Φ) "(HinR & Hsh & Hsa) HΦ".
    iApply (wp_receivefrom_nb_gen_groups None with "[$]"); [done..|].
    iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
  Qed.

  Lemma wp_receivefrom_nb k a E ζ sh skt R T φ :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T))) }}}.
  Proof.
     iIntros (? ? Hs Φ) "(Hsh & Hsa) HΦ".
     iApply (wp_receivefrom_nb_gen φ with "[$]"); [done|done|].
     iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
  Qed.

  Lemma wp_receivefrom_nb_alt_groups k saR sagR E ζ sh skt R T φ :
    let ip := ip_of_address saR in
    saddress skt = Some saR →
    sblock skt = false →
    {{{ ▷ saR ∈g sagR ∗ ▷ sh ↪[ip] skt ∗ ▷ sagR ⤳* (R, T) ∗ sagR ⤇* φ }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ sagR ⤳* (R, T))) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip] skt ∗ sagR ⤳* ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT, sagR} m') R⌝ ∗
             ∃ msg', ⌜msg ≡g{sagT, sagR} msg'⌝ ∗ φ msg') ∨
           ⌜set_Exists (λ m', msg ≡g{sagT,sagR} m') R⌝)) }}}.
  Proof.
    iIntros (? ? Hs Φ) "(HinR & Hsh & Hsa) HΦ".
    iApply (wp_receivefrom_nb_gen_groups (Some φ) with "[$]"); [done..|].
    iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
  Qed.

  (* TODO: Same as non-alt - Delete? *)
  Lemma wp_receivefrom_nb_alt k a E ζ sh skt R T φ :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
            ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T)) }}}.
  Proof.
    iIntros (? ? Hs Φ) "(Hsh & Hsa) HΦ".
    iApply (wp_receivefrom_nb_gen φ with "[$]"); [done|done|].
    iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
  Qed.

  Lemma wp_receivefrom_groups k saR sagR E ζ h s R T φ :
    let ip := ip_of_address saR in
    saddress s = Some saR →
    sblock s = true →
    {{{ ▷ saR ∈g sagR ∗ ▷ h ↪[ip] s ∗ ▷ sagR ⤳* (R, T) ∗ sagR ⤇* φ}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; ζ; E
    {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
        ∃ sagT,
          ⌜m_destination m = saR⌝ ∗
          m_sender m ∈g sagT ∗
          h ↪[ip] s ∗ sagR ⤳* ({[ m ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ m ≡g{sagT, sagR} m') R⌝ ∗
            ∃ msg', ⌜m ≡g{sagT, sagR} msg'⌝ ∗ sagR ⤇* φ ∗ φ msg') ∨
           ⌜set_Exists (λ m', m ≡g{sagT, sagR} m') R⌝) }}}.
  Proof.
    simpl; iIntros (Haddr Hblk Φ) "(HinR & Hsh & Ha & #Hsi) HΦ".
    iApply (wp_receivefrom_gen_groups' (Some φ) _ _ _ _ false _ _ _ _ _ _ [] (λ _, True) (λ _, True)
              with "[$HinR $Hsh $Ha $Hsi] [HΦ]")%I; [done..|].
    iNext.
    iIntros (?) "[(?&?&?&%)|H]"; first by destruct (sblock s).
    iDestruct "H" as (msg' sagT -> Hin) "H".
    iApply "HΦ".
    iExists sagT.
    iSplit;[done|].
    iDestruct "H" as "($ & $ & $ & [H _])".
    iDestruct "H" as "[(% & [%m' [%Hmeq H]])|H]";
      [iLeft; eauto with iFrame; eauto| iRight; eauto ].
  Qed.

  Lemma wp_receivefrom k a E ζ h s R T φ :
    let ip := ip_of_address a in
    saddress s = Some a →
    sblock s = true →
    {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; ζ; E
    {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
        ⌜m_destination m = a⌝ ∗
        ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
         ⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))
    }}}.
  Proof.
    simpl; iIntros (Haddr Hblk Φ) "(Hsh & Ha & #Hsi) HΦ".
    iApply (wp_receivefrom_gen' φ _ _ _ false _ _ _ _ _ _ [] (λ _, True) (λ _, True)
              with "[$Hsh $Ha $Hsi] [HΦ]")%I; [done|].
    iNext.
    iIntros (?) "[(?&?&?&%)|H]"; first by destruct (sblock s).
    iDestruct "H" as (msg' <- ->) "[H _]".
    iApply "HΦ".
    iSplit;[done|].
    iDestruct "H" as "[(% & $ & H & H')|(% & $ & H)]";
      [iLeft; iFrame; eauto| iRight; eauto ].
  Qed.

  Lemma wp_receivefrom_gen_groups k saR sagR E ζ h s R T φ :
    let ip := ip_of_address saR in
    saddress s = Some saR →
  {{{ ▷ saR ∈g sagR ∗ ▷ h ↪[ip] s ∗ ▷ sagR ⤳* (R, T) ∗ sagR ⤇* φ}}}
    (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; ζ; E
  {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ sagR ⤳* (R, T)) ∨
        ∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          h ↪[ip] s ∗ sagR ⤳* ({[ msg ]} ∪ R, T) ∗
         ((⌜set_Forall (λ m', ¬ msg ≡g{sagT,sagR} m') R⌝ ∗
             ∃ msg', ⌜msg ≡g{sagT,sagR} msg'⌝ ∗ φ msg') ∨
           ⌜set_Exists (λ m', msg ≡g{sagT,sagR} m') R⌝) }}}.
  Proof.
    simpl; iIntros (Haddr Φ) "(>#HinR & >Hsh & >Ha & #Hsi) HΦ".
    destruct (sblock s) eqn:Hblk.
    - iApply (wp_receivefrom_groups with "[$Hsh $Ha]"); eauto.
      iNext. iIntros (m) "Hm".
      iApply "HΦ". iRight.
      iDestruct "Hm" as (sagT) "Hm".
      iExists m, sagT.
      iDestruct "Hm" as (?) "($ & $ & $ & [(% & (%m' & Hmeq & _ & Hϕ)) | Hm])";
        (repeat iSplit; first done; eauto).
    - iApply (wp_receivefrom_nb_alt_groups with "[$Hsh $Ha]"); eauto.
  Qed.

  Lemma wp_receivefrom_gen k a E ζ h s R T φ :
    let ip := ip_of_address a in
    saddress s = Some a →
    {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) }}}.
  Proof.
    simpl; iIntros (Haddr Φ) "(>Hsh & >Ha & #Hsi) HΦ".
    destruct (sblock s) eqn:Hblk.
    - iApply (wp_receivefrom with "[$Hsh $Ha]"); eauto.
      iNext. iIntros (m) "Hm".
      iApply "HΦ". iRight. iExists m.
      iDestruct "Hm" as (?) "[(% & Hh & Ha & _ & Hϕ) | Hm]";
        (repeat iSplit; first done; eauto).
      iLeft. eauto with iFrame.
    - iApply (wp_receivefrom_nb_alt with "[$Hsh $Ha]"); eauto.
  Qed.

  Lemma wp_receivefrom_nb_gen_tracked_groups
          (Ψo : option (socket_interp Σ)) k saR sagR strck E ζ sh skt R T evs
          (Ψ1 Ψ2 : state → iProp Σ) :
    saddress skt = Some saR →
    sblock skt = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip_of_address saR] skt ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        ▷ receiveon_evs_groups sagR evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) ∗
        match Ψo with Some Ψ => sagR ⤇* Ψ | _ => True end }}}
      (mkExpr (ip_of_address saR)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address saR) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address saR] skt ∗ sagR ⤳*[strck, true] (R, T) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip_of_address saR] skt ∗
          sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT, sagR} m') R⌝ ∗
             ∃ msg', ⌜msg ≡g{sagT, sagR} msg'⌝ ∗
                      match Ψo with
                        Some Ψ => Ψ msg'
                      | _ => ∃ φ, sagR ⤇* φ ∗ φ msg' end) ∨
           ⌜set_Exists (λ m', msg ≡g{sagT, sagR} m') R⌝) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs saR st sh msg skts skt r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st sh msg skts skt r).(post_state)))) }}}.
  Proof.
    iIntros (Hskt Hblk Φ) "(>#HinR & >Hsh & >Hrt & Hevs & HΨ1 & HΨ2 & #HΨ) HΦ /=".
    iApply (wp_receivefrom_gen_groups' Ψo _ _ _ _ true with "[$HinR $Hsh $Hrt $Hevs $HΨ1 HΨ2 $HΨ //] [HΦ]")%I; [set_solver..|].
    iNext.
    iIntros (?) "[(?&?&?&?)|H]"; iApply "HΦ"; first by iLeft; iFrame.
    iRight.
    iDestruct "H" as (m sagT) "H".
    iExists m, sagT.
    iDestruct "H" as (? ?) "($ & Hrt & HΨ' & H)".
    iSplit; [done|]. iSplit; [done|]. iFrame.
  Qed.

  Lemma wp_receivefrom_nb_gen_tracked
          (Ψ : socket_interp Σ) k a strck E ζ sh skt R T evs
          (Ψ1 Ψ2 : state → iProp Σ) :
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ Ψ ∗
        ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (mkExpr (ip_of_address a)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal (ip_of_address a) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, true] (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip_of_address a] skt ∗
            a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ Ψ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state)))) }}}.
  Proof.
    iIntros (Hskt Hblk Φ) "(>Hsh & >Hrt & #HΨ & Hevs & HΨ1 & HΨ2) HΦ /=".
    iApply (wp_receivefrom_gen' Ψ _ _ _ true with "[$Hsh $Hrt $Hevs $HΨ1 HΨ2 $HΨ //] [HΦ]")%I;
      [done|].
    iNext.
    iIntros (?) "[(?&?&?&?)|H]"; iApply "HΦ"; first by iLeft; iFrame.
    iDestruct "H" as (? ? ?) "[H1 H2]".
    iDestruct "H1" as "[H1|H1]"; by iRight; iExists _; iFrame.
  Qed.

  Lemma wp_receivefrom_nb_tracked_groups k saR sagR strck E ζ sh skt R T evs (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address saR in
    saddress skt = Some saR →
    sblock skt = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip] skt ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        ▷ receiveon_evs_groups sagR evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ)}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ sagR ⤳*[strck, true] (R, T))) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip] skt ∗ sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT, sagR} m') R⌝ ∗
             ∃ msg', ⌜msg ≡g{sagT, sagR} msg'⌝ ∗
                      ∃ φ, sagR ⤇* φ ∗ φ msg') ∨
           ⌜set_Exists (λ m', msg ≡g{sagT, sagR} m') R⌝) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs saR st sh msg skts skt r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st sh msg skts skt r).(post_state)) }}}.
  Proof.
    iIntros (? ? Hs Φ) "(>#HinR & Hsh & Hsa & Hevs & HΨ1 & HΨ2) HΦ".
    iApply (wp_receivefrom_nb_gen_tracked_groups None with "[$]"); [done..|].
    iNext. iIntros (r) "Hr". iApply "HΦ"; done.
  Qed.

  Lemma wp_receivefrom_nb_tracked Ψ k a strck E ζ sh skt R T evs (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ Ψ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ)}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T))) ∨
        (∃ msg,
            ⌜m_destination msg = a⌝ ∗
            ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                              (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
            ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗
              Ψ msg) ∨
             ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T)) ∗
            ∃ st skts r,
              ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
              receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
              Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state)) }}}.
  Proof.
    iIntros (? ? Hs Φ) "(Hsh & Hsa & #HΨ & Hevs & HΨ1 & HΨ2) HΦ".
    iApply (wp_receivefrom_nb_gen_tracked Ψ with "[$]"); [done|done|].
    iNext. iIntros (r) "Hr". iApply "HΦ"; done.
  Qed.

  Lemma wp_receivefrom_nb_alt_tracked_groups k saR sagR strck E ζ sh skt R T φ
        evs (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address saR in
    saddress skt = Some saR →
    sblock skt = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip] skt ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        sagR ⤇* φ ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ)}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ sagR ⤳*[strck, true] (R, T)) ∨
        ∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ ip_of_address saR] skt ∗
          sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT,sagR} m') R⌝ ∗
            ∃ msg', ⌜msg ≡g{sagT,sagR} msg'⌝ ∗ φ msg') ∨
           ⌜set_Exists (λ m', msg ≡g{sagT,sagR} m') R⌝) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs saR st sh msg skts skt r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st sh msg skts skt r).(post_state) }}}.
  Proof.
    iIntros (? ? Hs Φ) "(>#HinR & Hsh & Hsa & Hproto & Hevs & HΨ1 & HΨ2) HΦ".
    iApply (wp_receivefrom_nb_gen_tracked_groups (Some φ) with "[$]"); [done..|].
    iNext.
    iIntros (r) "Hr"; iApply "HΦ"; eauto 10.
  Qed.

  Lemma wp_receivefrom_nb_alt_tracked k a strck E ζ sh skt R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
          (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ)}}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳[strck, true] (R, T)) ∗
           ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts skt r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts skt r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts skt r).(post_state) }}}.
  Proof.
    iIntros (? ? Hs Φ) "(Hsh & Hsa & Hproto & Hevs & HΨ1 & HΨ2) HΦ".
    iApply (wp_receivefrom_nb_gen_tracked φ with "[$]"); [done|done|].
    iNext.
    iIntros (r) "Hr"; iApply "HΦ"; eauto 10.
  Qed.

  Lemma wp_receivefrom_tracked_groups k saR sagR strck E ζ sh s R T φ evs (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address saR in
    saddress s = Some saR →
    sblock s = true →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip] s ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        sagR ⤇* φ ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
        ∃ sagT,
          ⌜m_destination m = saR⌝ ∗
          m_sender m ∈g sagT ∗
          sh ↪[ip] s ∗ sagR ⤳*[strck, true] ({[ m ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ m ≡g{sagT,sagR} m') R⌝ ∗
            ∃ msg', ⌜m ≡g{sagT,sagR} msg'⌝ ∗ sagR  ⤇* φ ∗ φ msg') ∨
           ⌜set_Exists (λ m', m ≡g{sagT,sagR} m') R⌝) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs saR st sh m skts s r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st sh m skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st sh m skts s r).(post_state) }}}.
  Proof.
    simpl; iIntros (Haddr Hblk Φ) "(>#HinR & Hsh & Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    iApply (wp_receivefrom_gen_groups' (Some φ) _ _ _ _ true
              with "[$Hsh $Ha $Hsi $Hevs $HΨ1 $HΨ2 //] [HΦ]")%I; [done..|].
    iNext.
    iIntros (?) "[(?&?&?&%)|H]"; first by destruct (sblock s).
    iDestruct "H" as (m sagT ? <-) "H". subst.
    iApply "HΦ".
    iExists sagT.
    iDestruct "H" as "($ & $ & $ & H & $)".
    iSplit; [done|].
    iDestruct "H" as "[[%Hall (%m' & %Hmeq & H)]|H]";
      [by iLeft; eauto |by iRight].
  Qed.

  Lemma wp_receivefrom_tracked k a strck E ζ sh s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address a in
    saddress s = Some a →
    sblock s = true →
    {{{ ▷ sh ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
        ⌜m_destination m = a⌝ ∗
        ((⌜m ∉ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
         ⌜m ∈ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
        ∃ st skts r,
          ⌜valid_receiveonObs a st sh m skts s r⌝ ∗
          receiveon_evs a (evs ++ [receiveonObs a st sh m skts s r]) ∗
          Ψ1 st ∗ Ψ2 (receiveonObs a st sh m skts s r).(post_state) }}}.
  Proof.
    simpl; iIntros (Haddr Hblk Φ) "(Hsh & Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    iApply (wp_receivefrom_gen' φ _ _ _ true
              with "[$Hsh $Ha $Hsi $Hevs $HΨ1 $HΨ2 //] [HΦ]")%I; [done|].
    iNext.
    iIntros (?) "[(?&?&?&%)|H]"; first by destruct (sblock s).
    iDestruct "H" as (? ? ->) "[[(?&?&?&?)|(?&?&?)] H]"; iApply "HΦ"; iFrame "H".
    - iSplit; first done. by iLeft; iFrame.
    - iSplit; first done. by iRight; iFrame.
  Qed.

  Lemma wp_receivefrom_gen_tracked_groups k saR sagR strck E ζ sh s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address saR in
    saddress s = Some saR →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip] s ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        sagR ⤇* φ ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ sagR ⤳*[strck, true] (R, T)) ∨
        ∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip] s ∗ sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT,sagR} m') R⌝ ∗
            ∃ msg', ⌜msg ≡g{sagT,sagR} msg'⌝ ∗ φ msg') ∨
           ⌜set_Exists (λ m', msg ≡g{sagT,sagR} m') R⌝) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs saR st sh msg skts s r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st sh msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st sh msg skts s r).(post_state) }}}.
  Proof.
    simpl; iIntros (Haddr Φ) "(>#HinR & >Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    destruct (sblock s) eqn:Hblk.
    - iApply (wp_receivefrom_tracked_groups with "[$]"); eauto.
      iNext. iIntros (m) "[%sagT Hm]".
      iApply "HΦ". iRight. iExists m, sagT.
      iDestruct "Hm" as (?) "($ & $ & $ & H & $)".
      iSplit;[done|]. iSplit;[done|].
      iDestruct "H" as "[[% (%m' & Hmeq & _ & H)]|H]"; [by iLeft;eauto|by iRight].    - iApply (wp_receivefrom_nb_alt_tracked_groups with "[$]"); eauto.
  Qed.

  Lemma wp_receivefrom_gen_tracked k a strck E ζ sh s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    let ip := ip_of_address a in
    saddress s = Some a →
    {{{ ▷ sh ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; ζ; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts s r).(post_state) }}}.
  Proof.
    simpl; iIntros (Haddr Φ) "(>Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    destruct (sblock s) eqn:Hblk.
    - iApply (wp_receivefrom_tracked with "[$]"); eauto.
      iNext. iIntros (m) "Hm".
      iApply "HΦ". iRight. iExists m.
      iDestruct "Hm" as (?) "[[(% & Hh & Ha & _ & Hϕ) | Hm] $]";
        (repeat iSplit; first done; eauto).
      iLeft. eauto with iFrame.
    - iApply (wp_receivefrom_nb_alt_tracked with "[$]"); eauto.
  Qed.

  Lemma wp_rcvtimeo_unblock k a E ζ h s n1 n2 :
     let ip := ip_of_address a in
     saddress s = Some a →
     (0 ≤ n1 ∧ 0 <= n2 ∧ 0 < n1 + n2)%Z →
    {{{ ▷ h ↪[ip] s }}}
    (mkExpr ip (SetReceiveTimeout
                  (Val $ LitV $ LitSocket h)
                  (Val $ LitV $ LitInt n1)
                  (Val $ LitV $ LitInt n2))) @ k; ζ; E
     {{{ RET (mkVal ip #());
          h ↪[ip] s<|sblock := false|> }}}.
  Proof.
    iIntros (??? Φ) ">Hsh HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iMod (aneris_state_interp_sblock_update with "Hσ Hsh") as "(Hσ&Hsh)"; eauto.
    iModIntro. iSplitR.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step; last by lia.
    iModIntro.
    iExists (trace_last atr), ().
    rewrite -message_history_evolution_update_sblock; [|done|done].
    iSplitR; [done|].
    rewrite Htrig.
    iFrame.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_rcvtimeo_block k a E ζ h s :
     let ip := ip_of_address a in
     saddress s = Some a →
     {{{ ▷ h ↪[ip] s }}}
    (mkExpr ip (SetReceiveTimeout
                  (Val $ LitV $ LitSocket h)
                  (Val $ LitV $ LitInt 0)
                  (Val $ LitV $ LitInt 0))) @ k; ζ; E
     {{{ RET (mkVal ip #());
          h ↪[ip] s<|sblock := true|> }}}.
  Proof.
    iIntros (?? Φ) ">Hsh HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hlocale) "(Hevs & Hσ & Hm & % & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iMod (aneris_state_interp_sblock_update with "Hσ Hsh") as "(Hσ&Hsh)"; eauto.
    iModIntro. iSplitR.
    { iPureIntro; do 3 eexists.
      eapply SocketStepS; eauto.
      econstructor; naive_solver. }
    iIntros (v2' ? ? Hstep) "!>".
    pose proof Hex as Htrig.
    eapply aneris_events_state_interp_no_triggered in Htrig;
      [|done|done|done|done|done].
    inv_head_step; first by lia.
    iModIntro.
    iExists (trace_last atr), ().
    rewrite -message_history_evolution_update_sblock; [|done|done].
    iSplitR; [done|].
    rewrite Htrig.
    iFrame.
    iSplit; [ iPureIntro; apply user_model_evolution_id |].
    iApply ("HΦ" with "[$]").
  Qed.

End primitive_laws.
