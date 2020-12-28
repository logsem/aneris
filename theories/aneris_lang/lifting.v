From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From aneris.program_logic Require Export weakestpre lifting.
From aneris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import aneris_lang base_lang state_interp.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
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
    | H : base_lang.head_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
      inversion H; subst; clear H
    | H : head_step ?e _ _ _ _ _ |- _ =>
      try (is_var e; fail 1);
      inversion H; subst; clear H
    | H: socket_step _ ?e _ _ _ _ _ _ _ |- _ =>
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
         | H : socket_step _ _ _ _ _ _ _ _ _ |- _ =>
           inversion H
         end.
Local Ltac solve_pure_exec :=
  simplify_eq; rewrite /PureExec; intros;
  apply nsteps_once, pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Instance into_val_val n v : IntoVal (mkExpr n (Val v)) (mkVal n v).
Proof. done. Qed.
Instance as_val_val n v : AsVal (mkExpr n (Val v)).
Proof. by exists (mkVal n v). Qed.

Instance into_val_base_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_base_val v : AsVal (Val v).
Proof. by exists v. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; inv_head_step; naive_solver
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

Instance aneris_pure_exec_fill
         (K : list ectx_item) ip (φ : Prop) (n : nat) (e1 e2 : expr) :
  PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
  @PureExec aneris_lang φ n
            (mkExpr ip (@fill base_ectxi_lang K e1))
            (mkExpr ip (@fill base_ectxi_lang K e2)).
Proof.
  intros.
  rewrite !aneris_base_fill.
  eapply pure_exec_ctx; first apply _; done.
Qed.

Instance binop_atomic n s op v1 v2 :
  Atomic s (mkExpr n (BinOp op (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance alloc_atomic n s v : Atomic s (mkExpr n (Alloc (Val v))).
Proof. solve_atomic. Qed.
Instance load_atomic n s v : Atomic s (mkExpr n (Load (Val v))).
Proof. solve_atomic. Qed.
Instance store_atomic n s v1 v2 : Atomic s (mkExpr n (Store (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance cmpxchg_atomic n s v0 v1 v2 :
  Atomic s (mkExpr n (CAS (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance fork_atomic n s e : Atomic s (mkExpr n (Fork e)).
Proof. solve_atomic. Qed.
Instance skip_atomic n s : Atomic s (mkExpr n Skip).
Proof. solve_atomic. Qed.

Instance newsocket_atomic n v0 v1 v2 s :
  Atomic s (mkExpr n  (NewSocket (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.
Instance socketbind_atomic n v0 v1  s :
  Atomic s (mkExpr n (SocketBind (Val v0) (Val v1))).
Proof. solve_atomic. Qed.
Instance sendto_atomic n v0 v1 v2 s :
  Atomic s (mkExpr n (SendTo (Val v0) (Val v1) (Val v2))).
Proof. solve_atomic. Qed.

(* NB: receive is not atomic any more! *)
(* Instance receivefrom_atomic n v s :
 Atomic s (mkExpr n (ReceiveFrom (Val v))).
Proof. solve_atomic. Qed.*)

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Instance pure_rec n f x (erec : expr) :
  PureExec True 1 (mkExpr n (Rec f x erec)) (mkExpr n (Val $ RecV f x erec)).
Proof. solve_pure_exec. Qed.
Instance pure_pairc n (v1 v2 : val):
  PureExec True 1 (mkExpr n (Pair (Val v1) (Val v2))) (mkExpr n (Val $ PairV v1 v2)).
Proof. solve_pure_exec. Qed.
Instance pure_injlc n (v : val) :
  PureExec True 1 (mkExpr n (InjL $ Val v)) (mkExpr n (Val $ InjLV v)).
Proof. solve_pure_exec. Qed.
Instance pure_injrc n (v : val) :
  PureExec True 1 (mkExpr n (InjR $ Val v)) (mkExpr n (Val $ InjRV v)).
Proof. solve_pure_exec. Qed.

Instance pure_beta n f x erec (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (mkExpr n (App (Val v1) (Val v2)))
           (mkExpr n (subst' x v2 (subst' f v1 erec))).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop n op v v' :
  PureExec (un_op_eval op v = Some v') 1 (mkExpr n (UnOp op (Val v)))
           (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

Instance pure_binop n op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1
           (mkExpr n (BinOp op (Val v1) (Val v2))) (mkExpr n (of_val v')).
Proof. solve_pure_exec. Qed.

Instance pure_if_true n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool true) e1 e2)) (mkExpr n e1).
Proof. solve_pure_exec. Qed.

Instance pure_if_false n e1 e2 :
  PureExec True 1 (mkExpr n (If (Val $ LitV $ LitBool false) e1 e2))
           (mkExpr n e2).
Proof. solve_pure_exec. Qed.

Instance pure_fst n v1 v2 :
  PureExec True 1 (mkExpr n (Fst (PairV v1 v2))) (mkExpr n (Val v1)).
Proof. solve_pure_exec. Qed.

Instance pure_snd n v1 v2  :
  PureExec True 1 (mkExpr n (Snd (PairV v1 v2))) (mkExpr n (Val v2)).
Proof. solve_pure_exec. Qed.

Instance pure_find_from n v0 v1 n1 v2 v' :
  PureExec (index n1 v2 v0 = v' ∧ Z.of_nat n1 = v1) 1
           (mkExpr n (FindFrom (Val $ LitV $ LitString v0)
                       (Val $ LitV $ LitInt v1)
                       (Val $ LitV $ LitString v2)))
           (mkExpr n (base_lang.of_val (option_nat_to_val v'))).
Proof. solve_pure_exec. Qed.

Instance pure_substring n v0 v1 n1 v2 n2 v' :
  PureExec (substring n1 n2 v0 = v' ∧ Z.of_nat n1 = v1 ∧ Z.of_nat n2 = v2) 1
           (mkExpr
              n (Substring
                   (LitV $ LitString v0) (LitV $ LitInt v1) (LitV $ LitInt v2)))
           (mkExpr n (base_lang.of_val (LitV $ LitString v'))).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl n v e1 e2  :
  PureExec True 1 (mkExpr n (Case (Val $ InjLV v) e1 e2))
           (mkExpr n (App e1 (Val v))).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr n v e1 e2 :
  PureExec True 1 (mkExpr n (Case (Val $ InjRV v) e1 e2))
           (mkExpr n (App e2 (Val v))).
Proof. solve_pure_exec. Qed.

Instance pure_make_address n v1 v2 :
  PureExec True 1
           (mkExpr n (MakeAddress (LitV (LitString v1)) (LitV (LitInt (v2)))))
           (mkExpr
              n (LitV (LitSocketAddress (SocketAddressInet v1 (Z.to_pos v2))))).
Proof. solve_pure_exec. Qed.

Opaque aneris_state_interp.

Section primitive_laws.
  Context `{anerisG Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : aneris_val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.
  Implicit Types σ : state.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.

  Lemma wp_fork n k E e Φ :
    ▷ Φ (mkVal n #()) ∗ ▷ WP (mkExpr n e) @ k; ⊤ {{ _, True }} ⊢
    WP (mkExpr n (Fork e)) @ k; E {{ Φ }}.
  Proof.
    iIntros "[HΦ He]". iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 κ κs m) "Hσ !>". iSplit.
    - iPureIntro. eexists; solve_exec_safe.
    - iIntros (? ? ? ?). inv_head_step. iFrame. done.
  Qed.

  Lemma wp_alloc n k E v :
    {{{ ▷ is_node n }}}
      (mkExpr n (Alloc (Val v))) @ k; E
    {{{ l, RET (mkVal n #l); l ↦[n] v }}}.
  Proof.
    iIntros (Φ) ">Hn HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ ? ? ?) "Hσ !> /=".
    iDestruct (is_node_heap_valid with "Hσ Hn") as (h) "%".
    iSplitR.
    { iPureIntro. do 4 eexists. eapply LocalStepS; eauto. }
    iIntros (v2 σ2 efs Hstep); inv_head_step.
    iSplitR; [done|]. iModIntro.
    iMod (aneris_state_interp_alloc_heap with "Hn Hσ") as "[Hσ Hl]"; [done..|].
    iModIntro. iFrame.
    by iApply "HΦ".
  Qed.

  Lemma wp_load n k E l q v :
    {{{ ▷ l ↦[n]{q} v }}}
      (mkExpr n (Load #l)) @ k; E
    {{{ RET (mkVal n v); l ↦[n]{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ κ κs n') "Hσ !> /=".
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro. do 4 eexists. eapply LocalStepS; eauto. eapply LoadS; eauto. }
    iIntros (e2 σ2 efs Hstep). inv_head_step.
    rewrite insert_id //. destruct σ; iFrame.
    do 2 iModIntro. iSplit; [done|]. by iApply "HΦ".
  Qed.

  Lemma wp_store n k E l v1 v2 :
    {{{ ▷ l ↦[n] v1 }}}
      (mkExpr n (Store #l (Val v2))) @ k; E
    {{{ RET (mkVal n #()); l ↦[n] v2 }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ κ κs n') "Hσ !>".
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 4 eexists. eapply LocalStepS; eauto. econstructor. }
    iIntros (????); inv_head_step. iModIntro.
    iMod (aneris_state_interp_heap_update with "[$Hσ $Hl]") as "[Hσ Hl]";
      [done|].
    iModIntro. iSplit; [done|]. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail n k E l q v v1 v2 :
    v ≠ v1 →
    {{{ ▷ l ↦[n]{q} v }}}
      (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; E
    {{{ RET (mkVal n #false); l ↦[n]{q} v }}}.
  Proof.
    iIntros (Heq Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ κ κs n') "Hσ !>".
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 4 eexists. eapply LocalStepS; eauto. by econstructor. }
    iIntros (????); inv_head_step. iModIntro.
    rewrite insert_id //. destruct σ; iFrame.
    iModIntro. iSplit; [done|]. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc n k E l v1 v2 :
    {{{ ▷ l ↦[n] v1 }}}
      (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; E
    {{{ RET (mkVal n #true); l ↦[n] v2 }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ κ κs n') "Hσ !>".
    iDestruct (aneris_state_interp_heap_valid with "Hσ Hl") as (h) "[% %]".
    iSplit.
    { iPureIntro; do 4 eexists. eapply LocalStepS; eauto. by econstructor. }
    iIntros (????); inv_head_step. iModIntro.
    iMod (aneris_state_interp_heap_update with "[$Hσ $Hl]") as "[Hσ Hl]";
      [done|].
    iModIntro. iSplit; [done|]. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_start ip ports k E e Φ :
    ip ≠ "system" →
    ▷ free_ip ip ∗
    ▷ Φ (mkVal "system" #()) ∗
    ▷ (is_node ip -∗ free_ports ip ports -∗
              ([∗ set] p ∈ ports, (SocketAddressInet ip p) ⤳ (∅, ∅)) -∗
               WP (mkExpr ip e) @ k; ⊤ {{ _, True }})
    ⊢ WP (mkExpr "system" (Start (LitString ip) e)) @ k; E {{ Φ }}.
  Proof.
    iIntros (?) "(>Hfip & HΦ & Hwp)".
    iApply (wp_lift_head_step with "[-]"); first auto.
    iIntros (σ κ κs n) "Hσ".
    iMod (fupd_intro_mask _ ∅ True%I with "[]") as "Hmk"; first set_solver; auto.
        iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip")
      as "(% & % & %)".
    iModIntro; iSplit.
    { iPureIntro. do 4 eexists. apply (AssignNewIpStepS _ _ []); eauto. }
    iNext. iIntros (e2 σ2 efs Hrd). iMod "Hmk" as "_".
    inv_head_step.
    iMod (aneris_state_interp_alloc_node _ _ ports with "[$]")
      as "(Hn & Hports & Hms & Hσ)".
    iModIntro. iFrame.
    iSplitL "HΦ"; [by iApply wp_value|].
    iSplitL; [|done].
    by iApply ("Hwp" with "[$] [$]").
  Qed.

  Lemma wp_new_socket ip s E f t p :
    {{{ ▷ is_node ip }}}
      (mkExpr ip (NewSocket (Val $ LitV $ LitAddressFamily f)
                            (Val $ LitV $ LitSocketType t)
                            (Val $ LitV $ LitProtocol p))) @ s; E
    {{{ sh, RET (mkVal ip (LitV (LitSocket sh)));
        sh ↪[ip] (mkSocket f t p None true) }}}.
  Proof.
    iIntros (Φ) ">Hn HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (σ κ κs n) "Hσ !> /=".
    iDestruct (is_node_valid_sockets with "Hσ Hn") as (?) "%".
    iSplitR.
    { iPureIntro; do 4 eexists.
      eapply (SocketStepS _ _ _ _ _ _ _ _ []); eauto.
      apply newsocket_fresh. }
    set (sock := {| sfamily := f;
                    stype := t;
                    sprotocol := p;
                    saddress := None;
                    sblock := true |}).
    iIntros (v2' ? ? Hstep) "!>"; inv_head_step.
    iMod (aneris_state_interp_alloc_socket sock with "Hn Hσ")
      as "[Hσ Hsh]"; try done.
    iModIntro. iFrame. iSplitR; [done|]. by iApply "HΦ".
  Qed.


  Lemma wp_socketbind_static A E sh skt k a R T:
    saddress skt = None →
    a ∈ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳ (R, T) }}}
      (mkExpr (ip_of_address a)
              (SocketBind (Val $ LitV $ LitSocket sh)
                          (Val $ LitV $ LitSocketAddress a))) @ k; E
   {{{ RET (mkVal (ip_of_address a) #0);
       sh ↪[ip_of_address a] (skt<| saddress := Some a |>) ∗
       a ⤳ (R, T) ∗
       ∃ φ, a ⤇ φ }}}.
  Proof.
  Admitted.
(*    iIntros (?? Φ) "(#Hfixed & >Hp & >Hsh) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (σ κ κs n) "Hσ /=".
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh") as (?) "[% %]".
    iDestruct (aneris_state_interp_free_ports_valid with "Hσ Hp") as (?) "[% %]".
    iModIntro. iSplitR.
    { iPureIntro; do 4 eexists. eapply (SocketStepS _ _ _ _ _ _ _ _ []); eauto.
      by econstructor. }
    iIntros (v2' ? ? Hstep) "!>"; inv_head_step.
    iMod (aneris_state_interp_socketbind_static with "Hσ Hfixed Hsh Hp")
      as "(Hσ & Hsh & Hφ)"; [done..|].
    iModIntro. iSplitR; [done|]. iFrame.
    iApply ("HΦ" with "[$]").
  Qed. *)

  Lemma wp_socketbind_dynamic skt A E sh k a φ R T:
    saddress skt = None →
    a ∉ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳ (R, T)
    }}}
      (mkExpr (ip_of_address a)
              (SocketBind (Val $ LitV $ LitSocket sh)
                          (Val $ LitV $ LitSocketAddress a))) @ k; E
    {{{ RET (mkVal (ip_of_address a) #0);
        sh ↪[ip_of_address a] (skt <| saddress := Some a |>) ∗
        a ⤳ (R, T) ∗
        a ⤇ φ }}}.
  Proof.
  Admitted.
(*    iIntros (?? Φ) "(#>Hfixed & >Hp & >Hsh) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; first auto.
    iIntros (σ κ κs n) "Hσ /=".
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh") as (?) "[% %]".
    iDestruct (aneris_state_interp_free_ports_valid with "Hσ Hp") as (?) "[% %]".
    iModIntro. iSplitR.
    { iPureIntro; do 4 eexists. eapply (SocketStepS _ _ _ _ _ _ _ _ []); eauto.
      by econstructor. }
    iIntros (v2' ? ? Hstep) "!>"; inv_head_step.
    iMod (aneris_state_interp_socketbind_dynamic with "Hσ Hfixed Hsh Hp")
      as "(Hσ & Hsh & Hφ)"; [done..|].
    iModIntro. iSplitR; [done|]. iFrame.
    iApply ("HΦ" with "[$]").
  Qed. *)

  Lemma wp_send φ mbody sh skt a to k E R T:
    let msg := mkMessage a to (sprotocol skt) mbody  in
    saddress skt = Some a ->
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳ (R, T) ∗
        ▷ to ⤇ φ ∗
        ▷ φ msg }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳ (R, {[ msg ]} ∪ T) }}}.
  Proof.
  Admitted.
  (*    iIntros (? Hsome Φ) "(>Hsh & #Hφ & Hm) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ κ κs n) "Hσ !>".
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh") as (?) "[% %]".
    iSplitR.
    { iPureIntro; do 4 eexists; eapply (SocketStepS _ _ _ _ _ _ _ _ []); eauto.
        by econstructor. }
    iIntros (????) "!>"; inv_head_step; rewrite -/msg.
    iMod (aneris_state_interp_send with "Hsh Hφ Hm Hσ") as "[Hσ Hsh]";
      [done..|].
    iModIntro. iSplitR; [done|]. iFrame. by iApply "HΦ".
  Qed. *)

  Lemma wp_send_duplicate mbody sh skt a to k E R T:
    let msg := mkMessage a to (sprotocol skt) mbody in
    saddress skt = Some a ->
    msg ∈ T →
    {{{  ▷ sh ↪[ip_of_address a] skt ∗
         ▷ a ⤳ (R, T) }}}
      (mkExpr (ip_of_address a)
              (SendTo (Val $ LitV $ LitSocket sh) #mbody #to)) @ k; E
    {{{ RET (mkVal (ip_of_address a) #(String.length mbody));
        sh ↪[ip_of_address a] skt ∗
        a ⤳ (R, T) }}}.
  Proof.
  Admitted.
  (*
    iIntros (msg Hsome Hmsg Φ) ">Hsh HΦ /=".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ κ κs n) "Hσ !>".
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh") as (?) "[% %]".
    iSplitR.
    { iPureIntro; do 4 eexists; eapply (SocketStepS _ _ _ _ _ _ _ _ []); eauto.
        by econstructor. }
    iIntros (????) "!>"; inv_head_step; rewrite -/msg.
    iMod (aneris_state_interp_send_duplicate with "Hsh Hσ") as "[Hσ Hsh]";
      [done..|].
    iModIntro. iSplitR; [done|]. iFrame. by iApply "HΦ".
   Qed.
   *)

  Lemma wp_receivefrom_nb_gen
        (Ψo : option (socket_interp Σ)) k a E sh skt R T :
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip_of_address a] skt ∗
        ▷ a ⤳ (R, T) ∗
        match Ψo with Some Ψ => a ⤇ Ψ | _ => True end }}}
      (mkExpr (ip_of_address a)
              (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; E
    {{{ r, RET (mkVal (ip_of_address a) r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳ (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
            ⌜msg ∈ R⌝ ∗ sh ↪[ip_of_address a] skt ∗ a ⤳ (R, T))))) }}}.
  Proof.
  Admitted.
(*    iIntros (Hsome Φ) "[>Hsh #HΨ] HΦ /=".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ κ κs n) "Hσ !>".
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh") as (?) "[% %]".
    iSplitR.
    { iPureIntro; do 4 eexists; eapply (SocketStepS _ _ _ _ _ _ _ _ []); eauto.
        by econstructor. }
    iIntros (????); inv_head_step; (iSplitR; [done|]).
    - (* received a message *)
      iDestruct (aneris_state_interp_receive with "HΨ [$Hσ $Hsh]") as "H";
        [done..|].
      iDestruct "H" as (R') "[Hsi Hσ2]".
      iNext. iMod "Hσ2" as "[$ Hsh]". iModIntro.
      iApply "HΦ". iRight. iExists m. iFrame.
      match goal with
      | H: m ∈ messages_to_receive_at a (state_ms σ) |- _ =>
        apply elem_of_filter in H as (? &?)
      end.
      do 2 (iSplit; [done|]).
      iDestruct "Hsi" as "[(% & -> & ?) | (% & ->) ]"; [|eauto].
      iLeft. by iFrame.
    - (* did not receive a message *)
      assert
      (<[ip_of_address a:=Sn']> (state_sockets σ) = state_sockets σ) as ->.
      { by apply insert_id. }
      iModIntro. iFrame. iApply "HΦ"; auto.
  Qed. *)

  Lemma wp_receivefrom_nb k a E sh skt R T :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗ ▷ a ⤳ (R, T) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗
             ∃ φ, a ⤇ φ ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] skt ∗ a ⤳ (R, T))) }}}.
   Proof.
     iIntros (? ? Hs Φ) "(Hsh & Hsa) HΦ".
     iApply (wp_receivefrom_nb_gen None with "[$]"); [done|done|].
     iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
   Qed.

  Lemma wp_receivefrom_nb_alt k a E sh skt R T φ :
    let ip := ip_of_address a in
    saddress skt = Some a →
    sblock skt = false →
    {{{ ▷ sh ↪[ip] skt ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; E
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
     iApply (wp_receivefrom_nb_gen (Some φ) with "[$]"); [done|done|].
     iNext. iIntros (r) "Hr". iApply "HΦ"; eauto.
   Qed.


   Lemma wp_receivefrom_hocap k a E h s R T φ
         (P : iProp Σ) (Q__new Q__old : message -> iProp Σ) :
     let ip := ip_of_address a in
     saddress s = Some a →
     sblock s = true →
    □ (P ={⊤, E}=∗
            h ↪[ip] s ∗ a ⤳ (R, T) ∗
           (h ↪[ip] s ∗ a ⤳ (R, T) ={E, ⊤}=∗ P) ∧
      (∀ m, h ↪[ip] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ ⌜m ∉ R⌝ ∗ φ m ={E, ⊤}=∗ Q__new m) ∧
      (∀ m, h ↪[ip] s ∗ a ⤳ (R, T) ∗ ⌜m ∈ R⌝ ={E, ⊤}=∗ Q__old m)) -∗
  {{{ P ∗ a ⤇ φ}}}
    (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; E
  {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
      (⌜m ∉ R⌝ ∗ Q__new m ∨
       ⌜m ∈ R⌝ ∗ Q__old m)
  }}}.
  Proof.
  Admitted.
  (* iIntros (n Haddr) "#Hpreds".
    iModIntro. iIntros (Φ) "(HP & #Hsi) HΦ".
    iLöb as "IH". wp_rec.
    wp_bind (ReceiveFrom _).
    iMod ("Hpreds" with "HP") as "(Hs & Hall)".
    wp_apply (aneris_wp_receivefrom_alt with "[$Hs]");
      [done|done|by iFrame "#"|].
    iIntros (r)  "[(-> & Hs) | Hrd ]".
    - (* No message *)
      iDestruct "Hall" as "[Hempty _]".
      iMod ("Hempty" with "Hs") as "HP".
      iModIntro; wp_pures.
      by iApply ("IH" with "HP HΦ").
    - iDestruct "Hrd" as (m Hdst ->) "[ (% & Hs & Hφ) | (% & Hs) ]".
      + (* New message *)
        iDestruct "Hall" as "(_ & Hnew & _)".
        iMod ("Hnew" $! m with "[Hs Hφ]") as "Qnew".
        { eauto with iFrame. }
        iModIntro; wp_pures.
        iApply "HΦ". iLeft. eauto with iFrame.
      + (* Old message *)
        iDestruct "Hall" as "(_ & _ & Hold)".
        iMod ("Hold" $! m with "[Hs]") as "Qold".
        { eauto with iFrame. }
        iModIntro; wp_pures.
        iApply "HΦ". iRight. eauto with iFrame.
  Qed.
   *)

  Lemma wp_receivefrom k a E h s R T φ P :
     let ip := ip_of_address a in
     saddress s = Some a →
     sblock s = true →
  {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
    (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; E
  {{{ m, RET (mkVal ip (SOMEV (PairV #(m_body m) #(m_sender m))));
      ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
        ⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))
  }}}.
  Proof.
  Admitted.
(*  iIntros (n Haddr Φ) "(Hs & #Hsi) HΦ".
    wp_apply (listen_wait_hocap_spec _ _ _ _ _ _
          φ (h ↪[ip] (s, R, T))
                     (λ m, h ↪[ip] (s, {[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m)
                                     (λ m, h ↪[ip] (s, R, T))
                                     ⊤ with "[] [$Hs]")%I; eauto.
    iModIntro. iIntros "Hs".
    iModIntro; iFrame.
    repeat iSplit; eauto with iFrame.
    - iIntros (?) "(? & ? & ?)"; eauto with iFrame.
    - iIntros (?) "(? & ?)"; eauto with iFrame.
  Qed.
*)

  Lemma wp_rcvtimeo_unblock k a E h s R T P n1 n2 :
     let ip := ip_of_address a in
     saddress s = Some a →
     0 <= n1 →
     0 < n2 →
    {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) }}}
    (mkExpr ip (SetReceiveTimeout
                  (Val $ LitV $ LitSocket h)
                  (Val $ LitV $ LitInt n1)
                  (Val $ LitV $ LitInt n2))) @ k; E
     {{{ RET (mkVal ip #());
          h ↪[ip] s<|sblock := false|> ∗ a ⤳ (R, T) }}}.
  Proof.
  Admitted.

  Lemma wp_rcvtimeo_block k a E h s R T P :
     let ip := ip_of_address a in
     saddress s = Some a →
     {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) }}}
    (mkExpr ip (SetReceiveTimeout
                  (Val $ LitV $ LitSocket h)
                  (Val $ LitV $ LitInt 0)
                  (Val $ LitV $ LitInt 0))) @ k; E
     {{{ RET (mkVal ip #());
          h ↪[ip] s<|sblock := true|> ∗ a ⤳ (R, T) }}}.
  Proof.
  Admitted.

End primitive_laws.
