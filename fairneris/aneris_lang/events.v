From trillium.events Require Export event.
From trillium.program_logic Require Import
     language ectx_language ectxi_language.
From fairneris.aneris_lang Require Import aneris_lang base_lang.
From RecordUpdate Require Import RecordSet.
From fairneris.algebra Require Import disj_gsets.

Import ast.
Import RecordSetNotations.

Lemma fill_mkExpr ip K e :
  fill K (mkExpr ip e) = mkExpr ip (fill (Λ := base_ectxi_lang) K e).
Proof.
  induction K as [|? ? IH] using rev_ind; first done.
  rewrite /= !fill_app /= IH //=.
Qed.

Lemma is_Some_to_val_mkExpr ip e :
  is_Some (ectx_language.to_val (mkExpr ip e)) ↔ is_Some (ectx_language.to_val e).
Proof.
  rewrite /= /aneris_to_val /=; destruct (to_val e); simpl.
  - split; eauto.
  - split; intros [? ?]; done.
Qed.

Program Definition allocEV (lbl : string) : Event aneris_lang :=
  {| is_triggered e σ e' σ' :=
       ∃ ip v h (ℓ : loc),
         e = (mkExpr ip (ref<<lbl>> (Val v))%E) ∧
         e' = (mkExpr ip #ℓ) ∧
         σ.(state_heaps) !! ip = Some h ∧
         h !! ℓ = None ∧
         σ' = σ <| state_heaps := <[ip:=<[ℓ:=v]>h]>(state_heaps σ) |>
  |}.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&->&?); done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&h&?&->&?&?&?&?).
  intros K [ip' e1'] He1.
  rewrite fill_mkExpr in He1.
  simplify_eq He1; intros -> He1'.
  rewrite is_Some_to_val_mkExpr.
  eapply (ectx_language.head_ctx_step_val (Λ := base_ectx_lang) _ _ h).
  rewrite /= -He1'; constructor; done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&->&->&?).
  intros Heq; simplify_eq/=.
Qed.

Lemma allocEV_impure lbl eo :
  validEventObservation (allocEV lbl) eo → eo.(pre_state) ≠ eo.(post_state).
Proof.
  destruct 1 as (ip&v&h&ℓ&?&?&Hiplu&Hℓ&Hsts); intros Heq.
  rewrite -Heq in Hsts.
  pose proof (f_equal (λ σ, σ.(state_heaps) !! ip) Hsts) as Hsts2.
  rewrite /= lookup_insert Hiplu in Hsts2.
  simplify_eq Hsts2; intros Hsts3.
  pose proof (f_equal (λ h, h !! ℓ) Hsts3) as Hsts4.
  rewrite /= lookup_insert Hℓ in Hsts4; done.
Qed.

Lemma allocEV_inj lbl lbl' e1 σ1 e2 σ2 :
  allocEV lbl e1 σ1 e2 σ2 → allocEV lbl' e1 σ1 e2 σ2 → lbl = lbl'.
Proof. by intros (?&?&?&?&?&?&?&?&?) (?&?&?&?&?&?&?&?&?); simplify_eq. Qed.

Definition allocObs (ip : ip_address) (lbl : string) (l : loc) (v : val)
           (σ : state) (h : heap) :=
  mkEventObservation
    (mkExpr ip (ref<<lbl>> (Val v)))
    σ
    (mkExpr ip #l)
    (σ <| state_heaps := <[ip:=<[l:=v]>h]>(state_heaps σ) |>).

Definition valid_allocObs (ip : ip_address) (l : loc) (σ : state) (h : heap) :=
  σ.(state_heaps) !! ip = Some h ∧ h !! l = None.

Program Definition sendonEV_groups (sag : gset socket_address) : Event aneris_lang :=
  {| is_triggered e σ e' σ' :=
       ∃ (sa : socket_address) (sh: socket_handle)
         (mbody: string) (to: socket_address) skts skt r,
         sa ∈ sag ∧
         σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
         skts !! sh = Some (skt, r) ∧
         saddress skt = Some sa ∧
         e = (mkExpr (ip_of_address sa) (SendTo #(LitSocket sh) #mbody #to)) ∧
         e' = (mkExpr (ip_of_address sa) #(String.length mbody)) ∧
         σ' = σ <| state_ms := {[+ mkMessage sa to mbody +]} ⊎ σ.(state_ms) |>
  |}.
Next Obligation.
Proof.
  simpl. intros ?????(?&?&?&?&?&?&?&?&?&?&?&->&?); done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&?&?&->&?&?).
  intros K [ip' e1'] He1.
  rewrite fill_mkExpr in He1.
  simplify_eq He1; intros <- He1'.
  eapply (ectx_language.head_ctx_step_val (Λ := aneris_ectx_lang) _ _ σ1).
  rewrite /= fill_mkExpr.
  rewrite /= -He1'. eapply SocketStepS; last done.
  econstructor; done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&?&?&->&->&?).
  intros Heq; simplify_eq/=.
Qed.

Definition sendonEV (sa : socket_address) : Event aneris_lang :=
  sendonEV_groups {[sa]}.

Lemma sendonEV_groups_impure sag eo :
  validEventObservation (sendonEV_groups sag) eo → eo.(pre_state) ≠ eo.(post_state).
Proof.
  destruct 1 as (sa&sh&mbody&to&skts&skt&r&Hsa&Hiplu&Hskts&Hskt&?&?&Hsts); intros Heq.
  rewrite -Heq in Hsts.
  set (msg := {| m_sender := sa; m_destination := to; m_body := mbody |}).
  pose proof (f_equal (λ σ, multiplicity msg σ.(state_ms)) Hsts) as Hsts2.
  rewrite /= multiplicity_disj_union multiplicity_singleton in Hsts2; lia.
Qed.

Lemma sendonEV_groups_inj sag sag' e1 σ1 e2 σ2 :
  eq_or_disj sag sag' →
  sendonEV_groups sag e1 σ1 e2 σ2 → sendonEV_groups sag' e1 σ1 e2 σ2 → sag = sag'.
Proof.
  intros Hdisj.
  intros (sa&?&?&?&?&?&?&Hsa&?&?&?&?&?&?) (sa'&?&?&?&?&?&?&Hsa'&?&?&?&?&?&?).
  destruct Hdisj as [ Hdisj | Hdisj ]; [ done | ].
  assert (sa = sa').
  { destruct sa; destruct sa'. simplify_eq/=. done. }
  subst.
  pose proof (elem_of_disjoint sag sag') as [Hfalso _].
  specialize (Hfalso Hdisj _ Hsa Hsa').
  done.
Qed.

Lemma sendonEV_inj sa sa' e1 σ1 e2 σ2 :
  sendonEV sa e1 σ1 e2 σ2 → sendonEV sa' e1 σ1 e2 σ2 → sa = sa'.
Proof.
  intros H1 H2.
  assert ({[sa]} = ({[sa']}:gset _)).
  { eapply sendonEV_groups_inj; [apply eq_or_disj_singleton|done..]. }
  set_solver.
Qed.

Definition sendonObs (sa : socket_address) (σ : state) (sh : socket_handle)
           (mbody: string) (to : socket_address) (skt : socket) :=
  mkEventObservation
    (mkExpr (ip_of_address sa) (SendTo #(LitSocket sh) #mbody #to))
    σ
    (mkExpr (ip_of_address sa) #(String.length mbody))
    (σ <| state_ms := {[+ mkMessage sa to mbody +]} ⊎ σ.(state_ms) |>).

Definition valid_sendonObs (sa : socket_address) (σ : state) (sh : socket_handle)
           (skts : sockets) (skt : socket) (r : list message) :=
  σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
  skts !! sh = Some (skt, r) ∧
  saddress skt = Some sa.

Program Definition receiveonEV_groups
        (sag : gset socket_address) : Event aneris_lang :=
  {| is_triggered e σ e' σ' :=
       ∃ (sa : socket_address) (sh: socket_handle) skts skt r m,
         sa ∈ sag ∧
         σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
         skts !! sh = Some (skt, r ++ [m]) ∧
         saddress skt = Some sa ∧
         e = (mkExpr (ip_of_address sa) (ReceiveFrom #(LitSocket sh))) ∧
         e' = (mkExpr (ip_of_address sa) (SOMEV (#(m_body m),#(m_sender m)))) ∧
         σ' = σ <| state_sockets := <[(ip_of_address sa) :=
                                        <[sh := (skt, r)]>skts]> σ.(state_sockets) |>
  |}.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&?&->&?); done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&?&->&?&?).
  intros K [ip' e1'] He1.
  rewrite fill_mkExpr in He1.
  simplify_eq He1; intros <- He1'.
  eapply (ectx_language.head_ctx_step_val (Λ := aneris_ectx_lang) _ _ σ1).
  rewrite /= fill_mkExpr.
  rewrite /= -He1'. eapply SocketStepS; last done.
  econstructor; done.
Qed.
Next Obligation.
Proof.
  simpl; intros ?????(?&?&?&?&?&?&?&?&?&?&->&->&?).
  intros Heq; simplify_eq/=.
Qed.

Definition receiveonEV (sa : socket_address) : Event aneris_lang :=
  receiveonEV_groups {[sa]}.

Lemma receiveonEV_groups_impure sag eo :
  validEventObservation (receiveonEV_groups sag) eo → eo.(pre_state) ≠ eo.(post_state).
Proof.
  destruct 1 as (sa&sh&skts&skt&r&m&Hsa&Hiplu&Hskts&Hskt&?&?&Hsts); intros Heq.
  rewrite -Heq in Hsts.
  pose proof (f_equal (λ σ, σ.(state_sockets) !! (ip_of_address sa)) Hsts) as Hsts2.
  rewrite /= lookup_insert Hiplu in Hsts2.
  simplify_eq Hsts2; intros Hsts3.
  pose proof (f_equal (λ h, h !! sh) Hsts3) as Hsts4.
  rewrite /= lookup_insert Hskts in Hsts4.
  list_simplifier. assert ([m] = []); last done.
  eapply (inj (app r)). by list_simplifier.
Qed.

Lemma receiveonEV_groups_inj sag sag' e1 σ1 e2 σ2 :
  eq_or_disj sag sag' →
  receiveonEV_groups sag e1 σ1 e2 σ2 → receiveonEV_groups sag' e1 σ1 e2 σ2 → sag = sag'.
Proof.
  intros Hdisj.
  intros (sa&?&?&?&?&?&Hsa&?&?&?&?&?&?) (sa'&?&?&?&?&?&Hsa'&?&?&?&?&?&?).
  destruct Hdisj as [ Hdisj | Hdisj ]; [ done | ].
  assert (sa = sa').
  { destruct sa; destruct sa'. simplify_eq/=. done. }
  subst.
  pose proof (elem_of_disjoint sag sag') as [Hfalso _].
  specialize (Hfalso Hdisj _ Hsa Hsa').
  done.
Qed.

Lemma receiveonEV_inj sa sa' e1 σ1 e2 σ2 :
  receiveonEV sa e1 σ1 e2 σ2 → receiveonEV sa' e1 σ1 e2 σ2 → sa = sa'.
Proof.
  intros H1 H2.
  assert ({[sa]} = ({[sa']}:gset _)).
  { eapply receiveonEV_groups_inj; [apply eq_or_disj_singleton|done..]. }
  set_solver.
Qed.

Definition receiveonObs (sa : socket_address) (σ : state) (sh : socket_handle)
           (m: message) (skts : sockets) (skt : socket) (r : list message) :=
  mkEventObservation
    (mkExpr (ip_of_address sa) (ReceiveFrom #(LitSocket sh)))
    σ
    (mkExpr (ip_of_address sa) (SOMEV (#(m_body m),#(m_sender m))))
    (σ <| state_sockets :=
       <[(ip_of_address sa):= <[sh := (skt, r)]>skts]> σ.(state_sockets) |>).

Definition valid_receiveonObs (sa : socket_address) (σ : state)
           (sh : socket_handle) (m: message)
           (skts : sockets) (skt : socket) (r : list message) :=
  σ.(state_sockets) !! (ip_of_address sa) = Some skts ∧
  skts !! sh = Some (skt, r ++ [m]) ∧ saddress skt = Some sa.

(** if one event is triggered, the other two are not *)
Lemma ev_not_others_alloc_groups lbl e1 σ1 e2 σ2 :
  allocEV lbl e1 σ1 e2 σ2 →
  (∀ sag, ¬ sendonEV_groups sag e1 σ1 e2 σ2) ∧
  (∀ sag, ¬ receiveonEV_groups sag e1 σ1 e2 σ2).
Proof.
  destruct 1 as (?&?&?&?&?&?&?&?&?); simplify_eq.
  split.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?); done.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?); done.
Qed.

Lemma ev_not_others_sendon_groups sag e1 σ1 e2 σ2 :
  sendonEV_groups sag e1 σ1 e2 σ2 →
  (∀ lbl, ¬ allocEV lbl e1 σ1 e2 σ2) ∧
  (∀ sag', ¬ receiveonEV_groups sag' e1 σ1 e2 σ2).
Proof.
  destruct 1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq.
  split.
  - intros ? (?&?&?&?&?&?&?&?&?); done.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?); done.
Qed.

Lemma ev_not_others_receiveon_groups sag e1 σ1 e2 σ2 :
  receiveonEV_groups sag e1 σ1 e2 σ2 →
  (∀ sag', ¬ sendonEV_groups sag' e1 σ1 e2 σ2) ∧
  (∀ sag', ¬ allocEV sag' e1 σ1 e2 σ2).
Proof.
  destruct 1 as (?&?&?&?&?&?&?&?&?&?&?&?&?); simplify_eq.
  split.
  - intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?&?); done.
  - intros ? (?&?&?&?&?&?&?&?&?); done.
Qed.
