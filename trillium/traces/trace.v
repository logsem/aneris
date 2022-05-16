From trillium.prelude Require Export fixpoint classical.
Require Import iris.prelude.prelude.

Set Default Proof Using "Type".

Inductive finite_trace (A : Type) (L : Type) : Type :=
| trace_singleton (a : A)
| trace_extend (ft : finite_trace A L) (l : L) (a : A).

Global Arguments trace_singleton {_ _} _.
Global Arguments trace_extend {_ _} _ _ _.

Notation "'{tr[' a ]}" := (trace_singleton a) (at level 1, format "{tr[  a  ]}").
Notation "t ':tr[' l ']:' a" := (trace_extend t l a) (at level 60).

Section finite_trace.
  Context {A L : Type}.

  Implicit Types a : A.
  Implicit Types ft : finite_trace A L.
  Implicit Types l : list (L * A).

  Fixpoint trace_first (ft : finite_trace A L) : A :=
    match ft with
    | {tr[a]} => a
    | ft' :tr[_]: _ => trace_first ft'
    end.

  Definition trace_last (ft : finite_trace A L) : A :=
    match ft with
    | {tr[a]} => a
    | _ :tr[_]: a => a
    end.

  Definition trace_starts_in (ft : finite_trace A L) (a : A) : Prop :=
    trace_first ft = a.

  Definition trace_ends_in (ft : finite_trace A L) (a : A) : Prop :=
    trace_last ft = a.

  Fixpoint trace_append_list (ft : finite_trace A L) (l : list (L * A)) : finite_trace A L :=
    match l with
    | [] => ft
    | (ℓ, a) :: l' => trace_append_list (ft :tr[ℓ]: a) l'
    end.

  Infix "+trl+" := trace_append_list (at level 60).

  Definition trace_prefix (ft ft' : finite_trace A L) : Prop :=
    ∃ l, ft' = ft +trl+ l.

  Infix "`trace_prefix_of`" := trace_prefix (at level 70).

  (** instance and properties *)

  Lemma trace_starts_in_first ft : trace_starts_in ft (trace_first ft).
  Proof. done. Qed.

  Lemma trace_ends_in_last ft : trace_ends_in ft (trace_last ft).
  Proof. done. Qed.

  Lemma first_eq_trace_starts_in ft a : trace_starts_in ft a → trace_first ft = a.
  Proof. done. Qed.

  Lemma last_eq_trace_ends_in ft a: trace_ends_in ft a → trace_last ft = a.
  Proof. done. Qed.

  Lemma trace_singleton_starts_in c : trace_starts_in {tr[c]} c.
  Proof. done. Qed.

  Lemma trace_singleton_starts_in_inv c c' :
    trace_starts_in {tr[c']} c → c' = c.
  Proof. by inversion 1. Qed.

  Lemma trace_singleton_ends_in c : trace_ends_in {tr[c]} c.
  Proof. done. Qed.

  Lemma trace_singleton_ends_in_inv c c' :
    trace_ends_in {tr[c']} c → c' = c.
  Proof. by inversion 1. Qed.

  Lemma trace_starts_in_inj ft c c' :
   trace_starts_in ft c → trace_starts_in ft c' → c = c'.
  Proof. rewrite /trace_starts_in; intros ->; done. Qed.

  Lemma trace_ends_in_inj ft c c' :
   trace_ends_in ft c → trace_ends_in ft c' → c = c'.
  Proof. rewrite /trace_ends_in; intros ->; done. Qed.

  Definition trace_contract (ft: finite_trace A L) ℓ ft' : Prop :=
    ∃ a, ft = ft' :tr[ℓ]: a.

  Lemma trace_contract_of_extend ft ℓ a ft' ℓ' :
    trace_contract (ft :tr[ℓ]: a) ℓ' ft' → ft' = ft ∧ ℓ = ℓ'.
  Proof. intros (? & Heq); simplify_eq; done. Qed.

  Lemma not_trace_contract_singleton a ft ℓ:
    ¬ trace_contract {tr[a]} ℓ ft.
  Proof. intros (?&?); destruct ft; simplify_eq/=. Qed.

  Lemma trace_extend_starts_in ft a' ℓ a :
    trace_starts_in ft a' → trace_starts_in (ft :tr[ℓ]: a) a'.
  Proof. induction ft; auto. Qed.

  Lemma trace_extend_starts_in_inv ft a' ℓ a :
    trace_starts_in (ft :tr[ℓ]: a) a' → trace_starts_in ft a'.
  Proof. induction ft; auto. Qed.

  Lemma trace_extend_ends_in ft c ℓ : trace_ends_in (ft :tr[ℓ]: c) c.
  Proof. done. Qed.

  Lemma trace_does_end_in ft : ∃ a, trace_ends_in ft a.
  Proof. destruct ft; rewrite /trace_ends_in; eauto. Qed.

  Lemma trace_extend_neq_singleton ft a a' ℓ : ¬ ft :tr[ℓ]: a = {tr[ a' ]}.
  Proof. inversion 1. Qed.

  Lemma trace_prefix_append ft ft' :
    ft `trace_prefix_of` ft' → ∃ l, ft' = ft +trl+ l.
  Proof. done. Qed.

  Global Instance finite_trace_eq_dec `{!EqDecision A, EqDecision L} :
    EqDecision (finite_trace A L).
  Proof.
    intros ft ft'; rewrite /Decision.
    decide equality; try apply (_ : EqDecision A); apply (_ : EqDecision L).
  Qed.

  Lemma trace_append_list_assoc ft l l' :
    (ft +trl+ l) +trl+ l' = ft +trl+ (l ++ l').
  Proof.
    revert ft l'; induction l as [|[ℓ a] l IHl]; first done.
    intros ft l'; rewrite /= IHl; done.
  Qed.

  Lemma trace_appned_list_eq_singleton_inv ft l a:
    ft +trl+ l = {tr[a]} → ft = {tr[a]} ∧ l = [].
  Proof.
    intros Hl.
    revert ft Hl; induction l as [|[? b] l IHl]; first done.
    simpl; intros ft [Hft ?]%IHl.
    destruct ft; apply trace_extend_neq_singleton in Hft; done.
  Qed.

  Lemma trace_append_list_snoc ft l ℓ a : ft +trl+ (l ++ [(ℓ, a)]) = (ft +trl+ l) :tr[ℓ]: a.
  Proof. rewrite -trace_append_list_assoc; done. Qed.

  Lemma trace_extend_eq_trace_append_list ft ft' l ℓ a :
    ft :tr[ℓ]: a = ft' +trl+ l → (ft' = ft :tr[ℓ]: a ∧ l = []) ∨ (∃ l', l = l' ++ [(ℓ, a)]).
  Proof.
    revert ft a ft'.
    induction l as [|[? b] l IHl] using rev_ind; intros ft a ft'; first by left.
    rewrite trace_append_list_snoc.
    intros; simplify_eq; eauto.
  Qed.

  Lemma trace_append_list_eq_self_inv ft l: ft = ft +trl+ l → l = [].
  Proof.
    revert l; induction ft as [|ft IHft ℓ a]; intros l Hft.
    - symmetry in Hft.
      apply trace_appned_list_eq_singleton_inv in Hft as [_ ?]; done.
    - edestruct trace_extend_eq_trace_append_list as [[]|[l' Hl']];
        [done|done|].
      rewrite Hl' -trace_append_list_assoc /= in Hft.
      simplify_eq.
      apply (IHft ((ℓ, a) :: l')) in Hft; done.
  Qed.

  Global Instance trace_prefix_equivalence : PartialOrder trace_prefix.
  Proof.
    split; first split.
    - intros ft; exists []; done.
    - intros ft ft' ft'' [l ->] [l' ->].
      exists (l ++ l'); rewrite trace_append_list_assoc; done.
    - intros ft ft' [l Hl] [l' Hl'].
      rewrite Hl trace_append_list_assoc in Hl'.
      apply trace_append_list_eq_self_inv in Hl'.
      destruct l; done.
  Qed.

  Lemma trace_prefix_antisym ft ft' :
    ft `trace_prefix_of` ft' → ft' `trace_prefix_of` ft → ft = ft'.
  Proof. intros; eapply (anti_symm_iff (R := trace_prefix)); done. Qed.

  Lemma trace_append_list_first ft l : trace_first (ft +trl+ l) = trace_first ft.
  Proof.
    revert ft; induction l as [|[? a] l IHl]; intros ft; [|rewrite /= IHl]; done.
  Qed.

  Lemma trace_prefix_eq_firsts ft ft':
    ft `trace_prefix_of` ft' → trace_first ft = trace_first ft'.
  Proof. intros [? ->]. rewrite trace_append_list_first; done. Qed.

  Lemma trace_prefix_of_singleton ft a:
    trace_starts_in ft a → {tr[a]} `trace_prefix_of` ft.
  Proof.
    induction ft as [|ft IHft ℓ b].
    - intros ->; reflexivity.
    - intros Hfta%trace_extend_starts_in_inv.
      apply IHft in Hfta as [l Hl].
      exists (l ++ [(ℓ, b)]); rewrite -trace_append_list_assoc Hl; done.
  Qed.

  Lemma trace_prefix_trace_append ft ft' l :
    ft `trace_prefix_of` ft' → ft `trace_prefix_of` ft' +trl+ l.
  Proof.
    intros [l' ->]; exists (l' ++ l); rewrite trace_append_list_assoc; done.
  Qed.

  Lemma trace_prefix_trace_extend ft ft' ℓ a :
    ft `trace_prefix_of` ft' → ft `trace_prefix_of` ft' :tr[ℓ]: a.
  Proof.
    intros [l ->]; exists (l ++ [(ℓ, a)]); rewrite -trace_append_list_assoc; done.
  Qed.

  Lemma trace_append_prefix ft ft' l :
    ft +trl+ l `trace_prefix_of` ft' → ft `trace_prefix_of` ft'.
  Proof.
    intros [l' ->]; exists (l ++ l'); rewrite trace_append_list_assoc; done.
  Qed.

  Lemma trace_extend_prefix ft ft' ℓ a :
    ft :tr[ℓ]: a `trace_prefix_of` ft' → ft `trace_prefix_of` ft'.
  Proof. intros [l ->]; exists ((ℓ, a) :: l); done. Qed.

  Lemma trace_prefix_of_singleton_inv ft a:
    ft `trace_prefix_of` {tr[a]} → ft = {tr[a]}.
  Proof. intros []; eapply trace_appned_list_eq_singleton_inv; done. Qed.

  Lemma trace_prefix_of_extend ft ft' ℓ a :
    ft `trace_prefix_of` ft' :tr[ℓ]: a → ft = ft' :tr[ℓ]: a ∨ ft `trace_prefix_of` ft'.
  Proof.
    intros [l Hl].
    edestruct trace_extend_eq_trace_append_list as [[? ?]|[l' Hl']];
      [done|eauto|].
    rewrite Hl' trace_append_list_snoc in Hl; simplify_eq.
    right; apply trace_prefix_trace_append; done.
  Qed.

  Global Instance trace_prefix_dec `{!EqDecision A, EqDecision L} :
    RelDecision trace_prefix.
  Proof.
    intros ft ft'.
    revert ft; induction ft' as [a'|ft' IHft' ℓ' a']; intros ft.
    - destruct ft as [a|ft ℓ a].
      + destruct (decide (a = a')) as [->|]; first by left.
        right; intros Hpf%trace_prefix_eq_firsts; done.
      + right; intros Hft%trace_prefix_of_singleton_inv.
        apply trace_extend_neq_singleton in Hft; done.
    - destruct (decide (ft `trace_prefix_of` ft')) as [|Hnpf].
      + left; by apply trace_prefix_trace_extend.
      + destruct (decide (ft = ft' :tr[ℓ']: a')) as [->|]; first by left.
        right; intros [|]%trace_prefix_of_extend; done.
  Qed.

  Lemma trace_prefixes_related ft ft' ft'' :
    ft `trace_prefix_of` ft'' → ft' `trace_prefix_of` ft'' →
    ft `trace_prefix_of` ft' ∨ ft' `trace_prefix_of` ft.
  Proof.
    intros [l Hl] [l' Hl'].
    rewrite Hl in Hl'.
    clear Hl ft''.
    revert ft ft' l' Hl'.
    induction l as [|[ℓ a] l IHl]; simpl.
    - intros ??? ->; right; apply trace_prefix_trace_append; done.
    - intros ft ft' l' [Hpf|Hpf]%IHl.
      + left; eapply trace_extend_prefix; done.
      + apply trace_prefix_of_extend in Hpf as [->|]; [left|by right].
        apply trace_prefix_trace_extend; done.
  Qed.

  Lemma trace_last_of_append_list ft l oζ:
    exists oζ',
    ((oζ, trace_last ft) :: l) !! length l = Some (oζ', trace_last (ft +trl+ l)).
  Proof.
    induction l as [|[a ?] l IHl] using rev_ind; first by eexists.
    rewrite app_length /= trace_append_list_snoc /=.
    rewrite (lookup_app_r (_ :: _)) /=; last by simpl; lia.
    replace (length l + 1 - S (length l)) with 0 by lia.
    eexists. done.
  Qed.

  Lemma trace_last_of_append_list_map (ft : finite_trace A L) l:
    ((trace_last ft) :: map snd l) !! length l = Some (trace_last (ft +trl+ l)).
  Proof.
    induction l as [|[a ?] l IHl] using rev_ind; first by eexists.
    rewrite app_length /= trace_append_list_snoc /=.
    rewrite map_app (lookup_app_r (_ :: _)) /=; last by rewrite map_length /=; lia.
    rewrite map_length.
    replace (length l + 1 - S (length l)) with 0 by lia.
    done.
  Qed.

  Lemma trace_append_list_inj2 ft l l' :
    ft +trl+ l = ft +trl+ l' → l = l'.
  Proof.
    revert ft l'; induction l as [|[? a] l IHl] using rev_ind; intros ft l' Heq; simpl in *.
    - apply trace_append_list_eq_self_inv in Heq; done.
    - destruct l' as [|[? a'] l' _] using rev_ind; simpl in *.
      + symmetry in Heq.
        apply (trace_append_list_eq_self_inv) in Heq; done.
      + rewrite -!trace_append_list_assoc /= in Heq; simplify_eq.
        rewrite (IHl ft l'); auto.
  Qed.

End finite_trace.

(* Global Instance trace_fmap : FMap finite_trace := *)
(*   λ A B f, fix go (ft : finite_trace A) := *)
(*     match ft with *)
(*     | trace_singleton a => {tr[f a]} *)
(*     | trace_extend ft a => go ft :tr: f a *)
(*     end. *)

(* Fixpoint trace_fold {A B} (f : B → A → B) (b : B) (ft : finite_trace A) := *)
(*   match ft with *)
(*   | {tr[a]} => f b a *)
(*   | ft' :tr: a => f (trace_fold f b ft') a *)
(*   end. *)


Infix "+trl+" := trace_append_list (at level 60).
Infix "`trace_prefix_of`" := trace_prefix (at level 70).

(* Section fmap. *)
(*   Context {A B : Type} (f : A → B). *)
(*   Implicit Types ft : finite_trace A. *)

(*   Lemma trace_fmap_compose {C} (g : B → C) ft : *)
(*     g ∘ f <$> ft = g <$> (f <$> ft). *)
(*   Proof. induction ft; f_equal/=; auto. Qed. *)

(*   Lemma trace_fmap_singleton a : f <$> {tr[a]} = {tr[f a]}. *)
(*   Proof. reflexivity. Qed. *)

(*   Lemma trace_fmap_extend a ft : f <$> ft :tr: a = (f <$> ft) :tr: f a. *)
(*   Proof. reflexivity. Qed. *)

(*   Lemma trace_fmap_append_list ft l : *)
(*     f <$> ft +trl+ l = (f <$> ft) +trl+ (f <$> l). *)
(*   Proof. *)
(*     revert ft; induction l as [|a l IHl]; [done|]. *)
(*     intros ft'; rewrite /= IHl; done. *)
(*   Qed. *)

(*   Lemma trace_fmap_first ft : *)
(*     trace_first (f <$> ft) = f (trace_first ft). *)
(*   Proof. induction ft; [done|]. rewrite /= IHft //. Qed. *)

(*   Lemma trace_fmap_last ft : *)
(*     trace_last (f <$> ft) = f (trace_last ft). *)
(*   Proof. by destruct ft. Qed. *)

(*   Lemma trace_fmap_starts_in a ft : *)
(*     trace_starts_in ft a → trace_starts_in (f <$> ft) (f a). *)
(*   Proof. rewrite /trace_starts_in trace_fmap_first. by intros ->. Qed. *)

(*   Lemma trace_fmap_ends_in a ft : *)
(*     trace_ends_in ft a → trace_ends_in (f <$> ft) (f a). *)
(*   Proof. rewrite /trace_ends_in trace_fmap_last. by intros ->. Qed. *)

(*   Lemma trace_fmap_prefix ft ft' : *)
(*     ft `trace_prefix_of` ft' → (f <$> ft) `trace_prefix_of` (f <$> ft'). *)
(*   Proof. *)
(*     destruct 1 as [l Hl]. *)
(*     exists (f <$> l). rewrite Hl. *)
(*     apply trace_fmap_append_list. *)
(*   Qed. *)

(* End fmap. *)

(* Section trace_fold. *)
(*   Context {A B : Type}. *)

(*   Implicit Types ft : finite_trace A. *)
(*   Implicit Types f : B → A → B. *)

(*   Lemma trace_fold_singleton f b a : trace_fold f b {tr[a]} = f b a. *)
(*   Proof. done. Qed. *)

(*   Lemma trace_fold_extend f b ft a : trace_fold f b (ft :tr: a) = f (trace_fold f b ft) a. *)
(*   Proof. done. Qed. *)

(*   Lemma trace_fold_append_list f b ft l : *)
(*     trace_fold f b (ft +trl+ l) = fold_left f l (trace_fold f b ft). *)
(*   Proof. *)
(*     induction l as [|a l IHl] using rev_ind; first done. *)
(*     rewrite -trace_append_list_assoc fold_left_app /= IHl //. *)
(*   Qed. *)

(* End trace_fold. *)

(* Section trace_fold. *)
(*   Context {A B C : Type}. *)

(*   Implicit Types ft : finite_trace C. *)
(*   Implicit Types f : B → A → B. *)
(*   Implicit Types G : C → A. *)

(*   Lemma trace_fold_fmap g f b ft : trace_fold f b (g <$> ft) = trace_fold (λ b c, f b (g c)) b ft. *)
(*   Proof. *)
(*     induction ft as [|ft IHft a]; first done. *)
(*     rewrite trace_fmap_extend /= IHft //. *)
(*   Qed. *)

(* End trace_fold. *)

Inductive trace_steps {A L : Type} (R : A -> L -> A -> Prop) : finite_trace A L → Prop :=
| trace_steps_singleton x : trace_steps R {tr[x]}
| trace_steps_step ex x ℓ y :
    trace_ends_in ex x →
    R x ℓ y →
    trace_steps R ex →
    trace_steps R (ex :tr[ℓ]: y).

Inductive trace_steps2 {A B L1 L2 : Type} (R : A → B → L1 -> L2 -> A → B → Prop) : finite_trace A L1 → finite_trace B L2 → Prop :=
| trace_steps2_singleton x y : trace_steps2 R {tr[x]} {tr[y]}
| trace_steps2_step ex1 ex2 x1 y1 ℓ1 ℓ2 x2 y2 :
    trace_ends_in ex1 x1 →
    trace_ends_in ex2 y1 →
    R x1 y1 ℓ1 ℓ2 x2 y2 →
    trace_steps2 R ex1 ex2 →
    trace_steps2 R (ex1 :tr[ℓ1]: x2) (ex2 :tr[ℓ2]: y2).

Section trace_steps.
  Context {A L : Type} (R : A -> L -> A -> Prop).

  Lemma trace_steps_step_inv ex ℓ x:
    trace_steps R (ex :tr[ℓ]: x) →
    trace_steps R ex ∧
    ∃ y, trace_ends_in ex y ∧ R y ℓ x.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_steps_impl (R' : A -> L -> A -> Prop) :
    (∀ x ℓ y, R x ℓ y → R' x ℓ y) → ∀ ex, trace_steps R ex → trace_steps R' ex.
  Proof. intros HR ex Hex; induction Hex; econstructor; eauto. Qed.

  Lemma trace_steps_rtc x y :
    rtc (λ x y, ∃ ℓ, R x ℓ y) x y ↔ ∃ ex, trace_steps R ex ∧ trace_starts_in ex x ∧ trace_ends_in ex y.
  Proof.
    split.
    - apply (rtc_ind_r (λ z, ∃ ex, trace_steps R ex ∧ trace_starts_in ex x ∧ trace_ends_in ex z) x).
      + eexists {tr[ _ ]}; split_and!; [constructor|done|done].
      + intros ? ? ? [??] (? & ? & ? & ?).
        eexists (_ :tr[_]: _); split_and!; [|done|done].
        econstructor; eauto.
    - intros (ex & Hex & Hex1 & Hex2).
      revert x y Hex1 Hex2; induction Hex as [|? ? ? ? ? ? IHex IH]; intros z w Hex1 Hex2.
      + inversion Hex1; simplify_eq.
        inversion Hex2; simplify_eq.
        econstructor.
      + inversion Hex1; simplify_eq.
        inversion Hex2; simplify_eq.
        eapply rtc_r; last by eexists.
        apply IH; done.
  Qed.

  Lemma trace_steps_rtc_1  x y :
    rtc (λ x y, ∃ ℓ, R x ℓ y) x y → ∃ ex, trace_steps R ex ∧ trace_starts_in ex x ∧ trace_ends_in ex y.
  Proof. intros ?. by eapply trace_steps_rtc. Qed.

  Lemma trace_steps_rtc_2 ex :
    trace_steps R ex → rtc (λ x y, ∃ ℓ, R x ℓ y) (trace_first ex) (trace_last ex).
  Proof. intros ?. eapply trace_steps_rtc. eexists; done. Qed.
End trace_steps.

Section traces_step_binary.
  Context {A L : Type} (R : A -> A -> Prop).

  Notation Rb := (λ x (_ : L) y, R x y).

  Lemma trace_steps_step_inv_bin ex x ℓ:
    trace_steps Rb (ex :tr[ℓ]: x) →
    trace_steps Rb ex ∧
    ∃ y, trace_ends_in ex y ∧ R y x.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_steps_impl_bin (R' : relation A) :
    (∀ x y, R x y → R' x y) → ∀ (ex : finite_trace A L), trace_steps (λ x _ y, R x y) ex → trace_steps (λ x _ y, R' x y) ex.
  Proof. intros HR ex Hex; induction Hex; econstructor; eauto. Qed.

  Lemma trace_steps_rtc_bin `{Inhabited L} x y :
    rtc R x y ↔ ∃ ex, trace_steps Rb ex ∧ trace_starts_in ex x ∧ trace_ends_in ex y.
  Proof.
    split.
    - apply (rtc_ind_r (λ z, ∃ ex, trace_steps Rb ex ∧ trace_starts_in ex x ∧ trace_ends_in ex z) x).
      + eexists {tr[ _ ]}; split_and!; [constructor|done|done].
      + intros ? ? ? ? (? & ? & ? & ?).
        eexists (_ :tr[inhabitant]: _); split_and!; [|done|done].
        econstructor; eauto.
    - intros (ex & Hex & Hex1 & Hex2).
      revert x y Hex1 Hex2; induction Hex as [|? ? ? ? ? ? IHex IH]; intros z w Hex1 Hex2.
      + inversion Hex1; simplify_eq.
        inversion Hex2; simplify_eq.
        econstructor.
      + inversion Hex1; simplify_eq.
        inversion Hex2; simplify_eq.
        eapply rtc_r; last done.
        apply IH; done.
  Qed.

  Lemma trace_steps_rtc_1_bin  `{Inhabited L} x y :
    rtc R x y → ∃ ex, trace_steps Rb ex ∧ trace_starts_in ex x ∧ trace_ends_in ex y.
  Proof. intros ?. by eapply trace_steps_rtc_bin. Qed.

  Lemma trace_steps_rtc_2_bin `{Inhabited L} ex :
    trace_steps Rb ex → rtc R (trace_first ex) (trace_last ex).
  Proof. intros ?. eapply trace_steps_rtc_bin. eexists; done. Qed.

  Lemma trace_append_list_steps_rtc_bin (x y : A) (ex : finite_trace A L) (l : list (L * A)) :
    trace_ends_in ex x →
    trace_ends_in (ex +trl+ l) y →
    trace_steps (λ x _ y, R x y) (ex +trl+ l) →
    rtc R x y.
  Proof.
    revert ex x y; induction l as [|[? a] l IHl] using rev_ind ; simpl; intros ex x y Hx Hy Hts.
    - assert (x = y) as -> by by eapply trace_ends_in_inj; eauto.
      constructor.
    - rewrite -trace_append_list_assoc in Hy, Hts.
      simpl in Hts.
      apply trace_steps_step_inv in Hts as [Hts1 [z [Hts2 Htz3]]].
      apply last_eq_trace_ends_in in Hy; simplify_eq.
      eapply rtc_r; last apply Htz3.
      eapply IHl; eauto.
  Qed.

End traces_step_binary.

Section trace_steps_no_labels.
  Context {A : Type} (R : A -> A -> Prop).

  Lemma trace_steps_step_inv_nl (ex : finite_trace A ()) ℓ x:
    trace_steps (λ x _ y, R x y) (ex :tr[ℓ]: x) →
    trace_steps (λ x _ y, R x y) ex ∧
    ∃ y, trace_ends_in ex y ∧ R y x.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_steps_impl_nl (R' : A -> A -> Prop) :
    (∀ x y, R x y → R' x y) → ∀ (ex: finite_trace A ()), trace_steps (λ x _ y, R x y) ex → trace_steps (λ x _ y, R' x y) ex.
  Proof. intros HR ex Hex; induction Hex; econstructor; eauto. Qed.

  Lemma trace_steps_rtc_nl x y :
    rtc R x y ↔ ∃ (ex : finite_trace A ()), trace_steps (λ x _ y, R x y) ex ∧ trace_starts_in ex x ∧ trace_ends_in ex y.
  Proof.
    split.
    - apply (rtc_ind_r (λ z, ∃ ex, trace_steps (λ x _ y, R x y) ex ∧ trace_starts_in ex x ∧ trace_ends_in ex z) x).
      + eexists {tr[ _ ]}; split_and!; [constructor|done|done].
      + intros ? ? ? ? (? & ? & ? & ?).
        eexists (_ :tr[tt]: _); split_and!; [|done|done].
        econstructor; eauto.
    - intros (ex & Hex & Hex1 & Hex2).
      revert x y Hex1 Hex2; induction Hex as [|? ? ? ? ? ? IHex IH]; intros z w Hex1 Hex2.
      + inversion Hex1; simplify_eq.
        inversion Hex2; simplify_eq.
        econstructor.
      + inversion Hex1; simplify_eq.
        inversion Hex2; simplify_eq.
        eapply rtc_r; last by [].
        apply IH; done.
  Qed.

  Lemma trace_steps_rtc_1_nl  x y :
    rtc R x y → ∃ (ex : finite_trace A ()), trace_steps (λ x _ y, R x y) ex ∧ trace_starts_in ex x ∧ trace_ends_in ex y.
  Proof. intros ?. by eapply trace_steps_rtc_nl. Qed.

  Lemma trace_steps_rtc_2_nl (ex : finite_trace A ()) :
    trace_steps (λ x _ y, R x y) ex → rtc R (trace_first ex) (trace_last ex).
  Proof. intros ?. eapply trace_steps_rtc_nl. eexists; done. Qed.

  Lemma trace_append_list_steps_rtc_nl (x y : A) (ex : finite_trace A ()) (l : list (() * A)) :
    trace_ends_in ex x →
    trace_ends_in (ex +trl+ l) y →
    trace_steps (λ x _ y, R x y) (ex +trl+ l) →
    rtc R x y.
  Proof.
    revert ex x y; induction l as [|[? a] l IHl] using rev_ind ; simpl; intros ex x y Hx Hy Hts.
    - assert (x = y) as -> by by eapply trace_ends_in_inj; eauto.
      constructor.
    - rewrite -trace_append_list_assoc in Hy, Hts.
      simpl in Hts.
      apply trace_steps_step_inv_nl in Hts as [Hts1 [z [Hts2 Htz3]]].
      apply last_eq_trace_ends_in in Hy; simplify_eq.
      eapply rtc_r; last apply Htz3.
      eapply IHl; eauto.
  Qed.
End trace_steps_no_labels.

Section trace_steps2.
  Context {A B L1 L2 : Type} (R : A → B → L1 -> L2 -> A → B → Prop).

  Lemma trace_steps2_step_inv ex1 x ex2 y ℓ1 ℓ2:
    trace_steps2 R (ex1 :tr[ℓ1]: x) (ex2 :tr[ℓ2]: y) →
    trace_steps2 R ex1 ex2 ∧
    ∃ x' y', trace_ends_in ex1 x' ∧ trace_ends_in ex2 y' ∧ R x' y' ℓ1 ℓ2 x y.
  Proof. inversion 1; simplify_eq; eauto 10. Qed.

  Lemma trace_steps2_impl (R' : A → B -> L1 -> L2 -> A → B → Prop) :
    (∀ x1 y1 ℓ1 ℓ2 x2 y2, R x1 y1 ℓ1 ℓ2 x2 y2 → R' x1 y1 ℓ1 ℓ2 x2 y2) →
    ∀ ex ex', trace_steps2 R ex ex' → trace_steps2 R' ex ex'.
  Proof. intros HR ex ex' Hex; induction Hex; econstructor; eauto. Qed.

  Lemma trace_steps2_trace_steps (R1 : A -> L1 -> A -> Prop) (R2 : B -> L2 -> B -> Prop) :
    (∀ x1 y1 ℓ1 ℓ2 x2 y2, R x1 y1 ℓ1 ℓ2 x2 y2 → R1 x1 ℓ1 x2 ∧ R2 y1 ℓ2 y2) →
    ∀ ex ex', trace_steps2 R ex ex' → trace_steps R1 ex ∧ trace_steps R2 ex'.
  Proof.
    intros HR ex ex' Hexs.
    induction Hexs as [|?????????? []%HR ? []].
    - split; constructor.
    - split; econstructor; done.
  Qed.

End trace_steps2.
Section traces_forall.
  Context {A L : Type}.

  Inductive trace_forall (P : A → Prop) : finite_trace A L → Prop :=
  | TFA_singleton a : P a → trace_forall P {tr[a]}
  | TFA_extend tr a ℓ: trace_forall P tr → P a → trace_forall P (tr :tr[ℓ]: a).

  Lemma trace_forall_last P tr : trace_forall P tr → P (trace_last tr).
  Proof. inversion 1; done. Qed.

  Lemma trace_forall_first P tr : trace_forall P tr → P (trace_first tr).
  Proof. induction 1; done. Qed.

  Lemma trace_forall_extend_inv P tr a ℓ: trace_forall P (tr :tr[ℓ]: a) → trace_forall P tr ∧ P a.
  Proof. inversion 1; done. Qed.

End traces_forall.

Section traces_forall2.
  Context {A B L1 L2: Type}.

  Inductive trace_forall2 (P : A → B → Prop) : finite_trace A L1 → finite_trace B L2 → Prop :=
  | TFA2_singleton a b : P a b → trace_forall2 P {tr[a]} {tr[b]}
  | TFA2_extend tr tr' a b ℓ1 ℓ2 :
      trace_forall2 P tr tr' → P a b → trace_forall2 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b).

  Lemma trace_forall2_impl (P Q : A → B → Prop) tr tr' :
    (∀ x y, P x y → Q x y) → trace_forall2 P tr tr' → trace_forall2 Q tr tr'.
  Proof. intros HPQ; induction 1; constructor; auto. Qed.

  Lemma trace_forall2_last P tr tr' : trace_forall2 P tr tr' → P (trace_last tr) (trace_last tr').
  Proof. inversion 1; done. Qed.

  Lemma trace_forall2_first P tr tr' : trace_forall2 P tr tr' → P (trace_first tr) (trace_first tr').
  Proof. induction 1; done. Qed.

  Lemma trace_forall2_singleton_inv P a b : trace_forall2 P {tr[a]} {tr[b]} → P a b.
  Proof. inversion 1; done. Qed.

  Lemma trace_forall2_singleton_inv_l P tr' a :
    trace_forall2 P {tr[a]} tr' → ∃ b, tr' = {tr[b]} ∧ P a b.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_forall2_singleton_inv_r P tr b :
    trace_forall2 P tr {tr[b]} → ∃ a, tr = {tr[a]} ∧ P a b.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_forall2_extend_inv P tr tr' a b ℓ1 ℓ2:
    trace_forall2 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b) → trace_forall2 P tr tr' ∧ P a b.
  Proof. inversion 1; done. Qed.

  Lemma trace_forall2_extend_inv_l P tr tr' a ℓ1:
    trace_forall2 P (tr :tr[ℓ1]: a) tr' → ∃ b tr'' ℓ2, tr' = tr'' :tr[ℓ2]: b ∧ trace_forall2 P tr tr'' ∧ P a b.
  Proof. inversion 1; simplify_eq; eexists _, _. eauto. Qed.

  Lemma trace_forall2_extend_inv_r P tr tr' b ℓ2:
    trace_forall2 P tr (tr' :tr[ℓ2]: b) → ∃ a tr'' ℓ1, tr = tr'' :tr[ℓ1]: a ∧ trace_forall2 P tr'' tr' ∧ P a b.
  Proof. inversion 1; simplify_eq; eexists _, _; eauto. Qed.

End traces_forall2.

Section traces_forall3.
  Context {A B C L1 L2 L3: Type}.

  Inductive trace_forall3 (P : A → B → C → Prop) :
    finite_trace A L1 → finite_trace B L2 → finite_trace C L3 → Prop :=
  | TFA3_singleton a b c : P a b c → trace_forall3 P {tr[a]} {tr[b]} {tr[c]}
  | TFA3_extend tr tr' tr'' a b c ℓ1 ℓ2 ℓ3:
      trace_forall3 P tr tr' tr'' → P a b c → trace_forall3 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b) (tr'' :tr[ℓ3]: c).

  Lemma trace_forall3_impl (P Q : A → B → C → Prop) tr tr' tr'' :
    (∀ x y z, P x y z → Q x y z) → trace_forall3 P tr tr' tr'' → trace_forall3 Q tr tr' tr''.
  Proof. intros HPQ; induction 1; constructor; auto. Qed.

  Lemma trace_forall3_last P tr tr' tr'' :
    trace_forall3 P tr tr' tr'' → P (trace_last tr) (trace_last tr') (trace_last tr'').
  Proof. inversion 1; done. Qed.

  Lemma trace_forall3_first P tr tr' tr'' :
    trace_forall3 P tr tr' tr'' → P (trace_first tr) (trace_first tr') (trace_first tr'').
  Proof. induction 1; done. Qed.

  Lemma trace_forall3_singleton_inv P a b c : trace_forall3 P {tr[a]} {tr[b]} {tr[c]} → P a b c.
  Proof. inversion 1; done. Qed.

  Lemma trace_forall3_singleton_inv_l P a tr' tr'' :
    trace_forall3 P {tr[a]} tr' tr'' → ∃ b c, tr' = {tr[b]} ∧ tr'' = {tr[c]} ∧ P a b c.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_forall2_singleton_inv_m P tr b tr'' :
    trace_forall3 P tr {tr[b]} tr'' → ∃ a c, tr = {tr[a]} ∧ tr'' = {tr[c]} ∧ P a b c.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_forall3_singleton_inv_r P tr tr' c :
    trace_forall3 P tr tr' {tr[c]} → ∃ a b, tr = {tr[a]} ∧ tr' = {tr[b]} ∧ P a b c.
  Proof. inversion 1; eauto. Qed.

  Lemma trace_forall3_extend_inv P tr tr' tr'' a b c ℓ1 ℓ2 ℓ3:
    trace_forall3 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b) (tr'' :tr[ℓ3]: c) → trace_forall3 P tr tr' tr'' ∧ P a b c.
  Proof. inversion 1; done. Qed.

  Lemma trace_forall3_extend_inv_l P tr1 a tr2 tr3 ℓ1 :
    trace_forall3 P (tr1 :tr[ℓ1]: a) tr2 tr3 →
    ∃ b tr2' c tr3' ℓ2 ℓ3, tr2 = tr2' :tr[ℓ2]: b ∧ tr3 = tr3' :tr[ℓ3]: c ∧ trace_forall3 P tr1 tr2' tr3' ∧ P a b c.
  Proof. inversion 1; eauto 10. Qed.

  Lemma trace_forall3_extend_inv_m P tr1 tr2 b tr3 ℓ2 :
    trace_forall3 P tr1 (tr2 :tr[ℓ2]: b) tr3 →
    ∃ a tr1' c tr3' ℓ1 ℓ3, tr1 = tr1' :tr[ℓ1]: a ∧ tr3 = tr3' :tr[ℓ3]: c ∧ trace_forall3 P tr1' tr2 tr3' ∧ P a b c.
  Proof. inversion 1; eauto 10. Qed.

  Lemma trace_forall3_extend_inv_r P tr1 tr2 tr3 c ℓ3 :
    trace_forall3 P tr1 tr2 (tr3 :tr[ℓ3]: c) →
    ∃ a tr1' b tr2' ℓ1 ℓ2, tr1 = tr1' :tr[ℓ1]: a ∧ tr2 = tr2' :tr[ℓ2]: b ∧ trace_forall3 P tr1' tr2' tr3 ∧ P a b c.
  Proof. inversion 1; eauto 10. Qed.

End traces_forall3.

Section trace_length_lookup.
  Context {A L : Type}.

  Implicit Types a : A.
  Implicit Types ft : finite_trace A L.

  Fixpoint trace_length {A} (ft : finite_trace A L) : nat :=
    match ft with
    | {tr[_]} => 1
    | ft' :tr[_]: _ => S (trace_length ft')
    end.

  Global Instance trace_lookup {A} : Lookup nat A (finite_trace A L) :=
    (fix go (n : nat) (ft : finite_trace A L) {struct ft} :=
       match ft with
       | {tr[a]} =>
         match n with
         | O => Some a
         | _ => None
         end
       | ft' :tr[_]: a =>
         if (bool_decide (trace_length ft' = n)) then Some a else go n ft'
       end).

  Lemma trace_lookup_lt_Some ft i : is_Some (ft !! i) ↔ i < trace_length ft.
  Proof.
    revert i; induction ft as [a|ft IHft ℓ a]; intros i; simpl.
    - rewrite -not_eq_None_Some; destruct i; simpl.
      + split; [lia|done].
      + split; [done|lia].
    - rewrite /lookup /trace_lookup /=.
      destruct (decide (trace_length ft = i)).
      + rewrite bool_decide_eq_true_2; last done.
        split; [lia|by eauto].
      + rewrite bool_decide_eq_false_2; last done.
        rewrite IHft; lia.
  Qed.

  Lemma trace_length_at_least ft : 1 ≤ trace_length ft.
  Proof. destruct ft; simpl; lia. Qed.

  Lemma trace_lookup_lt_Some_1 ft i a : ft !! i = Some a → i < trace_length ft.
  Proof. rewrite -trace_lookup_lt_Some; eauto. Qed.

  Lemma trace_lookup_lt_Some_2 ft i : i < trace_length ft → is_Some (ft !! i).
  Proof. apply trace_lookup_lt_Some. Qed.

  Lemma trace_lookup_extend ft a i ℓ : i = trace_length ft → (ft :tr[ℓ]: a) !! i = Some a.
  Proof. intros ->; rewrite /lookup /= bool_decide_eq_true_2; done. Qed.

  Lemma trace_lookup_extend_lt ft a i ℓ : i < trace_length ft → (ft :tr[ℓ]: a) !! i = ft !! i.
  Proof. intros ?; rewrite /lookup /= bool_decide_eq_false_2; auto with lia. Qed.

  Lemma trace_lookup_singelton a i : {tr[a]} !! i = Some a ↔ i = 0.
  Proof. destruct i; simpl; split; by auto with lia. Qed.

  Lemma trace_lookup_singelton_1 a i b : {tr[a]} !! i = Some b → i = 0 ∧ b = a.
  Proof. destruct i; simpl; split; simplify_eq; done. Qed.

  Lemma trace_lookup_singelton_2 a : {tr[a]} !! 0 = Some a.
  Proof. rewrite trace_lookup_singelton; done. Qed.

  Lemma trace_lookup_first ft : ft !! 0 = Some (trace_first ft).
  Proof.
    induction ft; first done.
    pose proof (trace_length_at_least ft).
    rewrite /lookup /= bool_decide_eq_false_2; auto with lia.
  Qed.

  Lemma trace_lookup_last ft i : S i = trace_length ft → ft !! i = Some (trace_last ft).
  Proof.
    destruct ft; simpl; intros ?.
    - assert (i = 0) as -> by lia.
      rewrite trace_lookup_first; done.
    - rewrite /lookup /= bool_decide_eq_true_2; auto with lia.
  Qed.


  Lemma trace_lookup_append_list ft l i : i < trace_length ft → (ft +trl+ l) !! i = ft !! i.
  Proof.
    revert ft i; induction l as [|[? a] l IHl]; intros ft i Hi; first done.
    rewrite IHl; last by simpl; lia.
    rewrite trace_lookup_extend_lt; done.
  Qed.

  Lemma trace_lookup_append_list_inv ft i a :
    ft !! i = Some a → ∃ ft' l, ft = ft' +trl+ l ∧ S i = trace_length ft'.
  Proof.
    revert i a; induction ft as [b|ft IHft ℓ b] ; intros i a Hlu.
    - apply trace_lookup_singelton_1 in Hlu as [-> ->].
      eexists {tr[_]}, []; done.
    - destruct (decide (i = trace_length ft)) as [->|].
      + rewrite trace_lookup_extend in Hlu; last done.
        simplify_eq.
        eexists _, []; split; done.
      + pose proof (trace_lookup_lt_Some_1 _ _ _ Hlu).
        rewrite trace_lookup_extend_lt in Hlu; last by simpl in *; lia.
        apply IHft in Hlu as (ft' & l & -> & Hli).
        eexists ft', (l ++ [(ℓ, b)]).
        rewrite -trace_append_list_assoc //=.
  Qed.

  Lemma trace_steps_append_list_inv (R : A → L -> A → Prop) ft l :
    trace_steps R (ft +trl+ l) → trace_steps R ft.
  Proof.
    revert ft; induction l as [|[??] l IHl] using rev_ind; intros ft Hftl; first done.
    apply IHl.
    rewrite -trace_append_list_assoc /= in Hftl.
    eapply trace_steps_step_inv; done.
  Qed.

  Lemma trace_steps_lookup (R : A → A → Prop) ft :
    trace_steps (λ x _ y, R x y) ft → ∀ i j a b, i ≤ j → ft !! i = Some a → ft !! j = Some b → rtc R a b.
  Proof.
    intros Hft i j a b Hij Ha Hb.
    pose proof (trace_lookup_append_list_inv _ _ _ Hb) as (ft' & l & -> & Hj).
    rewrite trace_lookup_append_list in Hb; last lia.
    rewrite trace_lookup_append_list in Ha; last lia.
    apply trace_steps_append_list_inv in Hft.
    pose proof (trace_lookup_append_list_inv _ _ _ Ha) as (ft'' & l' & -> & Hi).
    rewrite trace_lookup_append_list in Ha; last lia.
    rewrite trace_lookup_last in Ha; last done.
    rewrite trace_lookup_last in Hb; last done.
    simplify_eq.
    eapply trace_append_list_steps_rtc_bin; eauto using trace_ends_in_last.
  Qed.


End trace_length_lookup.
