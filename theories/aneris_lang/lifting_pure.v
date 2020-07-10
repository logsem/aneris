From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth ofe.
From iris.base_logic Require Export own gen_heap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Export helpers lang notation tactics network resources_lemmas.
From stdpp Require Import fin_maps gmap.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply to_base_val in H
  | H : ground_lang.head_step ?e _ _ _ _ _ |- _ =>
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

Instance into_val_val n v : IntoVal ⟨n;Val v⟩ 〈n;v〉.
Proof. done. Qed.
Instance as_val_val n v : AsVal ⟨n;Val v⟩.
Proof. by exists 〈n;v〉. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; inv_head_step; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; inv_head_step;
       rewrite /to_val /is_Some /=; eexists; by
         match goal with
         | H: _ = _ |- _ => rewrite -H
         end
    ].

Instance binop_atomic n s op v1 v2 : Atomic s ⟨n;BinOp op (Val v1) (Val v2)⟩.
Proof. solve_atomic. Qed.
Instance alloc_atomic n s v : Atomic s ⟨n;Alloc (Val v)⟩.
Proof. solve_atomic. Qed.
Instance load_atomic n s v : Atomic s ⟨n;Load (Val v)⟩.
Proof. solve_atomic. Qed.
Instance store_atomic n s v1 v2 : Atomic s ⟨n;Store (Val v1) (Val v2)⟩.
Proof. solve_atomic. Qed.
Instance cmpxchg_atomic n s v0 v1 v2 : Atomic s ⟨n;CAS (Val v0) (Val v1) (Val v2)⟩.
Proof. solve_atomic. Qed.
Instance fork_atomic n s e : Atomic s ⟨n;Fork e⟩.
Proof. solve_atomic. Qed.
Instance skip_atomic n s : Atomic s ⟨n;Skip⟩.
Proof. solve_atomic. Qed.

Instance newsocket_atomic n v0 v1 v2 s : Atomic s ⟨n; NewSocket (Val v0) (Val v1) (Val v2)⟩.
Proof. solve_atomic. Qed.
Instance socketbind_atomic n v0 v1  s : Atomic s ⟨n; SocketBind (Val v0) (Val v1)⟩.
Proof. solve_atomic. Qed.
Instance sendto_atomic n v0 v1 v2 s : Atomic s ⟨n; SendTo (Val v0) (Val v1) (Val v2)⟩.
Proof. solve_atomic. Qed.
Instance receivefrom_atomic n v s : Atomic s ⟨n; ReceiveFrom (Val v)⟩.
Proof. solve_atomic. Qed.

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
                   | H : ground_lang.to_val _ = Some _ |- _ =>
                     rewrite ground_lang.to_of_val in H; simplify_eq
                   end);
  try by match goal with
         | H : socket_step _ _ _ _ _ _ _ _ _ |- _ =>
           inversion H
         end.
Local Ltac solve_pure_exec :=
  simplify_eq; rewrite /PureExec; intros; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Class AsRecV (v : ground_lang.val) (f x : binder) (erec : ground_lang.expr) :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Instance pure_rec f x (erec : ground_lang.expr) :
  PureExec True 1 ⟨n;Rec f x erec⟩ ⟨n;Val $ RecV f x erec⟩.
Proof. solve_pure_exec. Qed.
Instance pure_pairc (v1 v2 : ground_lang.val) :
  PureExec True 1 ⟨n;(Pair (Val v1) (Val v2))⟩ ⟨n;(Val $ PairV v1 v2)⟩.
Proof. solve_pure_exec. Qed.
Instance pure_injlc (v : ground_lang.val) :
  PureExec True 1 ⟨n;(InjL $ Val v)⟩ ⟨n;(Val $ InjLV v)⟩.
Proof. solve_pure_exec. Qed.
Instance pure_injrc (v : ground_lang.val) :
  PureExec True 1 ⟨n;(InjR $ Val v)⟩ ⟨n;(Val $ InjRV v)⟩.
Proof. solve_pure_exec. Qed.

Instance pure_beta f x erec (v1 v2 : ground_lang.val) `{!AsRecV v1 f x erec} :
  PureExec True 1 ⟨n;(App (Val v1) (Val v2))⟩ ⟨n;(subst' x v2 (subst' f v1 erec))⟩.
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 ⟨n;UnOp op (Val v)⟩ ⟨n;ground_lang.of_val v'⟩.
Proof. solve_pure_exec. Qed.

Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1
           ⟨n;BinOp op (Val v1) (Val v2)⟩ ⟨n;ground_lang.of_val v'⟩.
Proof. solve_pure_exec. Qed.

Instance pure_if_true e1 e2 : PureExec True 1 ⟨n;If (Val $ LitV $ LitBool true) e1 e2⟩ ⟨n;e1⟩.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True 1 ⟨n;If (Val $ LitV $ LitBool false) e1 e2⟩ ⟨n;e2⟩.
Proof. solve_pure_exec. Qed.

Instance pure_fst v1 v2  :
  PureExec True 1 ⟨n;Fst (PairV v1 v2)⟩ ⟨n;Val v1⟩.
Proof. solve_pure_exec. Qed.

Instance pure_snd v1 v2  :
  PureExec True 1 ⟨n;Snd (PairV v1 v2)⟩ ⟨n;Val v2⟩.
Proof. solve_pure_exec. Qed.

Instance pure_find_from v0 v1 n1 v2 v' :
  PureExec (index n1 v2 v0 = v' ∧ Z.of_nat n1 = v1) 1
           ⟨n;FindFrom (Val $ LitV $ LitString v0)
                       (Val $ LitV $ LitInt v1)
                       (Val $ LitV $ LitString v2)⟩
           ⟨n;ground_lang.of_val (option_nat_to_val v')⟩.
Proof. solve_pure_exec. Qed.

Instance pure_substring v0 v1 n1 v2 n2 v' :
  PureExec (substring n1 n2 v0 = v' ∧ Z.of_nat n1 = v1 ∧ Z.of_nat n2 = v2) 1
           ⟨n;Substring (LitV $ LitString v0) (LitV $ LitInt v1) (LitV $ LitInt v2)⟩
           ⟨n;ground_lang.of_val (LitV $ LitString v')⟩.
Proof. solve_pure_exec. Qed.

Instance pure_case_inl v e1 e2  :
  PureExec True 1 ⟨n;Case (Val $ InjLV v) e1 e2⟩ ⟨n;App e1 (Val v)⟩.
Proof. solve_pure_exec. Qed.

Instance pure_case_inr v e1 e2 :
  PureExec True 1 ⟨n;Case (Val $ InjRV v) e1 e2⟩ ⟨n;App e2 (Val v)⟩.
Proof. solve_pure_exec. Qed.

Instance pure_make_address v1 v2 :
  PureExec True 1
           ⟨n;MakeAddress (LitV (LitString v1)) (LitV (LitInt (v2)))⟩
           ⟨n;LitV (LitSocketAddress (SocketAddressInet v1 (Z.to_pos v2)))⟩.
Proof. solve_pure_exec. Qed.

Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.
