Require Import Coq.Strings.Ascii.
From aneris.aneris_lang Require Export network.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Export ofe gset.
From stdpp Require Export strings.
From stdpp Require Import gmap fin pretty binders.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module base_lang.
Open Scope Z_scope.

Import Network.

(** Expressions and vals. *)
Definition loc := positive. (* Really, any countable type. *)

Inductive base_lit : Set :=
| LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc)
| LitString (s : string)
| LitAddressFamily (a : address_family)
| LitSocketType (t : socket_type) | LitProtocol (p : protocol)
| LitSocket (s : socket_handle) | LitSocketAddress (s : socket_address).
Inductive un_op : Set :=
| NegOp | MinusUnOp | StringOfInt | IntOfString | StringLength.
Inductive bin_op : Set :=
| PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
| AndOp | OrOp | XorOp (* Bitwise *)
| ShiftLOp | ShiftROp (* Shifts *)
| LeOp | LtOp | EqOp (* Relations *)
| StringApp.

Inductive expr :=
(* Values *)
| Val (v : val)
(* Base lambda calculus *)
| Var (x : string)
| Rec (f x : binder) (e : expr)
| App (e1 e2 : expr)
(* Base types and their operations *)
| UnOp (op : un_op) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| If (e0 e1 e2 : expr)
| FindFrom (e0 e1 e2 : expr)
| Substring (e0 e1 e2 : expr)
(* Products *)
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
(* Sums *)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : expr) (e2 : expr)
(* Node-local concurrency *)
| Fork (e : expr)
(* Heap *)
| Alloc (e : expr)
| Load (e : expr)
| Store (e1 : expr) (e2 : expr)
| CAS (e0 : expr) (e1 : expr) (e2 : expr)
(* Sockets/Network *)
| MakeAddress (e1 : expr) (e2 : expr)
| NewSocket (e1 : expr) (e2 : expr) (e3 : expr)
| SocketBind (e1 : expr) (e2 : expr)
| SendTo (e1 : expr) (e2 : expr) (e3 : expr)
| ReceiveFrom (e1 : expr)
| Start (ip : base_lit) (e : expr)
with val :=
| LitV (l : base_lit)
| RecV (f x : binder) (e : expr)
| PairV (v1 v2 : val)
| InjLV (v : val)
| InjRV (v : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** The state: heaps of vals. *)
Definition state := gmap loc val.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
      fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
        match e1, e2 with
        | Val v, Val v' => cast_if (decide (v = v'))
        | Var x, Var x' => cast_if (decide (x = x'))
        | Rec f x e, Rec f' x' e' =>
          cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
        | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
        | BinOp o e1 e2, BinOp o' e1' e2' =>
          cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
        | If e0 e1 e2, If e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | FindFrom e0 e1 e2, FindFrom e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | Substring e0 e1 e2, Substring e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | Pair e1 e2, Pair e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | Fst e, Fst e' => cast_if (decide (e = e'))
        | Snd e, Snd e' => cast_if (decide (e = e'))
        | InjL e, InjL e' => cast_if (decide (e = e'))
        | InjR e, InjR e' => cast_if (decide (e = e'))
        | Case e0 e1 e2, Case e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | Fork e, Fork e' => cast_if (decide (e = e'))
        | Alloc e, Alloc e' => cast_if (decide (e = e'))
        | Load e, Load e' => cast_if (decide (e = e'))
        | Store e1 e2, Store e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | CAS e0 e1 e2, CAS e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | MakeAddress e1 e2, MakeAddress e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | NewSocket e0 e1 e2, NewSocket e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | SocketBind e1 e2, SocketBind e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | SendTo e0 e1 e2, SendTo e0' e1' e2' =>
          cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | ReceiveFrom e, ReceiveFrom e' => cast_if (decide (e = e'))
        | Start e0 e1, Start e0' e1' =>
          cast_if_and (decide (e0 = e0')) (decide (e1 = e1'))
        | _, _ => right _
        end
      with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
      match v1, v2 with
        | LitV l, LitV l' => cast_if (decide (l = l'))
        | RecV f x e, RecV f' x' e' =>
          cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
        | PairV e1 e2, PairV e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | InjLV e, InjLV e' => cast_if (decide (e = e'))
        | InjRV e, InjRV e' => cast_if (decide (e = e'))
        | _, _ => right _
      end
        for go); try (clear go gov; abstract intuition congruence).
Defined.
Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
  refine (inj_countable' (λ l, match l with
   | LitInt n => inl (inl (inl (inl n)))
   | LitBool b => inl (inl (inl (inr b)))
   | LitUnit => inl (inl (inr (inl ())))
   | LitLoc l => inl (inl (inr (inr l)))
   | LitString s => inl (inr (inl (inl s)))
   | LitAddressFamily a => inl (inr (inl (inr a)))
   | LitSocketType t => inl (inr (inr (inl t)))
   | LitProtocol p => inl (inr (inr (inr p)))
   | LitSocket s => inr (inl (inl (inl s)))
   | LitSocketAddress a => inr (inl (inl (inr a)))
   end) (λ l, match l with
   | inl (inl (inl (inl n))) => LitInt n
   | inl (inl (inl (inr b))) => LitBool b
   | inl (inl (inr (inl ()))) => LitUnit
   | inl (inl (inr (inr l))) => LitLoc l
   | inl (inr (inl (inl s))) => LitString s
   | inl (inr (inl (inr a))) => LitAddressFamily a
   | inl (inr (inr (inl t))) => LitSocketType t
   | inl (inr (inr (inr p))) => LitProtocol p
   | inr (inl (inl (inl s))) => LitSocket s
   | inr (inl (inl (inr a))) => LitSocketAddress a
   | inr (inl (inr (inl ()))) => LitUnit
   | inr (inl (inr (inr ()))) => LitUnit
   | inr (inr (inl (inl ()))) => LitUnit
   | inr (inr (inl (inr ()))) => LitUnit
   | inr (inr (inr (inl ()))) => LitUnit
   | inr (inr (inr (inr ()))) => LitUnit
   end)  _); by intros [].
Qed.

Global Instance un_op_countable : Countable un_op.
Proof.
  refine (inj_countable' (λ op, match op with
   | NegOp => 0
   | MinusUnOp => 1
   | StringOfInt => 2
   | IntOfString => 3
   | StringLength => 4
   end) (λ n, match n with
   | 0 => NegOp
   | 1 => MinusUnOp
   | 2 => StringOfInt
   | 3 => IntOfString
   | _ => StringLength
   end) _); by intros [].
Qed.

Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable' (λ op, match op with
   | PlusOp => 0
   | MinusOp => 1
   | MultOp => 2
   | QuotOp => 3
   | RemOp => 4
   | AndOp => 5
   | OrOp => 6
   | XorOp => 7
   | ShiftLOp => 8
   | ShiftROp => 9
   | LeOp => 10
   | LtOp => 11
   | EqOp => 12
   | StringApp => 13
   end) (λ n, match n with
   | 0 => PlusOp
   | 1 => MinusOp
   | 2 => MultOp
   | 3 => QuotOp
   | 4 => RemOp
   | 5 => AndOp
   | 6 => OrOp
   | 7 => XorOp
   | 8 => ShiftLOp
   | 9 => ShiftROp
   | 10 => LeOp
   | 11 => LtOp
   | 12 => EqOp
   | _ => StringApp
   end) _); by intros [].
Qed.

Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr op))); go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
     | Fork e => GenNode 12 [go e]
     | Alloc e => GenNode 13 [go e]
     | Load e => GenNode 14 [go e]
     | Store e1 e2 => GenNode 15 [go e1; go e2]
     | MakeAddress e1 e2 => GenNode 16 [go e1; go e2]
     | NewSocket e1 e2 e3 => GenNode 17 [go e1; go e2; go e3]
     | SocketBind e1 e2 => GenNode 18 [go e1; go e2]
     | SendTo e1 e2 e3 => GenNode 19 [go e1; go e2; go e3]
     | ReceiveFrom e => GenNode 20 [go e]
     | Start i e => GenNode 21 [
                                  GenLeaf(inr (inl i));
                                  go e]
     | FindFrom e1 e2 e3 => GenNode 22 [go e1; go e2; go e3]
     | Substring e1 e2 e3 => GenNode 23 [go e1; go e2; go e3]
     | CAS e1 e2 e3 => GenNode 24 [go e1; go e2; go e3]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 12 [e] => Fork (go e)
     | GenNode 13 [e] => Alloc (go e)
     | GenNode 14 [e] => Load (go e)
     | GenNode 15 [e1; e2] => Store (go e1) (go e2)
     | GenNode 16 [e1; e2] => MakeAddress (go e1) (go e2)
     | GenNode 17 [e1; e2; e3] => NewSocket (go e1) (go e2) (go e3)
     | GenNode 18 [e1; e2] => SocketBind (go e1) (go e2)
     | GenNode 19 [e1; e2; e3] => SendTo (go e1) (go e2) (go e3)
     | GenNode 20 [e] => ReceiveFrom (go e)
     | GenNode 21 [
                   GenLeaf (inr (inl i)); e2] => Start i (go e2)
     | GenNode 22 [e1; e2; e3] => FindFrom (go e1) (go e2) (go e3)
     | GenNode 23 [e1; e2; e3] => Substring (go e1) (go e2) (go e3)
     | GenNode 24 [e1; e2; e3] => CAS (go e1) (go e2) (go e3)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e; simpl; f_equal; [exact (gov _) | done..].
 - destruct v; by f_equal.
Qed.

Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Definition stateC := leibnizO state.
Definition valC := leibnizO val.
Definition exprC := leibnizO expr.

(** Evaluation contexts *)
Inductive ectx_item :=
| AppLCtx (v2 : val)
| AppRCtx (e1 : expr)
| UnOpCtx (op : un_op)
| BinOpLCtx (op : bin_op) (v2 : val)
| BinOpRCtx (op : bin_op) (e1 : expr)
| IfCtx (e1 e2 : expr)
| FindFromLCtx (v1 v2 : val)
| FindFromMCtx (e0 : expr) (v2 : val)
| FindFromRCtx (e0 e1 : expr)
| SubstringLCtx (v1 v2 : val)
| SubstringMCtx (e0 : expr) (v2 : val)
| SubstringRCtx (e0 e1 : expr)
| PairLCtx (v2 : val)
| PairRCtx (e1 : expr)
| FstCtx
| SndCtx
| InjLCtx
| InjRCtx
| CaseCtx (e1 : expr) (e2 : expr)
| AllocCtx
| LoadCtx
| StoreLCtx (v2 : val)
| StoreRCtx (e1 : expr)
| CasLCtx (v1 v2 : val)
| CasMCtx (e0 : expr) (v2 : val)
| CasRCtx (e0 e1 : expr)
| MakeAddressLCtx (v2 : val)
| MakeAddressRCtx (e1 : expr)
| NewSocketLCtx (v1 v2 : val)
| NewSocketMCtx (e0 : expr) (v2 : val)
| NewSocketRCtx (e0 e1 : expr)
| SocketBindLCtx (v2 : val)
| SocketBindRCtx (e1 : expr)
| SendToLCtx (v1 v2 : val)
| SendToMCtx (e0 : expr) (v2 : val)
| SendToRCtx (e0 e1 : expr)
| ReceiveFromCtx
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (Val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | FindFromLCtx v1 v2 => FindFrom e (Val v1) (Val v2)
  | FindFromMCtx e0 v2 => FindFrom e0 e (Val v2)
  | FindFromRCtx e0 e1 => FindFrom e0 e1 e
  | SubstringLCtx v1 v2 => Substring e (Val v1) (Val v2)
  | SubstringMCtx e0 v2 => Substring e0 e (Val v2)
  | SubstringRCtx e0 e1 => Substring e0 e1 e
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocCtx => Alloc e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | CasLCtx v1 v2 => CAS e (Val v1) (Val v2)
  | CasMCtx e0 v2 => CAS e0 e (Val v2)
  | CasRCtx e0 e1 => CAS e0 e1 e
  | MakeAddressLCtx v2 => MakeAddress e (Val v2)
  | MakeAddressRCtx e1 => MakeAddress e1 e
  | NewSocketLCtx v1 v2 => NewSocket e (Val v1) (Val v2)
  | NewSocketMCtx e0 v2 => NewSocket e0 e (Val v2)
  | NewSocketRCtx e0 e1 => NewSocket e0 e1 e
  | SocketBindLCtx v2 => SocketBind e (Val v2)
  | SocketBindRCtx e1 => SocketBind e1 e
  | SendToLCtx v1 v2 => SendTo e (Val v1) (Val v2)
  | SendToMCtx e0 v2 => SendTo e0 e (Val v2)
  | SendToRCtx e0 e1 => SendTo e0 e1 e
  | ReceiveFromCtx => ReceiveFrom e
  end.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
    Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | FindFrom e0 e1 e2 => FindFrom (subst x v e0) (subst x v e1) (subst x v e2)
  | Substring e0 e1 e2 => Substring (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | Alloc e => Alloc (subst x v e)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | CAS e0 e1 e2 => CAS (subst x v e0) (subst x v e1) (subst x v e2)
  | MakeAddress e1 e2 => MakeAddress (subst x v e1) (subst x v e2)
  | NewSocket e0 e1 e2 =>
    NewSocket (subst x v e0) (subst x v e1) (subst x v e2)
  | SocketBind e1 e2 => SocketBind (subst x v e1) (subst x v e2)
  | SendTo e0 e1 e2 => SendTo (subst x v e0) (subst x v e1) (subst x v e2)
  | ReceiveFrom e => ReceiveFrom (subst x v e)
  | Start i e => Start i (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

Definition StringOfZ (x : Z) :=
  match x with
  | 0 => "0"
  | Z.pos x0 => pretty (N.pos x0)
  | Z.neg x0 => "-" +:+ pretty (N.pos x0)
  end.

Definition ZOfAscii (c : Ascii.ascii) : option N :=
  match c with
  | "0"%char => Some 0%N
  | "1"%char => Some 1%N
  | "2"%char => Some 2%N
  | "3"%char => Some 3%N
  | "4"%char => Some 4%N
  | "5"%char => Some 5%N
  | "6"%char => Some 6%N
  | "7"%char => Some 7%N
  | "8"%char => Some 8%N
  | "9"%char => Some 9%N
  | _ => None
  end.

Fixpoint ZOfString' (x : string) (ac : N) : option N :=
  match x with
  | EmptyString => Some ac
  | String c x' =>
    match ZOfAscii c with
      None => None
    | Some d => (ZOfString' x' ((ac * 10) + d)%N)
    end
  end.

Definition ZOfString (x : string) : option Z:=
  match x with
  | EmptyString => None
  | String "-"%char x' =>
    match (ZOfString' x' 0) with
    | Some z => Some (- (Z.of_N z))
    | None => None
    end
  | String c x' =>
    match (ZOfString' x 0) with
    | Some z => Some (Z.of_N z)
    | None => None
    end
  end.

Lemma lt_acc (n : N) : Acc N.lt n.
Proof.
  induction n using N.peano_ind; first by constructor; intros; lia.
  constructor => m Hlt.
  destruct (decide (m < n)%N); first by apply IHn.
    by replace m with n by lia.
Qed.

Lemma ZOfAscii_pretty x :
  (x < 10)%N →
  ZOfAscii (pretty_N_char x) = Some x.
Proof.
  intros Hlt.
  inversion Hlt as [Hlt']; cbv in Hlt'.
  destruct x as [|p]; first done.
  destruct p as [[[[]|[]|]|[[]|[]|]|]|[[[]|[]|]|[[]|[]|]|]|]; try done.
Qed.

Lemma ZOfString'_app s s' k :
  match ZOfString' s k with
  | None => ZOfString' (s +:+ s') k = None
  | Some m => ZOfString' (s +:+ s') k = ZOfString' s' m
  end.
Proof.
  revert s' k; induction s.
  - induction s'; simpl; first done.
    intros k.
    destruct a as [[] [] [] [] [] [] [] []]; simpl; auto;
      match goal with
        |- match ZOfString' s' ?A with _ => _ end =>
        specialize (IHs' A);
          destruct (ZOfString' s' A); trivial
      end.
  - intros s' k; rewrite /= -/append.
    destruct a as [[] [] [] [] [] [] [] []]; simpl; auto;
      match goal with
        |- match ZOfString' s ?A with _ => _ end =>
        specialize (IHs s' A);
          destruct (ZOfString' s (k * 10 + 7)); auto
      end.
Qed.

Global Instance append_assoc : Assoc eq append.
Proof.
  intros x.
  induction x.
  - induction y; auto with f_equal.
  - intros y z.
    rewrite /append -/append IHx. f_equal.
Qed.

Lemma pretty_N_go_app m s :
  (0 < m)%N → pretty_N_go m s = (pretty_N_go m "") +:+ s.
Proof.
  intros Hlt. revert s.
  induction (lt_acc m) as [? ? IH] => s.
  rewrite !(pretty_N_go_step x) //.
  destruct (decide (x < 10)%N).
  - rewrite N.div_small // pretty_N_go_0 /=.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    pose proof (IH _ Hltdv Hdvp) as IH'.
    rewrite (IH' (String (pretty_N_char (x `mod` 10)) "")).
    rewrite IH'; simpl.
      by rewrite -assoc.
Qed.

Lemma ZOfString'_inv (n : nat) : ZOfString' (StringOfZ n) 0 = Some (N.of_nat n).
Proof.
  destruct n; first done; simpl.
  unfold pretty, pretty_N.
  remember (N.pos (Pos.of_succ_nat n)) as m.
  replace (S n) with (N.to_nat m); last first.
  { by rewrite Heqm positive_N_nat SuccNat2Pos.id_succ. }
  assert (Hmlt : (0 < m)%N) by lia.
  clear dependent n.
  induction (lt_acc m) as [? ? IH].
  rewrite pretty_N_go_step; last done.
  destruct (decide (x < 10)%N).
  - rewrite N.mod_small //.
    rewrite N.div_small // pretty_N_go_0 /= ZOfAscii_pretty //.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    rewrite pretty_N_go_app //.
    pose proof (ZOfString'_app
                  (pretty_N_go (x `div` 10) "")
                  (String (pretty_N_char (x `mod` 10)) "") 0) as Hlp.
    rewrite (IH _ Hltdv Hdvp) in Hlp.
    rewrite Hlp.
    rewrite /= ZOfAscii_pretty; last by apply N.mod_lt.
    replace (x `div` 10 * 10)%N with (10 * x `div` 10)%N by lia.
    rewrite -N.div_mod' //.
Qed.

Lemma pretty_N_go_nnil m s :
  (0 < m)%N → pretty_N_go m s ≠ "".
Proof.
  intros Hlt. revert s.
  induction (lt_acc m) as [? ? IH] => s.
  rewrite !(pretty_N_go_step x) //.
  destruct (decide (x < 10)%N).
  - rewrite N.div_small // pretty_N_go_0 /=.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    apply (IH _ Hltdv Hdvp).
Qed.

Lemma pretty_N_go_pos_nneg m s s':
  (0 < m)%N → pretty_N_go m s ≠ String "-" s'.
Proof.
  intros Hlt. revert s.
  induction (lt_acc m) as [? ? IH] => s.
  rewrite !(pretty_N_go_step x) //.
  destruct (decide (x < 10)%N).
  - rewrite N.div_small // pretty_N_go_0 /=.
    destruct x as [|p]; first done.
    destruct p as [[[[]|[]|]|[[]|[]|]|]|[[[]|[]|]|[[]|[]|]|]|]; done.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    apply (IH _ Hltdv Hdvp).
Qed.

Lemma StringOfZ_nnil m : StringOfZ m ≠ "".
Proof.
  unfold StringOfZ; simpl.
  destruct m; auto.
  apply pretty_N_go_nnil; lia.
Qed.

Lemma ZOfString_inv (n : Z) : ZOfString (StringOfZ n) = Some n.
Proof.
  unfold ZOfString.
  destruct (StringOfZ n) eqn:Heq;
    first by exfalso; eapply StringOfZ_nnil; eauto.
  destruct n as [|p|p] eqn:Heqn.
  - destruct a as [[] [] [] [] [] [] [] []]; try done.
    rewrite -?Heq //.
  - rewrite -?Heq.
    pose proof (ZOfString'_inv (Pos.to_nat p)) as HZSi.
    rewrite positive_nat_Z in HZSi.
    rewrite HZSi nat_N_Z positive_nat_Z.
    destruct a as [[] [] [] [] [] [] [] []]; auto.
    exfalso; eapply pretty_N_go_pos_nneg; eauto; lia.
  - simpl in Heq.
    assert (0 < 1)%nat as Hneq by lia.
    pose proof (append_correct1 "-" (pretty (N.pos p)) 0 Hneq) as Hf;
      simpl in Heq.
    rewrite Heq in Hf; inversion Hf; subst.
    rewrite -(@string_app_inj "-" (pretty (N.pos p)) s Heq).
    pose proof (ZOfString'_inv (Pos.to_nat p)) as HZSi.
    rewrite positive_nat_Z in HZSi.
      by rewrite HZSi nat_N_Z positive_nat_Z.
Qed.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | StringOfInt, LitV (LitInt n) => Some $ LitV $ LitString (StringOfZ n)
  | IntOfString, LitV (LitString s) =>
    match ZOfString s with
      Some z => Some $ InjRV $ LitV (LitInt z)
    | None => Some $ InjLV (LitV (LitUnit))
    end
  | StringLength, LitV (LitString s) => Some $ LitV $ LitInt (String.length s)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (n1 `quot` n2)
  | RemOp => LitInt (n1 `rem` n2)
  | AndOp => LitInt (Z.land n1 n2)
  | OrOp => LitInt (Z.lor n1 n2)
  | XorOp => LitInt (Z.lxor n1 n2)
  | ShiftLOp => LitInt (n1 ≪ n2)
  | ShiftROp => LitInt (n1 ≫ n2)
  | LeOp => LitBool (bool_decide (n1 ≤ n2))
  | LtOp => LitBool (bool_decide (n1 < n2))
  | EqOp => LitBool (bool_decide (n1 = n2))
  | StringApp => LitInt 0
  end.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp | StringApp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match v1, v2, op with
  | LitV (LitInt n1), LitV (LitInt n2), op => Some $ LitV $ bin_op_eval_int op n1 n2
  | LitV (LitBool b1), LitV (LitBool b2), op => LitV <$> bin_op_eval_bool op b1 b2
  | LitV (LitString s1), LitV (LitString s2), StringApp =>
    Some $ LitV $ LitString (String.append s1 s2)
  | v1, v2, op => guard (op = EqOp); Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  end.

Definition option_nat_to_val (v : option nat) :=
  match v with
  | None => InjLV (LitV LitUnit)
  | Some v' => InjRV (LitV $ LitInt (Z.of_nat v'))
  end.

Definition observation : Set := ().

Inductive head_step
  : expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
     head_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | PairS v1 v2 σ :
     head_step (Pair (Val v1) (Val v2)) σ [] (Val $ PairV v1 v2) σ []
  | InjLS v σ :
     head_step (InjL $ Val v) σ [] (Val $ InjLV v) σ []
  | InjRS v σ :
     head_step (InjR $ Val v) σ [] (Val $ InjRV v) σ []
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step (UnOp op (Val v)) σ [] (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op (Val v1) (Val v2)) σ [] (Val v') σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) σ [] e1 σ []
  | IfFalseS e1 e2 σ :
      head_step (If (Val $ LitV $ LitBool false) e1 e2) σ [] e2 σ []
  | FindFromS v0 v1 v2 σ :
      head_step (FindFrom
                   (Val $ LitV $ LitString v0)
                   (Val $ LitV $ LitInt (Z.of_nat v1))
                   (Val $ LitV $ LitString v2)) σ
                []
                (of_val (option_nat_to_val (index v1 v2 v0))) σ
                []
  | SubstringS v0 v1 v2 σ :
      head_step (Substring (Val (LitV $ LitString v0)) (Val (LitV $ LitInt (Z.of_nat v1))) (Val (LitV $ LitInt (Z.of_nat v2)))) σ
                []
                (Val $ LitV $ LitString (substring v1 v2 v0)) σ
                []
  | FstS v1 v2 σ :
     head_step (Fst (Val $ PairV v1 v2)) σ [] (Val v1) σ []
  | SndS v1 v2 σ :
     head_step (Snd (Val $ PairV v1 v2)) σ [] (Val v2) σ []
  | CaseLS v e1 e2 σ :
     head_step (Case (Val $ InjLV v) e1 e2) σ [] (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     head_step (Case (Val $ InjRV v) e1 e2) σ [] (App e2 (Val v)) σ []
  | ForkS e σ :
     head_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]
  | AllocS v σ l :
      σ !! l = None →
      head_step (Alloc (Val v)) σ [] (Val $ LitV $ LitLoc l) (<[l:=v]>σ) []
  | LoadS l v σ :
      σ !! l = Some v →
      head_step (Load (Val $ LitV $ LitLoc l)) σ [] (Val v) σ []
  | StoreS l v σ :
      head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
                []
                (Val $ LitV $ LitUnit) (<[l:=v]>σ)
                []
  | CasFailS l v1 v2 vl σ :
      σ !! l = Some vl → vl ≠ v1 →
      head_step (CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
                []
                (Val $ LitV $ LitBool false) σ
                []
  | CasSucS l v1 v2 σ :
      σ !! l = Some v1 →
      head_step (CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
                []
                (Val $ LitV $ LitBool true) (<[l:=v2]>σ)
                []
  | MakeAddressS s p σ :
      head_step (MakeAddress (Val $ LitV $ (LitString s)) (Val $ LitV $ (LitInt p))) σ
                []
                (Val $ LitV $ LitSocketAddress (SocketAddressInet s (Z.to_pos p))) σ
                [].

(** Basic properties about the language *)
Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal. Qed.

Lemma alloc_fresh v σ :
  let l := fresh (dom (gset loc) σ) in
  head_step (Alloc (Val v)) σ [] (Val $ LitV (LitLoc l)) (<[l:=v]>σ) [].
Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

Lemma base_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
         fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

End base_lang.

(** The network-aware layer of the language *)
Module aneris_lang.
Import base_lang.
Import Network.
Import RecordSetNotations.

Record aneris_expr := mkExpr { expr_n : ip_address;
                        expr_e : base_lang.expr }.

Record aneris_val := mkVal { val_n : ip_address;
                      val_e : base_lang.val }.

Global Instance expr_inhabited : Inhabited aneris_expr :=
  populate {| expr_n := "";
              expr_e := Val inhabitant |}.
Global Instance val_inhabited : Inhabited aneris_val :=
  populate {| val_n := "";
              val_e := inhabitant |}.

Definition aneris_fill_item Ki e :=
  {| expr_n := expr_n e;
     expr_e := (base_lang.fill_item Ki (expr_e e)) |}.

Definition aneris_of_val v : aneris_expr :=
  {| expr_n := val_n v;
     expr_e := base_lang.of_val (val_e v) |}.
Arguments aneris_of_val !v.

Definition aneris_to_val e : option aneris_val :=
  (λ v, {| val_n := expr_n e; val_e := v |}) <$> base_lang.to_val (expr_e e).

(** For each node of the network, its local state is defined as a triple
   - a map [H] that maps pointers to values,
   - a map [Sn] associating each socket handler with a tuple of a socket and
     the messages received and send on the socket, and
   - a map [P] tracking for each ip address the ports in use on the ip. *)
Definition heap := gmap base_lang.loc base_lang.val.
Definition sockets := gmap socket_handle (socket * message_soup * message_soup).
Definition ports_in_use := gmap ip_address (gset port).

(** The global state of the system
   - maps each node of the system to it local state (H, S, P)
   - keeps track of all messages that has been sent throught the network *)
Record state := mkState {
  state_heaps : gmap ip_address heap;
  state_sockets : gmap ip_address sockets;
  state_ports_in_use : ports_in_use;
  state_ms : message_soup;
}.

Instance etaState : Settable _ :=
  settable! mkState
  <state_heaps;
   state_sockets;
   state_ports_in_use;
   state_ms>.

Definition option_socket_address_to_val (sa : option socket_address) :=
  match sa with
  | None => InjLV (LitV LitUnit)
  | Some addr => InjRV (LitV $ LitSocketAddress addr)
  end.

Implicit Types σ : state.
Implicit Types h : heap.
Implicit Types H : gmap ip_address heap.
Implicit Types S : gmap ip_address sockets.
Implicit Types Sn : sockets .
Implicit Types P : ports_in_use.
Implicit Types ps : gset port.
Implicit Types M R T : message_soup.
Implicit Types A B : gset socket_address.
Implicit Types sis : gmap socket_address gname.
Implicit Types a : socket_address.
Implicit Types ip : ip_address.
Implicit Types sh : socket_handle.
Implicit Types skt : socket.

(* The network-aware reduction step relation for a given node *)
Inductive socket_step ip :
  base_lang.expr -> sockets -> ports_in_use -> message_soup ->
  base_lang.expr -> sockets -> ports_in_use -> message_soup ->
  Prop :=
| NewSocketS f p sh s Sn P M :
    (* The socket handle is fresh *)
    Sn !! sh = None →
    socket_step
      ip
      (NewSocket (Val $ LitV $ LitAddressFamily f)
                 (Val $ LitV $ LitSocketType s)
                 (Val $ LitV $ LitProtocol p))
      Sn P M
      (* reduces to *)
      (Val $ LitV $ LitSocket sh)
      (<[sh:=(mkSocket f s p None, ∅, ∅)]>Sn) P M
| SocketBindSucS sh a R T skt Sn P ps M  :
    (* The socket handle is bound to a socket. *)
    Sn !! sh = Some (skt, R, T) →
    (* The socket has no assigned address. *)
    saddress skt = None →
    (* The port is not in use *)
    P !! ip_of_address a = Some ps →
    port_of_address a ∉ ps →
    socket_step
      ip
      (SocketBind
         (Val $ LitV $ LitSocket sh)
         (Val $ LitV $ LitSocketAddress a))
      Sn P M
      (* reduces to *)
      (Val $ LitV $ LitInt 0)
      (<[sh:=((skt <| saddress := Some a |>), R, T)]>Sn)
      (<[ip_of_address a:={[ port_of_address a ]} ∪ ps]> P)
      M
| SendToBoundS sh a mbody R T skt Sn P M f :
    (* There is a socket that has been allocated for the handle *)
    Sn !! sh = Some (skt, R, T) →
    (* The socket has an assigned address *)
    saddress skt = Some f ->
    let: new_message := mkMessage f a (sprotocol skt) mbody in
    socket_step
      ip
      (SendTo (Val $ LitV $ LitSocket sh)
              (Val $ LitV $ LitString mbody)
              (Val $ LitV $ LitSocketAddress a))
      Sn P M
      (* reduces to *)
      (Val $ LitV $ LitInt (String.length mbody))
      (<[sh:=(skt, R, ({[new_message]} ∪ T))]>Sn) P ({[ new_message ]} ∪ M)
| ReceiveFromSomeS sh R T skt a m Sn P M :
    (* The socket handle is bound to a socket *)
    Sn !! sh = Some (skt, R, T) →
    (* The socket has an assigned address *)
    saddress skt = Some a →
    (* There is a message to receive *)
    m ∈ (messages_to_receive_at a M) →
    socket_step
      ip
      (ReceiveFrom (Val $ LitV $ LitSocket sh))
      Sn P M
      (* reduces to *)
      (Val $ InjRV (PairV (LitV $ LitString (m_body m))
                          (LitV $ LitSocketAddress (m_sender m))))
      (<[sh:=(skt, {[ m ]} ∪ R, T)]>Sn) P M
| ReceiveFromNoneS sh srt Sn P M :
    (* The socket handle is bound to some socket *)
    Sn !! sh = Some srt →
    socket_step
      ip
      (ReceiveFrom (Val $ LitV $ LitSocket sh)) Sn P M
      (* reduces to *)
      (Val $ InjLV (LitV LitUnit)) Sn P M.

Definition is_head_step_pure (e : base_lang.expr) : bool :=
  match e with
  | Alloc _
  | Load _
  | Store _ _
  | CAS _ _ _
  | NewSocket _ _ _
  | SocketBind _ _
  | SendTo _ _ _
  | ReceiveFrom _ => false
  | _ => true
  end.

Inductive head_step : aneris_expr → state → list observation →
                      aneris_expr → state → list aneris_expr → Prop :=
| LocalStepPureS n h e e' ef κ σ
                 (is_pure : is_head_step_pure e = true)
                 (BaseStep : base_lang.head_step e h κ e' h ef)
  : head_step (mkExpr n e) σ
              κ
              (mkExpr n e') σ
              (map (mkExpr n) ef)
| LocalStepS n h h' e e' ef κ σ
             (is_pure : is_head_step_pure e = false)
             (BaseStep : base_lang.head_step e h κ e' h' ef)
  : state_heaps σ !! n = Some h →
    head_step (mkExpr n e ) σ
              κ
              (mkExpr n e') (σ <| state_heaps := <[n:=h']>(state_heaps σ) |>)
              (map (mkExpr n) ef)
| AssignNewIpStepS ip e κ σ :
    ip ≠ "system" →
    state_heaps σ !! ip = None →
    state_sockets σ !! ip = None →
    is_Some (state_ports_in_use σ !! ip) →
    head_step (mkExpr "system" (Start (LitString ip) e)) σ
              κ
              (mkExpr "system" (Val $ LitV $ LitUnit))
              {|
                state_heaps := <[ip:=∅]>(state_heaps σ);
                state_sockets := <[ip:=∅]>(state_sockets σ);
                state_ports_in_use := state_ports_in_use σ;
                state_ms := state_ms σ |}
              [mkExpr ip e]
| SocketStepS n e e' Sn Sn' P' M' σ κ
    (SocketStep : socket_step n
        e  Sn (state_ports_in_use σ) (state_ms σ)
        e' Sn' P' M')
  : state_sockets σ !! n = Some Sn ->
    head_step (mkExpr n e) σ
              κ
              (mkExpr n e')
              {| state_heaps := state_heaps σ;
                 state_sockets := <[n:=Sn']>(state_sockets σ);
                 state_ports_in_use := P';
                 state_ms := M'; |}
              [].

Lemma aneris_to_of_val v : aneris_to_val (aneris_of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma aneris_of_to_val e v : aneris_to_val e = Some v → aneris_of_val v = e.
Proof.
  case e, v. cbv. rewrite -/(base_lang.to_val expr_e0).
  case C: (base_lang.to_val expr_e0) =>//. move=> [<- <-].
  f_equal. exact: base_lang.of_to_val.
Qed.

Lemma to_base_aneris_val e v:
  aneris_to_val e = Some v → to_val (expr_e e) = Some (val_e v).
Proof. destruct e, v. cbv -[base_lang.to_val]. case_match; naive_solver. Qed.

Lemma to_base_aneris_val' n e v:
  aneris_to_val {| expr_n := n ; expr_e := e |} =
  Some {| val_n := n ; val_e := v |} →
  base_lang.to_val e = Some v.
Proof. cbv -[base_lang.to_val]. case_match; naive_solver. Qed.

Lemma to_base_aneris_val_inv e v n:
  base_lang.to_val e = Some v → aneris_to_val (mkExpr n e) = Some (mkVal n v).
Proof. cbv -[base_lang.to_val]. by move => ->. Qed.

Lemma of_base_aneris_val e v:
  aneris_of_val v = e → base_lang.of_val (val_e v) = (expr_e e).
Proof. destruct e,v. by inversion 1. Qed.

Lemma aneris_val_head_stuck σ1 e1 κ σ2 e2 ef :
  head_step e1 σ1 κ e2 σ2 ef → aneris_to_val e1 = None.
Proof.
  inversion 1; subst; last inversion SocketStep; subst;
    try (cbv -[base_lang.to_val];
           by erewrite base_lang.val_head_stuck; last eassumption);
    eauto.
Qed.

Lemma fill_item_aneris_val Ki e :
  is_Some (aneris_to_val (aneris_fill_item Ki e)) → is_Some (aneris_to_val e).
Proof.
  move/fmap_is_Some/base_lang.fill_item_val => H.
  exact/fmap_is_Some.
Qed.

Lemma fill_item_no_aneris_val_inj Ki1 Ki2 e1 e2 :
  aneris_to_val e1 = None → aneris_to_val e2 = None →
  aneris_fill_item Ki1 e1 = aneris_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  move => /fmap_None H1 /fmap_None H2 [] H3 H4.
  exact: base_lang.fill_item_no_val_inj H1 H2 H4.
Qed.

Lemma head_ctx_step_aneris_val Ki e σ κ e2 σ2 ef :
  head_step (aneris_fill_item Ki e) σ κ e2 σ2 ef → is_Some (aneris_to_val e).
Proof.
  inversion 1; subst; last inversion SocketStep; subst; simplify_option_eq;
    try
      (apply/fmap_is_Some; exact: base_lang.head_ctx_step_val);
    apply/fmap_is_Some.
    all: destruct Ki; try (by eauto);
      inversion H0; subst; by eauto.
Qed.

Instance of_aneris_val_inj : Inj (=) (=) aneris_of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!aneris_to_of_val Hv. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (λ e, aneris_fill_item Ki e).
Proof. destruct Ki; move => [? ?] [? ?] [? ?];
                              simplify_eq/=; auto with f_equal. Qed.

Lemma aneris_lang_mixin :
  EctxiLanguageMixin aneris_of_val aneris_to_val aneris_fill_item head_step.
Proof.
  split; apply _ || eauto using aneris_to_of_val, aneris_of_to_val,
         aneris_val_head_stuck, fill_item_aneris_val,
         fill_item_no_aneris_val_inj, head_ctx_step_aneris_val.
Qed.

Global Instance state_inhabited : Inhabited state.
Proof.
  exact {|
      inhabitant :=
        {|
          state_heaps := ∅;
          state_sockets := ∅;
          state_ports_in_use := ∅;
          state_ms := ∅;
        |}
    |}.
Qed.

Lemma newsocket_fresh n Sn P M v1 v2 v3 :
  let h := fresh (dom (gset socket_handle) Sn) in
  socket_step n
              (NewSocket (Val $ LitV $ LitAddressFamily v1)
                         (Val $ LitV $ LitSocketType v2)
                         (Val $ LitV $ LitProtocol v3)) Sn P M
              (Val $ LitV (LitSocket h))
              (<[h:=(mkSocket v1 v2 v3 None, ∅, ∅)]>Sn) P M.
Proof.
  intros; apply NewSocketS.
  apply (not_elem_of_dom (D:=gset loc)), is_fresh.
Qed.

End aneris_lang.

(* Prefer base names over ectx_language names. *)
Export base_lang.
Export aneris_lang.

Global Arguments aneris_fill_item /_ _.
