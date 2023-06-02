From fairneris.aneris_lang Require Export ast.
From fairneris.prelude Require Export strings.
From trillium.program_logic Require Export
     language ectx_language ectxi_language adequacy.
From iris.algebra Require Export ofe gset.
From stdpp Require Export strings.
From stdpp Require Import gmap fin pretty.
From stdpp Require Export binders.
From RecordUpdate Require Import RecordSet.
From fairneris.aneris_lang Require Export network.

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module base_lang.
Open Scope Z_scope.

Export ast.
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

#[global] Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

#[global] Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
#[global] Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
#[global] Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
#[global] Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
      fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
        match e1, e2 with
        | Val v, Val v' => cast_if (decide (v = v'))
        | Var x, Var x' => cast_if (decide (x = x'))
        | Rec f x e, Rec f' x' e' =>
          cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
        | App e1 e2, App e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
        | BinOp o e1 e2, BinOp o' e1' e2' =>
          cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
        | If e0 e1 e2, If e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | FindFrom e0 e1 e2, FindFrom e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | Substring e0 e1 e2, Substring e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | Rand e, Rand e' => cast_if (decide (e = e'))
        | Pair e1 e2, Pair e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | Fst e, Fst e' => cast_if (decide (e = e'))
        | Snd e, Snd e' => cast_if (decide (e = e'))
        | InjL e, InjL e' => cast_if (decide (e = e'))
        | InjR e, InjR e' => cast_if (decide (e = e'))
        | Case e0 e1 e2, Case e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | Fork e, Fork e' => cast_if (decide (e = e'))
        | Alloc lbl e, Alloc lbl' e' =>
          cast_if_and (decide (lbl = lbl')) (decide (e = e'))
        | Load e, Load e' => cast_if (decide (e = e'))
        | Store e1 e2, Store e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | CAS e0 e1 e2, CAS e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | MakeAddress e1 e2, MakeAddress e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | GetAddressInfo e, GetAddressInfo e' =>
          cast_if (decide (e = e'))
        | NewSocket e, NewSocket e' => cast_if (decide (e = e'))
        | SocketBind e1 e2, SocketBind e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | SendTo e0 e1 e2, SendTo e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | SendToRepeat e0 e1 e2, SendToRepeat e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
        | ReceiveFrom e, ReceiveFrom e' => cast_if (decide (e = e'))
        | SetReceiveTimeout e0 e1 e2,  SetReceiveTimeout e0' e1' e2' =>
          cast_if_and3
            (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
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
#[global] Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

#[global] Instance base_lit_countable : Countable base_lit.
Proof.
  refine (inj_countable' (λ l, match l with
   | LitInt n => inl (inl (inl (inl n)))
   | LitBool b => inl (inl (inl (inr b)))
   | LitUnit => inl (inl (inr (inl ())))
   | LitLoc l => inl (inl (inr (inr l)))
   | LitString s => inl (inr (inl (inl s)))
   | LitSocket s => inr (inl (inl (inl s)))
   | LitSocketAddress a => inr (inl (inl (inr a)))
   end) (λ l, match l with
   | inl (inl (inl (inl n))) => LitInt n
   | inl (inl (inl (inr b))) => LitBool b
   | inl (inl (inr (inl ()))) => LitUnit
   | inl (inl (inr (inr l))) => LitLoc l
   | inl (inr (inl (inl s))) => LitString s
   | inl (inr (inl (inr ()))) => LitUnit
   | inl (inr (inr (inl ()))) => LitUnit
   | inl (inr (inr (inr ()))) => LitUnit
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

#[global] Instance un_op_countable : Countable un_op.
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

#[global] Instance bin_op_countable : Countable bin_op.
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

#[global] Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl (inl x)))
     | Rec f x e =>
       GenNode 1 [GenLeaf (inl (inl (inr f))); GenLeaf (inl (inl (inr x))); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inl (inr (inr (inl op)))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inl (inr (inr (inr op)))); go e1; go e2]
     | If e0 e1 e2 => GenNode 5 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 6 [go e1; go e2]
     | Fst e => GenNode 7 [go e]
     | Snd e => GenNode 8 [go e]
     | InjL e => GenNode 9 [go e]
     | InjR e => GenNode 10 [go e]
     | Case e0 e1 e2 => GenNode 11 [go e0; go e1; go e2]
     | Fork e => GenNode 12 [go e]
     | Alloc lbl e => GenNode 13 [GenLeaf (inr lbl); go e]
     | Load e => GenNode 14 [go e]
     | Store e1 e2 => GenNode 15 [go e1; go e2]
     | MakeAddress e1 e2 => GenNode 16 [go e1; go e2]
     | NewSocket e => GenNode 17 [go e]
     | SocketBind e1 e2 => GenNode 18 [go e1; go e2]
     | SendTo e1 e2 e3 => GenNode 19 [go e1; go e2; go e3]
     | ReceiveFrom e => GenNode 20 [go e]
     | SetReceiveTimeout e1 e2 e3 => GenNode 21 [go e1; go e2; go e3]
     | Start i e => GenNode 22 [GenLeaf (inl (inr (inl i))); go e]
     | FindFrom e1 e2 e3 => GenNode 23 [go e1; go e2; go e3]
     | Substring e1 e2 e3 => GenNode 24 [go e1; go e2; go e3]
     | CAS e1 e2 e3 => GenNode 25 [go e1; go e2; go e3]
     | GetAddressInfo e => GenNode 26 [go e]
     | Rand e => GenNode 27 [go e]
     | SendToRepeat e1 e2 e3 => GenNode 28 [go e1; go e2; go e3]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inl (inr (inl l)))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inl (inr f))); GenLeaf (inl (inl (inr x))); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl (inl x))) => Var x
     | GenNode
         1 [GenLeaf (inl (inl (inr f))); GenLeaf (inl (inl (inr x))); e] =>
       Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inl (inr (inr (inl op)))); e] => UnOp op (go e)
     | GenNode
         4 [GenLeaf (inl (inr (inr (inr op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 6 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 7 [e] => Fst (go e)
     | GenNode 8 [e] => Snd (go e)
     | GenNode 9 [e] => InjL (go e)
     | GenNode 10 [e] => InjR (go e)
     | GenNode 11 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 12 [e] => Fork (go e)
     | GenNode 13 [GenLeaf (inr lbl);e] => Alloc lbl (go e)
     | GenNode 14 [e] => Load (go e)
     | GenNode 15 [e1; e2] => Store (go e1) (go e2)
     | GenNode 16 [e1; e2] => MakeAddress (go e1) (go e2)
     | GenNode 17 [e] => NewSocket (go e)
     | GenNode 18 [e1; e2] => SocketBind (go e1) (go e2)
     | GenNode 19 [e1; e2; e3] => SendTo (go e1) (go e2) (go e3)
     | GenNode 20 [e] => ReceiveFrom (go e)
     | GenNode 21 [e1; e2; e3] => SetReceiveTimeout (go e1) (go e2) (go e3)
     | GenNode 22 [GenLeaf (inl (inr (inl i))); e2] => Start i (go e2)
     | GenNode 23 [e1; e2; e3] => FindFrom (go e1) (go e2) (go e3)
     | GenNode 24 [e1; e2; e3] => Substring (go e1) (go e2) (go e3)
     | GenNode 25 [e1; e2; e3] => CAS (go e1) (go e2) (go e3)
     | GenNode 26 [e] => GetAddressInfo (go e)
     | GenNode 27 [e] => Rand (go e)
     | GenNode 28 [e1; e2; e3] => SendToRepeat (go e1) (go e2) (go e3)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inl (inr (inl l))) => LitV l
     | GenNode
         0 [GenLeaf (inl (inl (inr f))); GenLeaf (inl (inl (inr x))); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e}
         := _ with gov (v : val) {struct v} := _ for go).
 - destruct e; simpl; f_equal; [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.

#[global] Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

#[global] Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
#[global] Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

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
| RandCtx
| PairLCtx (v2 : val)
| PairRCtx (e1 : expr)
| FstCtx
| SndCtx
| InjLCtx
| InjRCtx
| CaseCtx (e1 : expr) (e2 : expr)
| AllocCtx (lbl : option string)
| LoadCtx
| StoreLCtx (v2 : val)
| StoreRCtx (e1 : expr)
| CasLCtx (v1 v2 : val)
| CasMCtx (e0 : expr) (v2 : val)
| CasRCtx (e0 e1 : expr)
| MakeAddressLCtx (v2 : val)
| MakeAddressRCtx (e1 : expr)
| GetAddressInfoCtx
| NewSocketCtx
| SocketBindLCtx (v2 : val)
| SocketBindRCtx (e1 : expr)
| SendToLCtx (v1 v2 : val)
| SendToMCtx (e0 : expr) (v2 : val)
| SendToRCtx (e0 e1 : expr)
| SetReceiveTimeoutLCtx (v1 v2 : val)
| SetReceiveTimeoutMCtx (e0 : expr) (v2 : val)
| SetReceiveTimeoutRCtx (e0 e1 : expr)
| ReceiveFromCtx.

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
  | RandCtx => Rand e
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocCtx lbl => Alloc lbl e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | CasLCtx v1 v2 => CAS e (Val v1) (Val v2)
  | CasMCtx e0 v2 => CAS e0 e (Val v2)
  | CasRCtx e0 e1 => CAS e0 e1 e
  | MakeAddressLCtx v2 => MakeAddress e (Val v2)
  | MakeAddressRCtx e1 => MakeAddress e1 e
  | GetAddressInfoCtx => GetAddressInfo e
  | NewSocketCtx => NewSocket e
  | SocketBindLCtx v2 => SocketBind e (Val v2)
  | SocketBindRCtx e1 => SocketBind e1 e
  | SendToLCtx v1 v2 => SendTo e (Val v1) (Val v2)
  | SendToMCtx e0 v2 => SendTo e0 e (Val v2)
  | SendToRCtx e0 e1 => SendTo e0 e1 e
  | SetReceiveTimeoutLCtx v1 v2 => SetReceiveTimeout e (Val v1) (Val v2)
  | SetReceiveTimeoutMCtx e0 v2 => SetReceiveTimeout e0 e (Val v2)
  | SetReceiveTimeoutRCtx e0 e1 => SetReceiveTimeout e0 e1 e
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
  | Rand e => Rand (subst x v e)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | Alloc lbl e => Alloc lbl (subst x v e)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | CAS e0 e1 e2 => CAS (subst x v e0) (subst x v e1) (subst x v e2)
  | MakeAddress e1 e2 => MakeAddress (subst x v e1) (subst x v e2)
  | GetAddressInfo e => GetAddressInfo (subst x v e)
  | NewSocket e => NewSocket (subst x v e)
  | SocketBind e1 e2 => SocketBind (subst x v e1) (subst x v e2)
  | SendTo e0 e1 e2 => SendTo (subst x v e0) (subst x v e1) (subst x v e2)
  | SendToRepeat e0 e1 e2 => SendToRepeat (subst x v e0) (subst x v e1) (subst x v e2)
  | SetReceiveTimeout e0 e1 e2 =>
    SetReceiveTimeout (subst x v e0) (subst x v e1) (subst x v e2)
  | ReceiveFrom e => ReceiveFrom (subst x v e)
  | Start i e => Start i (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

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
  | LitV (LitInt n1), LitV (LitInt n2), op =>
    Some $ LitV $ bin_op_eval_int op n1 n2
  | LitV (LitBool b1), LitV (LitBool b2), op =>
    LitV <$> bin_op_eval_bool op b1 b2
  | LitV (LitString s1), LitV (LitString s2), StringApp =>
    Some $ LitV $ LitString (String.append s1 s2)
  | v1, v2, op =>
    guard (op = EqOp); Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  end.

Lemma bin_op_eval_eq_val k k' :
  bin_op_eval EqOp k' k = Some (LitV $ LitBool $ bool_decide (k' = k)).
Proof.
  destruct k, k'; cbn; try reflexivity; try (destruct l; reflexivity).
  destruct l,  l0; try reflexivity; repeat f_equal.
  { rewrite /bool_decide.
    case (decide_rel _ _ n), (decide_rel _ _ (LitV $ LitInt n)); congruence. }
  { rewrite /bool_decide.
    case (decide_rel _ _ b), (decide_rel _ _ (LitV $ LitBool b)); congruence. }
Qed.

Definition option_nat_to_val (v : option nat) :=
  match v with
  | None => InjLV (LitV LitUnit)
  | Some v' => InjRV (LitV $ LitInt (Z.of_nat v'))
  end.

Inductive head_step
  : expr → state → expr → state → list expr → Prop :=
  | RecS f x e σ :
     head_step (Rec f x e) σ (Val $ RecV f x e) σ []
  | PairS v1 v2 σ :
     head_step (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ []
  | InjLS v σ :
     head_step (InjL $ Val v) σ (Val $ InjLV v) σ []
  | InjRS v σ :
     head_step (InjR $ Val v) σ (Val $ InjRV v) σ []
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step (App (Val $ RecV f x e1) (Val v2)) σ e' σ []
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step (UnOp op (Val v)) σ (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op (Val v1) (Val v2)) σ (Val v') σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ []
  | IfFalseS e1 e2 σ :
      head_step (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ []
  | FindFromS v0 v1 v2 σ :
      head_step (FindFrom
                   (Val $ LitV $ LitString v0)
                   (Val $ LitV $ LitInt (Z.of_nat v1))
                   (Val $ LitV $ LitString v2)) σ
                (of_val (option_nat_to_val (index v1 v2 v0))) σ
                []
  | SubstringS v0 v1 v2 σ :
      head_step (Substring (Val (LitV $ LitString v0))
                           (Val (LitV $ LitInt (Z.of_nat v1)))
                           (Val (LitV $ LitInt (Z.of_nat v2)))) σ
                (Val $ LitV $ LitString (substring v1 v2 v0)) σ
                []
 | RandS n n' σ :
      n' >= 0 ->
      n' < n ->
      head_step (Rand $ Val $ LitV $ LitInt n) σ (Val $ LitV $ LitInt n') σ []
  | FstS v1 v2 σ :
     head_step (Fst (Val $ PairV v1 v2)) σ (Val v1) σ []
  | SndS v1 v2 σ :
     head_step (Snd (Val $ PairV v1 v2)) σ (Val v2) σ []
  | CaseLS v e1 e2 σ :
     head_step (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     head_step (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ []
  | ForkS e σ :
     head_step (Fork e) σ (Val $ LitV LitUnit) σ [e]
  | AllocS lbl v σ l :
      σ !! l = None →
      head_step (Alloc lbl (Val v)) σ (Val $ LitV $ LitLoc l) (<[l:=v]>σ) []
  | LoadS l v σ :
      σ !! l = Some v →
      head_step (Load (Val $ LitV $ LitLoc l)) σ (Val v) σ []
  | StoreS l v σ :
      head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
                (Val $ LitV $ LitUnit) (<[l:=v]>σ)
                []
  | CasFailS l v1 v2 vl σ :
      σ !! l = Some vl → vl ≠ v1 →
      head_step (CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
                (Val $ LitV $ LitBool false) σ
                []
  | CasSucS l v1 v2 σ :
      σ !! l = Some v1 →
      head_step (CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
                (Val $ LitV $ LitBool true) (<[l:=v2]>σ)
                []
  | MakeAddressS s p σ :
      head_step (MakeAddress
                   (Val $ LitV $ (LitString s))
                   (Val $ LitV $ (LitInt p))) σ
                (Val $ LitV $ LitSocketAddress
                     (SocketAddressInet s (Z.to_pos p))) σ
                []
  | GetAddressInfoS s σ :
      head_step (GetAddressInfo
                   (Val $ LitV $ (LitSocketAddress s))) σ
                (Val $ PairV #(ip_of_address s) #(Zpos (port_of_address s))) σ [].

(** Basic properties about the language *)
#[global] Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 e2 σ2 efs :
  head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 efs :
  head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal. Qed.

Lemma alloc_fresh lbl v σ :
  let l := fresh (dom σ) in
  head_step (Alloc lbl (Val v)) σ (Val $ LitV (LitLoc l)) (<[l:=v]>σ) [].
Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

Definition base_locale := nat.
Definition locale_of (c: list expr) (e : expr) := length c.

Lemma locale_step e1 e2 t1 σ1 σ2 efs:
  head_step e1 σ1 e2 σ2 efs ->
  locale_of t1 e1 = locale_of t1 e2.
Proof. done. Qed.

Lemma locale_fill e K t1: locale_of t1 (fill_item K e) = locale_of t1 e.
Proof. done. Qed.

Lemma base_locale_injective tp0 e0 tp1 tp e :
  (tp, e) ∈ prefixes_from (tp0 ++ [e0]) tp1 →
  locale_of tp0 e0 ≠ locale_of tp e.
Proof.
  intros (?&?&->&?)%prefixes_from_spec.
  rewrite /locale_of !app_length /=. lia.
Qed.

Definition base_config_label := unit.
Definition base_config_step (σ : state) (lbl : base_config_label) (σ' : state) := False.
Definition base_config_enabled (lbl : base_config_label) (σ : state) := False.

Lemma base_mixin : EctxiLanguageMixin of_val to_val fill_item head_step (* base_config_step *) locale_of (* base_config_enabled *).
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val, locale_step, base_locale_injective.
  { intros ??? H%Forall2_length. rewrite !prefixes_from_length // in H. }
  (* { apply base_config_enabled_step. } *)
Qed.

End base_lang.

(** The network-aware layer of the language *)
Module aneris_lang.
Import base_lang.
Import RecordSetNotations.
Import ast.

Record aneris_expr := mkExpr { expr_n : ip_address;
                               expr_e : expr }.

Record aneris_val := mkVal { val_n : ip_address;
                             val_e : val }.

#[global] Instance expr_inhabited : Inhabited aneris_expr :=
  populate {| expr_n := "";
              expr_e := Val inhabitant |}.
#[global] Instance val_inhabited : Inhabited aneris_val :=
  populate {| val_n := "";
              val_e := inhabitant |}.

Definition aneris_fill_item Ki e :=
  {| expr_n := expr_n e;
     expr_e := (base_lang.fill_item Ki (expr_e e)) |}.

Definition aneris_of_val v : aneris_expr :=
  {| expr_n := val_n v;
     expr_e := of_val (val_e v) |}.
Arguments aneris_of_val !v.

Definition aneris_to_val e : option aneris_val :=
  (λ v, {| val_n := expr_n e; val_e := v |}) <$> base_lang.to_val (expr_e e).

(** For each node of the network, its local state is defined as a triple
   - a map [H] that maps pointers to values,
   - a map [Sn] associating each socket handler with a tuple of a socket and
     the receive buffer, and
   - a map [P] tracking for each ip address the ports in use on the ip. *)
Definition heap := gmap loc val.
Definition sockets := gmap socket_handle (socket * list message).
Definition ports_in_use := gmap ip_address (gset port).

(** The global state of the system
   - maps each node of the system to it local state (H, S, P)
   - keeps track of all messages that has been sent throught the network *)
Record state := mkState {
  state_heaps : gmap ip_address heap;
  state_sockets : gmap ip_address sockets;
  state_ports_in_use : ports_in_use;
  state_ms : message_multi_soup;
}.

#[global] Instance etaState : Settable _ :=
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
Implicit Types M : message_multi_soup.
Implicit Types R : list message.
Implicit Types A B : gset socket_address.
Implicit Types sis : gmap socket_address gname.
Implicit Types a : socket_address.
Implicit Types ip : ip_address.
Implicit Types sh : socket_handle.
Implicit Types skt : socket.

(* The network-aware reduction step relation for a given node *)
Inductive socket_step ip :
  expr -> sockets -> ports_in_use -> message_multi_soup ->
  expr -> sockets -> ports_in_use -> message_multi_soup ->
  Prop :=
| NewSocketS sh Sn P M :
    (* The socket handle is fresh *)
    Sn !! sh = None →
    socket_step
      ip
      (NewSocket #())
      Sn P M
      (* reduces to *)
      (Val $ LitV $ LitSocket sh)
      (<[sh:=(mkSocket None true, [])]>Sn) P M
| SocketBindS sh a skt Sn P ps M  :
    (* The socket handle is bound to a socket. *)
    Sn !! sh = Some (skt, []) →
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
      (<[sh:=((skt <| saddress := Some a |>), [])]>Sn)
      (<[ip_of_address a:={[ port_of_address a ]} ∪ ps]> P)
      M
| SendToS sh a mbody r skt Sn P M f :
    (* There is a socket that has been allocated for the handle *)
    Sn !! sh = Some (skt, r) →
    (* The socket has an assigned address *)
    saddress skt = Some f ->
    let new_message := mkMessage f a mbody in
    socket_step
      ip
      (SendTo (Val $ LitV $ LitSocket sh)
              (Val $ LitV $ LitString mbody)
              (Val $ LitV $ LitSocketAddress a))
      Sn P M
      (* reduces to *)
      (Val $ LitV $ LitInt (String.length mbody))
      Sn P ({[+ new_message +]} ⊎ M)
| SendToRepeatS sh a mbody r skt Sn P M f :
    (* There is a socket that has been allocated for the handle *)
    Sn !! sh = Some (skt, r) →
    (* The socket has an assigned address *)
    saddress skt = Some f ->
    let new_message := mkMessage f a mbody in
    socket_step
      ip
      (SendToRepeat (Val $ LitV $ LitSocket sh)
              (Val $ LitV $ LitString mbody)
              (Val $ LitV $ LitSocketAddress a))
      Sn P M
      (* reduces to *)
      (SendToRepeat (Val $ LitV $ LitSocket sh)
              (Val $ LitV $ LitString mbody)
              (Val $ LitV $ LitSocketAddress a))
      Sn P ({[+ new_message +]} ⊎ M)
| ReceiveFromSomeS sh r skt a m Sn P M :
    (* The socket handle is bound to a socket with a message *)
    Sn !! sh = Some (skt, r ++ [m]) →
    (* The socket has an assigned address *)
    saddress skt = Some a →
    socket_step
      ip
      (ReceiveFrom (Val $ LitV $ LitSocket sh))
      Sn P M
      (* reduces to *)
      (Val $ InjRV (PairV (LitV $ LitString (m_body m))
                          (LitV $ LitSocketAddress (m_sender m))))
      (<[sh:=(skt, r)]>Sn) P M
| ReceiveFromNoneS sh skt Sn P M :
    (* The socket handle is bound to some socket
       and there is nothing to receive
       and the operation should not block forever
       (a positive timeout was set). *)
    Sn !! sh = Some (skt, []) →
    sblock skt = false →
    socket_step
      ip
      (ReceiveFrom (Val $ LitV $ LitSocket sh)) Sn P M
      (* reduces to *)
      (Val $ InjLV (LitV LitUnit)) Sn P M
| ReceiveFromBlockS sh skt Sn P M :
    (* The socket handle is bound to some socket
       and there is nothing to receive
       and the operation should block
       (either no timeout, or timeout 0.0 was set). *)
    Sn !! sh = Some (skt, []) →
    sblock skt = true →
    socket_step
      ip
      (ReceiveFrom (Val $ LitV $ LitSocket sh)) Sn P M
      (* reduces to *)
      (ReceiveFrom (Val $ LitV $ LitSocket sh)) Sn P M
| SetReceiveTimeoutPositiveS sh skt R Sn P M m n :
    Sn !! sh = Some (skt, R) →
    (0 <= m ∧ 0 <= n ∧ 0 < (m+n)) →
    socket_step
      ip
      (SetReceiveTimeout
         (Val $ LitV $ LitSocket sh)
         (Val $ LitV $ LitInt m)
         (Val $ LitV $ LitInt n)) Sn P M
      (* reduces to *)
      (Val $ (LitV LitUnit))
      (<[sh:=((skt<|sblock := false|>), R)]>Sn) P M
| SetReceiveTimeoutZeroS sh skt R Sn P M :
    Sn !! sh = Some (skt, R) →
    socket_step
      ip
      (SetReceiveTimeout
         (Val $ LitV $ LitSocket sh)
         (Val $ LitV $ LitInt 0)
         (Val $ LitV $ LitInt 0)) Sn P M
      (* reduces to *)
      (Val $ (LitV LitUnit))
      (<[sh:=(skt<|sblock := true|>, R)]>Sn) P M.

Definition is_head_step_pure (e : expr) : bool :=
  match e with
  | Alloc _ _
  | Load _
  | Store _ _
  | CAS _ _ _
  | NewSocket _
  | SocketBind _ _
  | SendTo _ _ _
  | ReceiveFrom _
  | Rand _
  | SetReceiveTimeout _ _ _ => false
  | _ => true
  end.

Inductive head_step : aneris_expr → state →
                      aneris_expr → state → list aneris_expr → Prop :=
| LocalStepPureS n h e e' ef σ
                 (is_pure : is_head_step_pure e = true)
                 (BaseStep : base_lang.head_step e h e' h ef)
  : head_step (mkExpr n e) σ
              (mkExpr n e') σ
              (map (mkExpr n) ef)
| LocalStepS n h h' e e' ef σ
             (is_pure : is_head_step_pure e = false)
             (BaseStep : base_lang.head_step e h e' h' ef)
  : state_heaps σ !! n = Some h →
    head_step (mkExpr n e ) σ
              (mkExpr n e') (σ <| state_heaps := <[n:=h']>(state_heaps σ) |>)
              (map (mkExpr n) ef)
| AssignNewIpStepS ip e σ :
    ip ≠ "system" →
    state_heaps σ !! ip = None →
    state_sockets σ !! ip = None →
    is_Some (state_ports_in_use σ !! ip) →
    head_step (mkExpr "system" (Start (LitString ip) e)) σ
              (mkExpr "system" (Val $ LitV $ LitUnit))
              {|
                state_heaps := <[ip:=∅]>(state_heaps σ);
                state_sockets := <[ip:=∅]>(state_sockets σ);
                state_ports_in_use := state_ports_in_use σ;
                state_ms := state_ms σ |}
              [mkExpr ip e]
| SocketStepS n e e' Sn Sn' P' M' σ
    (SocketStep : socket_step n
        e  Sn (state_ports_in_use σ) (state_ms σ)
        e' Sn' P' M')
  : state_sockets σ !! n = Some Sn ->
    head_step (mkExpr n e) σ
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
  aneris_of_val v = e → of_val (val_e v) = (expr_e e).
Proof. destruct e,v. by inversion 1. Qed.

Lemma aneris_val_head_stuck σ1 e1 σ2 e2 ef :
  head_step e1 σ1 e2 σ2 ef → aneris_to_val e1 = None.
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

Lemma head_ctx_step_aneris_val Ki e σ e2 σ2 ef :
  head_step (aneris_fill_item Ki e) σ e2 σ2 ef → is_Some (aneris_to_val e).
Proof.
  inversion 1; subst; last inversion SocketStep; subst; simplify_option_eq;
    try
      (apply/fmap_is_Some; exact: base_lang.head_ctx_step_val);
    apply/fmap_is_Some.
    all: destruct Ki; try (by eauto);
      inversion H0; subst; by eauto.
Qed.

#[global] Instance of_aneris_val_inj : Inj (=) (=) aneris_of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!aneris_to_of_val Hv. Qed.

#[global] Instance fill_item_inj Ki : Inj (=) (=) (λ e, aneris_fill_item Ki e).
Proof. destruct Ki; move => [? ?] [? ?] [? ?];
                             simplify_eq/=; auto with f_equal. Qed.

Inductive config_label := DeliverLabel | DuplicateLabel | DropLabel.

Inductive config_step :
  state → config_label → state → Prop :=
| MessageDeliverStep n σ Sn Sn' sh a skt r m:
    m ∈ messages_to_receive_at_multi_soup a (state_ms σ) →
    state_sockets σ !! n = Some Sn ->
    Sn !! sh = Some (skt, r) →
    Sn' = <[sh := (skt, m :: r)]>Sn →
    saddress skt = Some a →
    config_step σ DeliverLabel
                {| state_heaps := state_heaps σ;
                   state_sockets := <[n:=Sn']>(state_sockets σ);
                   state_ports_in_use := state_ports_in_use σ;
                   state_ms := state_ms σ ∖ {[+ m +]}; |}
| MessageDuplicateStep σ m :
    m ∈ state_ms σ →
    config_step σ DuplicateLabel
                {| state_heaps := state_heaps σ;
                   state_sockets := state_sockets σ;
                   state_ports_in_use := state_ports_in_use σ;
                   state_ms := state_ms σ ⊎ {[+ m +]}; |}
| MessageDropStep σ m :
    m ∈ state_ms σ →
    config_step σ DropLabel
                {| state_heaps := state_heaps σ;
                   state_sockets := state_sockets σ;
                   state_ports_in_use := state_ports_in_use σ;
                   state_ms := state_ms σ ∖ {[+ m +]}; |}.

Definition aneris_locale := (ip_address * nat)%type.
Definition locale_of (c: list aneris_expr) (e : aneris_expr) := (e.(expr_n), length $ (filter (λ e', e'.(expr_n) = e.(expr_n))) c).

Lemma locale_step e1 e2 t1 σ1 σ2 efs:
  head_step e1 σ1 e2 σ2 efs ->
  locale_of t1 e1 = locale_of t1 e2.
Proof.
  intros Hstep.
  assert (expr_n e1 = expr_n e2) as Heq.
  { inversion Hstep =>//. }
  rewrite /locale_of. f_equal=>//. rewrite !Heq //.
Qed.

Lemma locale_fill e K t1: locale_of t1 (aneris_fill_item K e) = locale_of t1 e.
Proof. done. Qed.

Lemma filter_length_equiv {A B: Type} (P1: A -> Prop) (P2: B -> Prop) `{∀ x, Decision (P1 x)}  `{∀ y, Decision (P2 y) } (l1: list A) (l2: list B):
  (Forall2 (λ x1 x2, P1 x1 <-> P2 x2) l1 l2) ->
  length (filter P1 l1) = length (filter P2 l2).
Proof.
  revert l2. induction l1 as [|x1 l1]; intros l2 Hfa;
    destruct l2 as [|x2 l2]; try by apply Forall2_length in Hfa.
  rewrite !filter_cons. destruct (decide (P1 x1)).
  - rewrite decide_True; last by inversion Hfa; simplify_eq; intuition.
    rewrite /=. erewrite IHl1 =>//. by inversion Hfa.
  - rewrite decide_False; last by inversion Hfa; simplify_eq; intuition.
    rewrite /=. erewrite IHl1 =>//. by inversion Hfa.
Qed.

Lemma filter_locales_equiv t0 t0' t1 t2 e:
  Forall2 (λ '(t0, e) '(t'0, e'), locale_of t0 e = locale_of t'0 e')
        (prefixes t0) (prefixes t0') ->
  Forall2 (λ '(t0, e) '(t'0, e'), locale_of t0 e = locale_of t'0 e')
        (prefixes_from t0 t1) (prefixes_from t0' t2) ->
  Forall2
    (λ x1 x2 : aneris_expr, expr_n x1 = expr_n e ↔ expr_n x2 = expr_n e) t1 t2.
Proof.
  revert t0 t0' e t1. induction t2 as [|e2 t2 IH]; intros t0 t0' e t1 H0 H;
    destruct t1 as [|e1 t1]; try by apply Forall2_length in H.
  simpl; constructor.
  { inversion H as [|???? Heq]; simplify_eq. rewrite Heq //. }
  inversion H; simplify_eq.
  apply (IH (t0 ++ [e1]) (t0' ++ [e2])) =>//.
  rewrite !prefixes_from_app. apply Forall2_app =>//. list_simplifier =>//.
  constructor =>//. unfold locale_of; f_equal =>//.
Qed.

#[global] Instance aneris_expr_eq_dec : EqDecision (aneris_expr).
Proof. intros ? ?; unfold Decision; solve_decision. Qed.
#[global] Instance aneris_state_eq_dec : EqDecision state.
Proof. intros ? ?; unfold Decision; solve_decision. Qed.

Lemma aneris_locale_injective tp0 e0 tp1 tp e :
  (tp, e) ∈ prefixes_from (tp0 ++ [e0]) tp1 →
  locale_of tp0 e0 ≠ locale_of tp e.
Proof.
  intros (?&?&->&?)%prefixes_from_spec.
  rewrite /locale_of !filter_app !app_length /=.
  intros contra. injection contra => Heq Heq'.
  rewrite filter_cons_True //= Heq' in Heq. lia.
Qed.

(* Needs to be refined for support multiple messages *)
Definition config_enabled (lbl : config_label) (σ : state) := σ.(state_ms) ≠ ∅.

Lemma aneris_lang_mixin :
  EctxiLanguageMixin aneris_of_val aneris_to_val aneris_fill_item head_step locale_of.
Proof.
  split; apply _ || eauto using aneris_to_of_val, aneris_of_to_val,
         aneris_val_head_stuck, fill_item_aneris_val,
         fill_item_no_aneris_val_inj, head_ctx_step_aneris_val,
         locale_step, locale_fill, aneris_locale_injective.
  { intros t1 t2 e H . rewrite /locale_of. f_equal.
    apply filter_length_equiv, (filter_locales_equiv [] []) =>//. }
Qed.

#[global] Instance state_inhabited : Inhabited state.
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

Lemma newsocket_fresh n Sn P M :
  let h := fresh (dom Sn) in
  socket_step n
              (NewSocket #()) Sn P M
              (Val $ LitV (LitSocket h))
              (<[h:=(mkSocket None true, [])]>Sn) P M.
Proof.
  intros; apply NewSocketS.
  apply (not_elem_of_dom (D:=gset loc)), is_fresh.
Qed.

End aneris_lang.

Coercion of_val : val >-> expr.
Coercion aneris_lang.aneris_of_val : aneris_lang.aneris_val >-> aneris_lang.aneris_expr.
Notation LetCtx x e2 := (base_lang.AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).


(* Prefer base names over ectx_language names. *)
Export base_lang.
Export aneris_lang.

Global Arguments aneris_fill_item /_ _.
Global Arguments set {_ _} _ {_} /.
