From heap_lang Require Import heap_lang_defs lang notation.

(* TODO: change heap_lang accordingly *)

Definition ToInt (e: expr): expr. Admitted.

#[global] Instance ToInt_atomic s v : Atomic s (ToInt $ Val v).
Proof. Admitted. 

Definition val_into_int (v : val) := 
  match v with
  | LitV (LitInt n) => SOMEV v
  | _  => NONEV
  end.

Lemma val_into_int_spec v:
  (exists (n: Z), v = #n /\ val_into_int v = SOMEV v) \/ (¬ (exists (n: Z), v = #n) /\ val_into_int v = NONEV).
Proof using.
  destruct v; simpl; eauto.
  all: try set_solver. 
  destruct l; simpl; set_solver.
Qed.

#[global] Instance pure_ToInt (v : val) :
  PureExec True 1 (ToInt $ Val v) (Val $ val_into_int v).
Proof. Admitted. 

Lemma ToInt_subst (s: string) v e: subst s v (ToInt e) = ToInt (subst s v e).
Proof using. Admitted. 

Lemma ToInt_nval v: language.to_val (ToInt v) = None.
Proof using. Admitted.
