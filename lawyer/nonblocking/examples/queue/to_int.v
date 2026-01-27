From heap_lang Require Import heap_lang_defs lang notation.

(* TODO: change heap_lang accordingly *)

Definition ToInt: expr. Admitted.

#[global] Instance ToInt_atomic s v : Atomic s (ToInt $ Val v).
Proof. Admitted. 

Definition val_into_int (v : val) := 
  match v with
  | LitV (LitInt n) => SOMEV v
  | _  => NONEV
  end. 

#[global] Instance pure_ToInt (v : val) :
  PureExec True 1 (ToInt $ Val v) (Val $ val_into_int v).
Proof. Admitted. 
