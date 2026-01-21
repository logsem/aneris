From heap_lang Require Import heap_lang_defs lang notation.

(* TODO: change heap_lang accordingly *)

Definition IsInt: expr. Admitted.

#[global] Instance IsInt_atomic s v : Atomic s (IsInt $ Val v).
Proof. Admitted. 

Definition val_into_int (v : val) := 
  match v with
  | LitV (LitInt n) => SOMEV v
  | _  => NONEV
  end. 

#[global] Instance pure_IsInt (v : val) :
  PureExec True 1 (IsInt $ Val v) (Val $ val_into_int v).
Proof. Admitted. 
