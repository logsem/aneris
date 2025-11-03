From heap_lang Require Import heap_lang_defs sswp_logic tactics. 

Definition valid_base_lit (v: base_lit) : Prop :=
  match v with
  | LitInt _ | LitBool _ | LitUnit => True
  | LitLoc _ | LitProphecy _ | LitPoison => False
  end.

Definition valid_bin_op (op: bin_op): Prop :=
  match op with 
  | OffsetOp => False
  | _ => True
  end. 

(* a valid client proram is any program without:
     - hard-coded locations
     - address offset operations
     TODO: currently we also exclude prophecies, seems reasonable? *)
Fixpoint valid_client (e : expr) : Prop :=
  match e with
  | Val v => valid_val v
  | Var _ | ChooseNat => True
  | Rec _ _  e | UnOp _ e | Fst e | Snd e |
    InjL e | InjR e | Fork e | Load e | Free e
    => valid_client e
  | App e1 e2 | Pair e1 e2 | 
    AllocN e1 e2 | Store e1 e2 | FAA e1 e2
    => valid_client e1 /\ valid_client e2
  | BinOp op e1 e2 => valid_bin_op op /\ valid_client e1 /\ valid_client e2
  | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2
    => valid_client e0 /\ valid_client e1 /\ valid_client e2
  end
with valid_val (v: val) : Prop :=
  match v with
  | LitV b => valid_base_lit b
  | RecV _ _ e => valid_client e
  | PairV v1 v2 => valid_val v1 /\ valid_val v2
  | InjLV v | InjRV v => valid_val v
end.
