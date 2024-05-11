From iris.algebra Require Import gmap list.
From aneris.examples.transactional_consistency Require Import user_params.
From stdpp Require Import strings.
From aneris.aneris_lang Require Import network resources.

Definition Tag : Type := string.

Inductive operation : Type :=
  | Rd (tag : Tag) (k : Key) (ov : option val) : operation 
  | Wr (tag : Tag) (k : Key) (v : val) : operation
  | Cm (tag : Tag) (b : bool) : operation.

#[global] Instance operation_eq_dec : EqDecision operation.
Proof. solve_decision. Defined.

#[global] Instance operation_countable : Countable operation.
Proof.
  refine {|
    encode := λ op, match op with 
                 | Rd s k ov => encode (1, s, k, ov, LitV LitUnit, false)
                 | Wr s k v => encode (2, s, k, None : option val, v, false)
                 | Cm s b => encode (3, s, "", None : option val, LitV LitUnit, b)
                 end;
    decode := λ n, (λ x, match x.1.1.1.1.1 with 
                      | 1 => Rd x.1.1.1.1.2 x.1.1.1.2 x.1.1.2
                      | 2 => Wr x.1.1.1.1.2 x.1.1.1.2 x.1.2
                      | _ => Cm x.1.1.1.1.2 x.2
                      end) 
                <$> @decode (nat * string * Key * (option val) * val * bool)%type _ _ n;
  |}.
  by intros []; rewrite decode_encode.
Qed.

Definition transaction : Type := list operation.

Definition tagOfOp (op : operation) : Tag :=
  match op with 
    | Rd tag _ _ => tag
    | Wr tag _ _ => tag
    | Cm tag _ => tag
  end.

Definition rel_list {A : Type} (l : list A) (a1 a2 : A) : Prop :=
  ∃ i j, i <= j ∧ l !! i = Some a1 ∧ l !! j = Some a2.

Definition valid_transaction (t : transaction) : Prop :=
  (* The last operation is the commit operation *)
  (∃ s b, last t = Some (Cm s b)) ∧ 
  (* The commit operaion is unique *)
  (∀ op s b, op ∈ t → op = Cm s b → last t = Some op) ∧
  (* All operations use the same Tag *)
  (∀ op1 op2, op1 ∈ t → op2 ∈ t → tagOfOp op1 = tagOfOp op2).

Definition state : Type := gmap Key val.

Definition applyTransaction (s : state) (t : transaction) : state := 
  foldl (λ s op, match op with | Wr _ k v => <[k := v]> s | _ => s end) s t.
  
Definition execution : Type := list (transaction * state).

Definition commitTest : Type := execution -> transaction -> Prop.

Definition valid_transactions (T : list transaction) : Prop := 
  (* Transactions read their own writes *)
  (∀ t tag k ov, t ∈ T → 
                  Rd tag k ov ∈ t → 
                  ∃ v, Wr tag k v ∈ t →
                  rel_list t (Wr tag k v) (Rd tag k ov) →
                  (¬∃ v', Wr tag k v' ∈ t ∧ 
                          v' ≠ v ∧ 
                          rel_list t (Wr tag k v) (Wr tag k v') ∧
                          rel_list t (Wr tag k v') (Rd tag k ov)) →
                  ov = Some v) ∧ 
  (* Transactions read from some write *)
  (∀ t tag k v, t ∈ T → 
                 Rd tag k (Some v) ∈ t →
                 ∃ t' tag', t' ∈ T ∧ Wr tag' k v ∈ t') ∧
  (* Transactions satisfy the baseline transaction contraints *)
  (∀ t, t ∈ T → valid_transaction t).

Definition valid_execution (test : commitTest) (exec : execution) : Prop :=
  (* Transitions are valid *)
  (∀ i e1 e2, exec !! i = Some e1 → 
              exec !! (i + 1) = Some e2 →
              applyTransaction e1.2 e2.1 = e2.2) ∧
  (* Initial state is valid *)
  (exec !! 0 = Some ([], ∅)) ∧
  (* The commit test is satisfied *)
  (∀ t, t ∈ (split exec).1 → test exec t).

(** Read Uncommitted  *)

Definition commit_test_ru : commitTest := λ exec trans, true.

(** Read Committed  *)

Definition initTag : Tag := "init_tag".

Definition idOfTrans (t : transaction) : Tag :=
  match head t with | Some op => tagOfOp op | None => initTag end.

Definition read_state (tag : Tag) (k : Key) (ov : option val) 
(exec : execution) (s : state) : Prop := 
  (s ∈ (split exec).2) ∧ 
  (s !! k = ov) ∧
  (∀ i j s' t', (split exec).2 !! i = Some s → 
                exec !! j = Some (t', s') →
                tag = idOfTrans t' →
                i <= j).

Definition pre_read (exec : execution) (t : transaction) : Prop :=
  ∀ op tag k ov, op ∈ t → 
                  op = Rd tag k ov →
                  ∃ s, read_state tag k ov exec s.

Definition commit_test_rc : commitTest := 
  λ exec trans, pre_read exec trans.

(** Snapshot Isolation *)

Definition complete (exec : execution) (t : transaction)  
(s : state): Prop := 
  ∀ op tag k ov, op ∈ t → 
                  op = Rd tag k ov →
                  read_state tag k ov exec s.

Definition parent_state (exec : execution) (t : transaction) (s : state) : Prop :=
  ∃ i t' s', exec !! i = Some (t' , s) ∧ exec !! (i + 1) = Some (t, s').

Definition no_conf (exec : execution) (t : transaction) (s : state) : Prop := 
  ¬(∃ k, (∃ tag v, Wr tag k v ∈ t) ∧ 
         (∀ sp, parent_state exec t sp → s !! k ≠ sp !! k)). 

Definition commit_test_si : commitTest := 
  λ exec trans, ∃ s, s ∈ (split exec).2 ∧ 
                complete exec trans s ∧ 
                no_conf exec trans s.

(** Embedding into the trace infrastructure *)

Definition toOp (event : val) : option operation := 
  match event with 
    | (#(LitString tag), (#"Rd", (#(LitString k), NONEV)))%V => Some (Rd tag k None)
    | (#(LitString tag), (#"Rd", (#(LitString k), SOMEV v)))%V => Some (Rd tag k (Some v))
    | (#(LitString tag), (#"Wr", (#(LitString k), v)))%V => Some (Wr tag k v)
    | (#(LitString tag), (#"Cm", #(LitBool b)))%V => Some (Cm tag b)
    | _ => None
  end.

Definition toEvent (op : operation) : val := 
  match op with 
    | Rd tag k None => (#tag, (#"Rd", (#k, NONEV)))
    | Rd tag k (Some v) => (#tag, (#"Rd", (#k, SOMEV v)))
    | Wr tag k v => (#tag, (#"Wr", (#k, v)))
    | Cm tag b => (#tag, (#"Cm", #b))
  end.

Definition extractionOf (trace : list val) (T : list transaction): Prop := 
  (* Trace and transactions contain the same operations *)
  (∀ event op, event ∈ trace → toOp event = Some op → ∃ t, t ∈ T → op ∈ t) ∧
  (∀ t op, t ∈ T → op ∈ t → (toEvent op) ∈ trace) ∧
  (* Operations are grouped into transactions correctly *)
  (∀ t op1 op2, t ∈ T → op1 ∈ t → op2 ∈ t → tagOfOp op1 = tagOfOp op2).

Definition comTrans (T : list transaction) : list transaction := 
  List.filter (λ t, match last t with | Some (Cm tag true) => true | _ => false end) T.

Definition based_on (exec : execution) (transactions : list transaction) : Prop :=
  ∀ t, t ∈ (split exec).1 ↔ t ∈ transactions.

Definition valid_trace (test : commitTest) : list val → Prop :=
  λ t, ∀ T, extractionOf t T ∧ valid_transactions T ∧ 
            ∃ exec, based_on exec (comTrans T) ∧ valid_execution test exec.

Definition valid_trace_ru : list val → Prop := valid_trace commit_test_ru.

Definition valid_trace_rc : list val → Prop := valid_trace commit_test_rc.

Definition valid_trace_si : list val → Prop := valid_trace commit_test_si.