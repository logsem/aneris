From iris.algebra Require Import gmap list.
From aneris.examples.transactional_consistency Require Import user_params.
From stdpp Require Import strings.
From aneris.aneris_lang Require Import network resources.

Inductive operation : Type :=
  | Rd (tag : string) (c : val) (k : Key) (ov : option val) : operation 
  | Wr (tag : string) (c : val) (k : Key) (v : val) : operation
  | Cm (tag : string) (c : val) (b : bool) : operation.

#[global] Instance operation_eq_dec : EqDecision operation.
Proof. solve_decision. Defined.

Definition connOfOp (op : operation) : val :=
  match op with 
    | Rd _ c _ _ => c
    | Wr _ c _ _ => c
    | Cm _ c _ => c
  end.

Definition connOfEvent (event : val) : option val :=
  match event with 
    | (#(LitString tag), (c, (#"Rd", (#(LitString k), NONEV))))%V => Some c
    | (#(LitString tag), (c, (#"Rd", (#(LitString k), SOMEV v))))%V => Some c
    | (#(LitString tag), (c, (#"Wr", (#(LitString k), v))))%V => Some c
    | (#(LitString tag), (c, (#"Cm", #(LitBool b))))%V => Some c
    | (#(LitString tag), (c, #"St"))%V => Some c
    | _ => None
  end.

Definition transaction : Type := list operation.

Definition valid_transaction (t : transaction) : Prop :=
  (* The last operation is the commit operation *)
  (∃ tag c b, last t = Some (Cm tag c b)) ∧ 
  (* There is only one commit operation *)
  (∀ op tag c b, op ∈ t → op = Cm tag c b → last t = Some op) ∧
  (* Operations come from the same connection *)
  (∀ op1 op2, op1 ∈ t → op2 ∈ t → connOfOp op1 = connOfOp op2) ∧
  (* No duplicate operations *)
  (∀ op1 op2 i j, t !! i = Some op1 → t !! j = Some op2 → op1 = op2 → i = j).

(* We assume unit is not used as a connection *)
Definition initConn : val := #().

Definition connOfTrans (t : transaction) : val :=
  match head t with | Some op => connOfOp op | None => initConn end.

Definition rel_list {A : Type} (l : list A) (a1 a2 : A) : Prop :=
  ∃ i j, i < j ∧ l !! i = Some a1 ∧ l !! j = Some a2.

Definition valid_transactions (T : list transaction) : Prop := 
  (* Transactions read their own writes *)
  (∀ t tag c k ov, t ∈ T → 
                   Rd tag c k ov ∈ t → 
                   ∃ tag1 v1, Wr tag1 c k v1 ∈ t →
                   rel_list t (Wr tag1 c k v1) (Rd tag c k ov) →
                   (¬∃ tag2 v2, Wr tag2 c k v2 ∈ t ∧ 
                                 rel_list t (Wr tag1 c k v1) (Wr tag2 c k v2) ∧
                                 rel_list t (Wr tag2 c k v2) (Rd tag c k ov)) →
                    ov = Some v1) ∧ 
  (* Transactions read from some write *)
  (∀ t tag c k v, t ∈ T → 
                  Rd tag c k (Some v) ∈ t →
                  ∃ t' tag' c', t' ∈ T ∧ Wr tag' c' k v ∈ t') ∧
  (* Transactions satisfy the baseline transaction contraints *)
  (∀ t, t ∈ T → valid_transaction t) ∧
  (* No duplicate transactions *)
  (∀ t1 t2 i j, T !! i = Some t1 → T !! j = Some t2 → t1 = t2 → i = j).

Definition state : Type := gmap Key val.

Definition execution : Type := list (transaction * state).

Definition commitTest : Type := execution -> transaction -> Prop.

Definition applyTransaction (s : state) (t : transaction) : state := 
  foldl (λ s op, match op with | Wr tag c k v => <[k := v]> s | _ => s end) s t.

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

Definition read_state (c : val) (k : Key) (ov : option val)
(exec : execution) (s : state) : Prop := 
  (s ∈ (split exec).2) ∧ 
  (s !! k = ov) ∧
  (∀ i j t', (split exec).2 !! i = Some s → 
             (split exec).1 !! j = Some t' →
             c = connOfTrans t' →
             i <= j).

Definition pre_read (exec : execution) (t : transaction) : Prop :=
  ∀ tag c k ov, (Rd tag c k ov) ∈ t →  ∃ s, read_state c k ov exec s.

Definition commit_test_rc : commitTest := 
  λ exec trans, pre_read exec trans.

(** Snapshot Isolation *)

Definition complete (exec : execution) (t : transaction)  (s : state): Prop := 
  ∀ tag c k ov, (Rd tag c k ov) ∈ t → read_state c k ov exec s.

Definition parent_state (exec : execution) (t : transaction) (s : state) : Prop :=
  ∃ i t' s', exec !! i = Some (t' , s) ∧ exec !! (i + 1) = Some (t, s').

Definition no_conf (exec : execution) (t : transaction) (s : state) : Prop := 
  ¬(∃ k, (∃ tag c v, Wr tag c k v ∈ t) ∧ 
         (∀ sp, parent_state exec t sp → s !! k ≠ sp !! k)). 

Definition commit_test_si : commitTest := 
  λ exec trans, ∃ s, s ∈ (split exec).2 ∧ 
                complete exec trans s ∧ 
                no_conf exec trans s.

(** Embedding into the trace infrastructure *)

Definition toOp (event : val) : option operation := 
  match event with 
    | (#(LitString tag), (c, (#"Rd", (#(LitString k), NONEV))))%V => Some (Rd tag c k None)
    | (#(LitString tag), (c, (#"Rd", (#(LitString k), SOMEV v))))%V => Some (Rd tag c k (Some v))
    | (#(LitString tag), (c, (#"Wr", (#(LitString k), v))))%V => Some (Wr tag c k v)
    | (#(LitString tag), (c, (#"Cm", #(LitBool b))))%V => Some (Cm tag c b)
    | _ => None (* We ignore start events *)
  end.

Definition toEvent (op : operation) : val := 
  match op with 
    | Rd tag c k None => (#tag, (c, (#"Rd", (#k, NONEV))))
    | Rd tag c k (Some v) => (#tag, (c, (#"Rd", (#k, SOMEV v))))
    | Wr tag c k v => (#tag, (c, (#"Wr", (#k, v))))
    | Cm tag c b => (#tag, (c, (#"Cm", #b)))
  end.

Definition extraction_of (trace : list val) (T : list transaction) : Prop := 
  (* Trace and transactions contain the same operations 
    (start operations are ignored and we are allowed to close transactions with commit operations) *)
  (∀ event op, event ∈ trace → toOp event = Some op → ∃ t, t ∈ T → op ∈ t) ∧
  (∀ t op, t ∈ T → op ∈ t → ¬(∃ tag c b, op = Cm tag c b) → (toEvent op) ∈ trace) ∧
  (∀ t op, t ∈ T → op ∈ t → (∃ tag c b, op = Cm tag c b) → 
           ((toEvent op) ∈ trace ∨ (∃ op', op' ∈ t ∧ (toEvent op') ∈ trace))) ∧
  (* Order amongst operations is preserved *)
  (∀ t op1 op2, t ∈ T → op1 ∈ t → op2 ∈ t → rel_list t op1 op2 → rel_list trace (toEvent op2) (toEvent op2)).

Definition is_st_event (v : val) : Prop := ∃ tag c, v = (#tag, (c, #"St"))%V.

Definition is_rd_event (v : val) : Prop := 
  (∃ tag c k v', v = (#tag, (c, (#"Rd", (#k, SOMEV v'))))%V) ∨ 
  (∃ tag c k, v = (#tag, (c, (#"Rd", (#k, NONEV))))%V).

Definition is_wr_event (v : val) : Prop := ∃ tag c k v', v = (tag, (c, (#"Wr", (#k, v'))))%V.

Definition is_cm_event (v : val) : Prop := ∃ tag c b, v = (tag, (c, (#"Cm", #b)))%V.

Definition valid_call_sequence (trace : list val) : Prop :=
  (* Read, write and commit events have a prior start event *)
  (∀ e c, e ∈ trace → 
             connOfEvent e = Some c → 
             (is_rd_event e ∨ is_wr_event e ∨ is_cm_event e) → 
             (∃ e_st, e_st ∈ trace ∧ connOfEvent e_st = Some c ∧ 
                      is_st_event e_st ∧ rel_list trace e_st e ∧  
                      (¬∃ e_cm, e_cm ∈ trace ∧ connOfEvent e_cm = Some c ∧ is_cm_event e_cm ∧ 
                                rel_list trace e_st e_cm ∧ rel_list trace e_cm e))) ∧
  (* There is is at most one active transaction per connection *)
  (∀ e_st c, e_st ∈ trace → 
             connOfEvent e_st = Some c → 
             is_st_event e_st → 
             ((∃ e_cm, e_cm ∈ trace ∧ connOfEvent e_cm = Some c ∧
                       is_cm_event e_cm ∧ rel_list trace e_st e_cm ∧ 
                       (¬∃ e_st', e_st' ∈ trace ∧ connOfEvent e_st' = Some c ∧ is_st_event e_st' ∧ 
                                  rel_list trace e_st e_st' ∧ rel_list trace e_st' e_cm)) ∨ 
             (¬∃ e, e ∈ trace ∧ connOfEvent e = Some c ∧ 
                     (is_st_event e ∨ is_cm_event e) ∧ rel_list trace e_st e))).

Definition comTrans (T : list transaction) : list transaction := 
  List.filter (λ t, match last t with | Some (Cm tag c true) => true | _ => false end) T.

Definition based_on (exec : execution) (transactions : list transaction) : Prop :=
  ∀ t, (t ∈ (split exec).1 ∧ t ≠ []) ↔ t ∈ transactions.

Definition valid_trace (test : commitTest) : list val → Prop :=
  λ trace, valid_call_sequence trace ∧ 
           (∃ T exec, valid_transactions T ∧ extraction_of trace T ∧  
                      based_on exec (comTrans T) ∧ valid_execution test exec).

Definition valid_trace_ru : list val → Prop := valid_trace commit_test_ru.

Definition valid_trace_rc : list val → Prop := valid_trace commit_test_rc.

Definition valid_trace_si : list val → Prop := valid_trace commit_test_si.

Lemma valid_trace_ru_empty : valid_trace_ru [].
Proof.
  rewrite /valid_trace_ru /valid_trace.
  split.
  - rewrite /valid_call_sequence.
    split; intros; set_solver.
  - intros.
    exists [], [([], ∅)].
    split.
    + rewrite /valid_transactions.
      split; first set_solver.
      split; set_solver.
    + split.
      * rewrite /extraction_of.
        do 3 (split; first set_solver).
        set_solver.
      * split.
        -- rewrite /based_on.
           intro t.
           split; set_solver.
        -- rewrite /valid_execution.
           split; last done.
           intros.
           destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
           destruct i; first done.
           set_solver.
Qed.

Lemma valid_trace_rc_empty : valid_trace_rc [].
  rewrite /valid_trace_rc /valid_trace.
  split.
  - rewrite /valid_call_sequence.
    split; intros; set_solver.
  - intros.
    exists [], [([], ∅)].
    split.
    + rewrite /valid_transactions.
      split; first set_solver.
      split; set_solver.
    + split.
      * rewrite /extraction_of.
        do 3 (split; first set_solver).
        set_solver.
      * split.
        -- rewrite /based_on.
           intro t.
           split; set_solver.
        -- rewrite /valid_execution.
           split.
           ++ intros.
              destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
              destruct i; first done.
              set_solver.
           ++ split; first done.
              intros.
              rewrite /commit_test_rc /pre_read.
              assert (t = []) as ->; set_solver.
Qed.

Lemma valid_trace_si_empty : valid_trace_si [].
  rewrite /valid_trace_si /valid_trace.
  split.
  - rewrite /valid_call_sequence.
    split; intros; set_solver.
  - intros.
    exists [], [([], ∅)].
    split.
    + rewrite /valid_transactions.
      split; first set_solver.
      split; set_solver.
    + split.
      * rewrite /extraction_of.
        do 3 (split; first set_solver).
        set_solver.
      * split.
        -- rewrite /based_on.
           intro t.
           split; set_solver.
        -- rewrite /valid_execution.
           split.
           ++ intros.
              destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
              destruct i; first done.
              set_solver.
           ++ split; first done.
              intros.
              rewrite /commit_test_si.
              exists ∅.
              simpl.
              split; first set_solver.
              assert (t = []) as ->; first set_solver.
              split.
              ** rewrite /complete.
                 set_solver.
              ** rewrite /no_conf.
                 set_solver.
Qed.