From iris.algebra Require Import gmap list.
From aneris.examples.transactional_consistency Require Import user_params.
From stdpp Require Import strings.
From aneris.aneris_lang Require Import network resources.

(* Type for tag-connection pairs. We assume tags are unique. *)
Definition signature : Type := string * val.

Inductive operation : Type :=
  | Rd (s : signature) (k : Key) (ov : option val) : operation 
  | Wr (s : signature) (k : Key) (v : val) : operation
  | Cm (s : signature) (b : bool) : operation.

#[global] Instance operation_eq_dec : EqDecision operation.
Proof. solve_decision. Defined.

Definition connOfOp (op : operation) : val :=
  match op with 
    | Rd (_, c) _ _ => c
    | Wr (_, c) _ _ => c
    | Cm (_, c) _ => c
  end.

Definition tagOfOp (op : operation) : string :=
  match op with 
    | Rd (tag, _) _ _ => tag
    | Wr (tag, _) _ _ => tag
    | Cm (tag, _) _ => tag
  end.

Definition connOfEvent (event : val) : option val :=
  match event with 
    | (_, (c, _))%V => Some c
    | _ => None
  end.

Definition tagOfEvent (event : val) : option string :=
  match event with 
    | (#(LitString tag), _)%V => Some tag
    | _ => None
  end.

Definition rel_list {A : Type} (l : list A) (a1 a2 : A) : Prop :=
  ∃ i j, i < j ∧ l !! i = Some a1 ∧ l !! j = Some a2.

Definition transaction : Type := list operation.

Definition valid_transaction (t : transaction) : Prop :=
  (* There is at most one commit operation and it is the last *)
  (∀ op s b, op ∈ t → op = Cm s b → last t = Some op) ∧
  (* Operations come from the same connection *)
  (∀ op1 op2, op1 ∈ t → op2 ∈ t → connOfOp op1 = connOfOp op2) ∧
  (* No duplicate operations *)
  (∀ op1 op2 i j, t !! i = Some op1 → t !! j = Some op2 → op1 = op2 → i = j) ∧
  (* Read your own writes *)
  (∀ tag c k ov tag1 v1,
    rel_list t (Wr (tag1, c) k v1) (Rd (tag, c) k ov) →
    (¬∃ tag2 v2, rel_list t (Wr (tag1, c) k v1) (Wr (tag2, c) k v2) ∧
                 rel_list t (Wr (tag2, c) k v2) (Rd (tag, c) k ov)) →
    ov = Some v1).

Definition connOfTrans (t : transaction) : option val :=
  match head t with | Some op => Some (connOfOp op) | None => None end.

Definition is_cm_op (op : operation) : Prop := ∃ s b, op = Cm s b.

Definition valid_transactions (T : list transaction) : Prop := 
  (* Transactions satisfy the baseline transaction contraints *)
  (∀ t, t ∈ T → valid_transaction t) ∧
  (* At most one open transactions per connection *) 
  (∀ t1 t2 op1 op2 i j c, T !! i = Some t1 → T !! j = Some t2 → 
                          last t1 = Some op1 → last t2 = Some op2 → 
                          connOfOp op1 = c → connOfOp op2 = c →
                          (¬is_cm_op op1) → (¬is_cm_op op2) →
                          i = j) ∧
  (* No duplicate operations across transactions *)
  (∀ op1 op2 t1 t2 i j, T !! i = Some t1 → T !! j = Some t2 → op1 ∈ t1 → op2 ∈ t2 → op1 = op2 → i = j).

Definition state : Type := gmap Key val.

Definition execution : Type := list (transaction * state).

Definition commitTest : Type := execution -> transaction -> Prop.

 Definition latest_write_trans (k : Key) (v : val) (trans : transaction) : Prop := 
    ∃ s, (Wr s k v) ∈ trans ∧ ¬(∃ s' v', rel_list trans (Wr s k v) (Wr s' k v')).

Definition applied_transaction (s1 s2 : state) (trans : transaction) : Prop :=
  (∀ k v, s2 !! k = Some v → 
    (∀ v', latest_write_trans k v' trans → v = v') ∧ (¬(∃ sig v', (Wr sig k v' ∈ trans)) → s1 !! k = Some v)) ∧
  (∀ k, ((∃ sig v, (Wr sig k v) ∈ trans) ∨ k ∈ dom s1) → k ∈ dom s2).

Definition valid_execution (test : commitTest) (exec : execution) : Prop :=
  (* Transitions are valid *)
  (∀ i e1 e2, exec !! i = Some e1 →
              exec !! (i + 1) = Some e2 →
              applied_transaction e1.2 e2.2 e2.1) ∧
  (* Initial state is valid *)
  (exec !! 0 = Some ([], ∅)) ∧
  (* The commit test is satisfied *)
  (∀ t, t ∈ (split exec).1 → test exec t) ∧
  (* The same transaction is not applied twice *)
  (∀ t1 t2 i j, (split exec).1 !! i = Some t1 → (split exec).1 !! j = Some t2 → t1 = t2 → i = j).

(** Read Uncommitted  *)

Definition commit_test_ru : commitTest := λ exec trans, true.

(** Read Committed  *)

Definition read_state (c : val) (k : Key) (ov : option val) (i : nat) 
(exec : execution) (s : state) : Prop := 
  ∃ j, j <= i ∧ (split exec).2 !! j = Some s ∧ s !! k = ov.

Definition pre_read (exec : execution) (t : transaction) : Prop :=
  ∀ tag c k ov i, (split exec).1 !! i = Some t → (Rd (tag, c) k ov) ∈ t → 
    (¬ ∃ s v, rel_list t (Wr s k v) (Rd (tag, c) k ov)) → (∃ v, ov = Some v) →
    ∃ s, read_state c k ov i exec s.

Definition commit_test_rc : commitTest := 
  λ exec trans, pre_read exec trans.

(** Snapshot Isolation *)

Definition complete (exec : execution) (t : transaction) (s : state): Prop := 
  ∀ tag c k ov i, (split exec).1 !! i = Some t → 
    (Rd (tag, c) k ov) ∈ t → 
    (¬ ∃ s v, rel_list t (Wr s k v) (Rd (tag, c) k ov)) →
    read_state c k ov i exec s.

Definition parent_state (exec : execution) (t : transaction) (s : state) : Prop :=
  ∃ i t' s', exec !! i = Some (t' , s) ∧ exec !! (i + 1) = Some (t, s').

Definition no_conf (exec : execution) (t : transaction) (s : state) : Prop := 
  ∀ i j, (split exec).2 !! i = Some s → (split exec).1 !! j = Some t → 
    ∀ i' t', i < i' < j → (split exec).1 !! i' = Some t' → 
      ∀ k, (∃ sig v, Wr sig k v ∈ t) → ¬ (∃ sig v, Wr sig k v ∈ t').

Definition commit_test_si : commitTest := 
  λ exec trans, ∃ s, s ∈ (split exec).2 ∧ 
                complete exec trans s ∧ 
                no_conf exec trans s.

(** Embedding into the trace infrastructure *)

Definition postToPre (event : val) : option val := 
  match event with 
    | (#(LitString tag), (c, (#"StPost")))%V => Some (#tag, (c, #"StPre"))%V
    | (#(LitString tag), (c, (#"RdPost", (#(LitString k), NONEV))))%V => Some (#tag, (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"RdPost", (#(LitString k), SOMEV v))))%V => Some (#tag, (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"WrPost", (#(LitString k), v))))%V => Some (#tag, (c, #"WrPre"))%V
    | (#(LitString tag), (c, (#"CmPost", #(LitBool b))))%V => Some (#tag, (c, #"CmPre"))%V
    | (#(LitString tag), (c, #"InPost"))%V => Some (#tag, (#"", #"InPre"))%V
    | _ => None 
  end.

Definition toLinEvent (op : operation) : val := 
  match op with 
    | Rd (tag, c) k None => (#tag, (c, (#"RdLin", (#k, NONEV))))
    | Rd (tag, c) k (Some v) => (#tag, (c, (#"RdLin", (#k, SOMEV v))))
    | Wr (tag, c) k v => (#tag, (c, (#"WrLin", (#k, v))))
    | Cm (tag, c) b => (#tag, (c, (#"CmLin", #b)))
  end.

Definition linToOp (le : val) : option operation := 
  match le with 
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), NONEV))))%V => Some (Rd (tag, c) k None)
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V => Some (Rd (tag, c) k (Some v))
    | (#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V => Some (Wr (tag, c) k v)
    | (#(LitString tag), (c, (#"CmLin", #(LitBool b))))%V => Some (Cm (tag, c) b)
    | _ => None 
  end.

Definition is_in_pre_event (v : val) : Prop := ∃ (tag : string), v = (#tag, #"InPre")%V.

Definition is_in_post_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"InPost"))%V.

Definition is_st_pre_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"StPre"))%V.

Definition is_st_post_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"StPost"))%V.

Definition is_rd_pre_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"RdPre"))%V.

Definition is_rd_post_event (v : val) : Prop := 
  (∃ (tag k : string) (c v': val), v = (#tag, (c, (#"RdPost", (#k, SOMEV v'))))%V) ∨ 
  (∃ (tag k : string) (c : val), v = (#tag, (c, (#"RdPost", (#k, NONEV))))%V).

Definition is_wr_pre_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"WrPre"))%V.

Definition is_wr_post_event (v : val) : Prop := ∃ (tag k : string) (c v' : val), v = (#tag, (c, (#"WrPost", (#k, v'))))%V.

Definition is_cm_pre_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"CmPre"))%V.

Definition is_cm_post_event (v : val) : Prop := ∃ (tag : string) (c : val) (b : bool), v = (#tag, (c, (#"CmPost", #b)))%V.

Definition is_pre_event (v : val) : Prop := 
  is_st_pre_event v ∨ is_rd_pre_event v ∨ is_wr_pre_event v ∨ is_cm_pre_event v ∨ is_in_pre_event v.

Definition is_post_event (v : val) : Prop := 
  is_st_post_event v ∨ is_rd_post_event v ∨ is_wr_post_event v ∨ is_cm_post_event v ∨ is_in_post_event v.

Definition is_in_lin_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"InLin"))%V.

Definition is_st_lin_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"StLin"))%V.

Definition is_rd_lin_event (v : val) : Prop := 
  (∃ (tag k : string) (c v' : val), v = (#tag, (c, (#"RdLin", (#k, SOMEV v'))))%V) ∨ 
  (∃ (tag k : string) (c : val), v = (#tag, (c, (#"RdLin", (#k, NONEV))))%V).

Definition is_wr_lin_event (v : val) : Prop := ∃ (tag k : string) (c v' : val), v = (#tag, (c, (#"WrLin", (#k, v'))))%V.

Definition is_cm_lin_event (v : val) : Prop := ∃ (tag : string) (c : val) (b : bool), v = (#tag, (c, (#"CmLin", #b)))%V.

Definition is_lin_event (v : val) : Prop := 
  is_st_lin_event v ∨ is_rd_lin_event v ∨ is_wr_lin_event v ∨ is_cm_lin_event v ∨ is_in_lin_event v.

Definition extraction_of (lin_trace : list val) (T : list transaction) : Prop := 
  (* Linerization point trace and transactions contain the same operations *)
  (∀ le op, le ∈ lin_trace → linToOp le = Some op → ∃ t, t ∈ T ∧ op ∈ t) ∧
  (∀ t op, t ∈ T → op ∈ t → (toLinEvent op) ∈ lin_trace) ∧
  (* Order amongst operations is preserved *)
  (∀ t op1 op2, t ∈ T → rel_list t op1 op2 → rel_list lin_trace (toLinEvent op1) (toLinEvent op2)).

Definition no_later_start_or_commit (c e_st : val) (lin_trace : list val) : Prop := 
  ¬∃ e, connOfEvent e = Some c ∧ rel_list lin_trace e_st e ∧
        (is_st_lin_event e ∨ is_cm_lin_event e).

Definition later_commit (c e_st : val) (lin_trace : list val) : Prop := 
  ∃ e_cm, connOfEvent e_cm = Some c ∧ is_cm_lin_event e_cm ∧ rel_list lin_trace e_st e_cm ∧ 
          (¬∃ e_st', connOfEvent e_st' = Some c ∧ is_st_lin_event e_st' ∧ 
                    rel_list lin_trace e_st e_st' ∧ rel_list lin_trace e_st' e_cm).

Definition commit_closed (c : val) (lin_trace : list val) : Prop :=
  ∀ e_st, e_st ∈ lin_trace → connOfEvent e_st = Some c → 
          is_st_lin_event e_st → later_commit c e_st lin_trace.

Definition prior_start (c e : val) (lin_trace : list val) : Prop := 
  ∃ e_st, connOfEvent e_st = Some c ∧ is_st_lin_event e_st ∧ rel_list lin_trace e_st e ∧ 
          (¬∃ e_cm, connOfEvent e_cm = Some c ∧ is_cm_lin_event e_cm ∧
                    rel_list lin_trace e_st e_cm ∧ rel_list lin_trace e_cm e).

Definition prior_init (i : nat) (c : val) (lin_trace : list val) : Prop := 
  (∃ e_init j, lin_trace !! j = Some e_init ∧ connOfEvent e_init = Some c ∧
               is_in_lin_event e_init ∧ j <= i).

Definition unique_init_events (lin_trace : list val) : Prop :=
  ∀ e e' c i j, lin_trace !! i = Some e → is_in_lin_event e → connOfEvent e = Some c → 
                lin_trace !! j = Some e' → is_in_lin_event e' → connOfEvent e' = Some c →
                i = j.

(* This is to be used with traces of linearization point events *)
Definition valid_sequence (lin_trace : list val) : Prop :=
  (* All operations have a prior init event for their connections *)
  (∀ e c i, lin_trace !! i = Some e → 
            connOfEvent e = Some c → 
            prior_init i c lin_trace) ∧
  (* At most one init event per connection  *)
  unique_init_events lin_trace ∧
  (* Read, write and commit events have a prior start event *)
  (∀ e c, e ∈ lin_trace → 
          connOfEvent e = Some c → 
          (is_rd_lin_event e ∨ is_wr_lin_event e ∨ is_cm_lin_event e) → 
          prior_start c e lin_trace) ∧
  (* There is at most one active transaction per connection *)
  (∀ e_st c, e_st ∈ lin_trace → 
             connOfEvent e_st = Some c → 
             is_st_lin_event e_st → 
             (later_commit c e_st lin_trace ∨ no_later_start_or_commit c e_st lin_trace)) ∧
  (* Reads happen from prior writes *)
  (∀ i tag c k v, lin_trace !! i = Some (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V →
      ∃ j tag' c', j < i ∧ 
          lin_trace !! j = Some (#(LitString tag'), (c', (#"WrLin", (#(LitString k), v))))%V).

Definition comTrans (T : list transaction) : list transaction := 
  List.filter (λ t, match last t with | Some (Cm s true) => true | _ => false end) T.

Definition based_on (exec : execution) (T : list transaction) : Prop :=
  ∀ t, (t ∈ (split exec).1 ∧ t ≠ []) ↔ t ∈ T.

Definition linToPost (lin_event : val) : option val := 
  match lin_event with 
    | (#(LitString tag), (c, (#"InLin")))%V => 
      Some (#(LitString tag), (c, (#"InPost")))%V
    | (#(LitString tag), (c, (#"StLin")))%V => 
      Some (#(LitString tag), (c, (#"StPost")))%V
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), NONEV))))%V => 
      Some (#(LitString tag), (c, (#"RdPost", (#(LitString k), NONEV))))%V
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V => 
      Some (#(LitString tag), (c, (#"RdPost", (#(LitString k), SOMEV v))))%V
    | (#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V => 
      Some (#(LitString tag), (c, (#"WrPost", (#(LitString k), v))))%V
    | (#(LitString tag), (c, (#"CmLin", #(LitBool b))))%V => 
      Some (#(LitString tag), (c, (#"CmPost", #(LitBool b))))%V
    | _ => None 
  end.

Definition linToPre (lin_event : val) : option val := 
  match lin_event with 
    | (#(LitString tag), (c, (#"InLin")))%V => 
      Some (#(LitString tag), #"InPre")%V
    | (#(LitString tag), (c, (#"StLin")))%V => 
      Some (#(LitString tag), (c, #"StPre"))%V
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), NONEV))))%V => 
      Some (#(LitString tag), (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V => 
      Some (#(LitString tag), (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V => 
      Some (#(LitString tag), (c, #"WrPre"))%V
    | (#(LitString tag), (c, (#"CmLin", #(LitBool b))))%V => 
      Some (#(LitString tag), (c, #"CmPre"))%V
    | _ => None 
  end.

Definition postToLin (event : val) : option val := 
  match event with 
    | (#(LitString tag), (c, (#"InPost")))%V => 
      Some (#(LitString tag), (c, (#"InLin")))%V
    | (#(LitString tag), (c, (#"StPost")))%V => 
      Some (#(LitString tag), (c, (#"StLin")))%V
    | (#(LitString tag), (c, (#"RdPost", (#(LitString k), NONEV))))%V => 
      Some (#(LitString tag), (c, (#"RdLin", (#(LitString k), NONEV))))%V
    | (#(LitString tag), (c, (#"RdPost", (#(LitString k), SOMEV v))))%V => 
      Some (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V
    | (#(LitString tag), (c, (#"WrPost", (#(LitString k), v))))%V => 
      Some (#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V
    | (#(LitString tag), (c, (#"CmPost", #(LitBool b))))%V => 
      Some (#(LitString tag), (c, (#"CmLin", #(LitBool b))))%V
    | _ => None
  end.

Definition lin_trace_of (lin_trace trace : list val) : Prop := 
  (* Trace of linearization points *)
  (∀ le, le ∈ lin_trace → is_lin_event le) ∧
  (* Elements are preserved *)
  (∀ e_post, e_post ∈ trace → ∀ le, postToLin e_post = Some le → le ∈ lin_trace) ∧
  (∀ le, le ∈ lin_trace → ∃ e_pre, is_pre_event e_pre ∧ linToPre le = Some e_pre ∧ e_pre ∈ trace ∧ 
                                    (∀ e_post, (e_post ∈ trace ∧ is_post_event e_post ∧ postToPre e_post = Some e_pre) 
                                               → linToPost le = Some e_post)) ∧
  (* Order is preserved *)
  (∀ le1 le2, rel_list lin_trace le1 le2 → 
              ¬(∃ e1_pre e2_post, linToPre le1 = Some e1_pre ∧
                                  linToPost le2 = Some e2_post  ∧
                                  rel_list trace e2_post e1_pre)) ∧
  (* Only one linearization point per operation *)
  (∀ le1 le2 i j tag, lin_trace !! i = Some le1 → lin_trace !! j = Some le2 →
                      tagOfEvent le1 = Some tag → tagOfEvent le2 = Some tag → i = j).

Definition valid_trace (test : commitTest) : list val → Prop :=
  λ trace, ∃ lin_trace, lin_trace_of lin_trace trace ∧ valid_sequence lin_trace ∧ 
           (∃ T exec, valid_transactions T ∧ extraction_of lin_trace T ∧
                      based_on exec (comTrans T) ∧ valid_execution test exec).

Definition valid_trace_ru : list val → Prop := valid_trace commit_test_ru.

Definition valid_trace_rc : list val → Prop := valid_trace commit_test_rc.

Definition valid_trace_si : list val → Prop := valid_trace commit_test_si.

(** Helper definitions related to the state-based model *)

Definition optional_applied_transaction (exec : execution) (s : state) (trans : transaction) : Prop :=
  (∃ s' t', last exec = Some (t', s') ∧ applied_transaction s' s trans) ∨ 
  (last exec = None ∧ applied_transaction ∅ s trans).

Definition optionalExtendExecution (e : execution) (t : transaction) (s : state) : execution :=
  match (last t) with | Some (Cm _ true) => e ++ [(t, s)] | _ => e end.

Definition isCmOp (op : operation) : bool := match op with | Cm _ _ => true | _ => false end.

Definition isWrOp (op : operation) (k : Key) : bool := match op with | Wr _ k' _ => bool_decide (k = k') | _ => false end.

(** Helper lemmas related to the state-based model *)

Lemma valid_trace_ru_empty : valid_trace_ru [].
Proof.
  rewrite /valid_trace_ru /valid_trace.
  exists [].
  repeat (split_and!; rewrite /rel_list /commit_test_ru /lin_trace_of 
    /valid_sequence /unique_init_events /based_on /extraction_of); try set_solver.
  exists [], [([], ∅)].
  repeat (split_and!; try set_solver).
  - intros i.
    destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
    destruct i; first done.
    set_solver.
  - simpl.
    intros t1 t2 i j Hlookup_i Hlookup_j Heq.
    rewrite list_lookup_singleton_Some in Hlookup_i.
    rewrite list_lookup_singleton_Some in Hlookup_j.
    lia.
Qed.

Lemma valid_trace_rc_empty : valid_trace_rc [].
  rewrite /valid_trace_rc /valid_trace.
  exists [].
  repeat (split_and!; rewrite /rel_list /commit_test_rc /pre_read /lin_trace_of
    /valid_sequence /unique_init_events /based_on /extraction_of); try set_solver.
  exists [], [([], ∅)].
  repeat (split_and!; try set_solver).
  - intros i.
    destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
    destruct i; first done.
    set_solver.
  - intros t Ht_in.
    assert (t = []) as ->; set_solver.
  - simpl.
    intros t1 t2 i j Hlookup_i Hlookup_j Heq.
    rewrite list_lookup_singleton_Some in Hlookup_i.
    rewrite list_lookup_singleton_Some in Hlookup_j.
    lia.
Qed.

Lemma valid_trace_si_empty : valid_trace_si [].
  rewrite /valid_trace_si /valid_trace.
  exists [].
  repeat (split_and!; rewrite /rel_list /commit_test_si /complete /no_conf 
    /lin_trace_of /valid_sequence /unique_init_events /based_on /extraction_of); try set_solver.
  exists [], [([], ∅)].
  repeat (split_and!; try set_solver).
  - intros i.
    destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
    destruct i; first done.
    set_solver.
  - intros t Ht_in.
    assert (t = []) as ->; set_solver.
  - simpl.
    intros t1 t2 i j Hlookup_i Hlookup_j Heq.
    rewrite list_lookup_singleton_Some in Hlookup_i.
    rewrite list_lookup_singleton_Some in Hlookup_j.
    lia.
Qed.

Lemma rel_list_imp {A : Type} (l : list A) e1 e2 e : 
  rel_list l e1 e2 → rel_list (l ++ [e]) e1 e2.
Proof.
  rewrite /rel_list.
  intros (i & j & Hlt & Hlookup_i & Hlookup_j).
  exists i, j.
  split_and!; try done; by apply lookup_app_l_Some.
Qed.

Lemma rel_list_imp_cons {A : Type} (l : list A) e1 e2 e : 
  rel_list l e1 e2 → rel_list (e :: l) e1 e2.
Proof.
  intros (i & j & Hlt & Hlookup_i & Hlookup_j).
  exists (S i), (S j).
  split_and!; first lia.
  1, 2 : rewrite lookup_cons_Some; right; simpl.
  1, 2 : split; first lia.
  1 : by assert (i = i - 0) as <-; first lia.
  by assert (j = j - 0) as <-; first lia.
Qed.

Lemma rel_singleton_false {A : Type} (e e1 e2 : A) :
  ¬ rel_list [e] e1 e2.
Proof.
  intros (i & j & Hlt & Hlookup_i & Hlookup_j).
  rewrite list_lookup_singleton_Some in Hlookup_i.
  rewrite list_lookup_singleton_Some in Hlookup_j.
  lia.
Qed.

Lemma rel_list_last_neq {A : Type} (l : list A) e1 e2 e : 
  e ≠ e2 → rel_list (l ++ [e]) e1 e2 → rel_list l e1 e2. 
Proof.
  intros Hneq Hrel.
  destruct Hrel as (i & j & Hlt & Hlookup_i & Hlookup_j).
  apply lookup_snoc_Some in Hlookup_i, Hlookup_j.
  destruct Hlookup_i as [(Hlength & Hlookup_i) | (-> & ->)]; last lia.
  destruct Hlookup_j as [(Hlength' & Hlookup_j) | (-> & ->)]; last done.
  by exists i, j.
Qed.

Lemma rel_list_in {A : Type} (l : list A) e1 e2 e : 
  rel_list (l ++ [e]) e1 e2 → e1 ∈ l. 
Proof.
  intros (i & j & Hlt & Hlookup_i & Hlookup_j).
  apply lookup_snoc_Some in Hlookup_i, Hlookup_j.
  destruct Hlookup_i as [(Hlength & Hlookup_i) | (-> & ->)]; last lia.
  apply elem_of_list_lookup.
  set_solver.
Qed.

Lemma split_split {A B : Type} (l1 l2 : list (A * B)) :
  split (l1 ++ l2) = ((split l1).1 ++ (split l2).1, (split l1).2 ++ (split l2).2).
Proof.
  generalize l2.
  induction l1.
  - intro l1.
    simpl.
    by destruct (split l1).
  - intro l.
    destruct a.
    simpl split.
    rewrite (IHl1 l).
    by destruct (split l1).
Qed.

Lemma split_append {A B : Type} (a : A) (l1 l2 : list (A * B)) :
  a ∈ (split l1).1 → a ∈ (split (l1 ++ l2)).1.
Proof.
  intro H.
  rewrite split_split.
  simpl.
  set_solver.
Qed.

Lemma split_prefix {A B : Type} (l1 l2 : list (A * B)) :
  l1 `prefix_of` l2 →
  (split l1).2 `prefix_of` (split l2).2.
Proof.
  generalize dependent l2.
  induction l1 as [|h1 l1 IH].
  - intros l2 _.
    apply prefix_nil.
  - intros l2 Hprefix.
    destruct l2 as [|h2 l2].
    + exfalso.
      by eapply prefix_nil_not.
    + pose proof Hprefix as Hprefix'.
      apply prefix_cons_inv_2 in Hprefix.
      specialize (IH l2 Hprefix).
      apply prefix_cons_inv_1 in Hprefix'.
      rewrite -Hprefix'.
      assert (h1 :: l1 = [h1] ++ l1) as ->; first set_solver.
      assert (h1 :: l2 = [h1] ++ l2) as ->; first set_solver.
      do 2 rewrite split_split.
      simpl.
      destruct h1 as [a b].
      simpl.
      by apply prefix_cons.
Qed.

Lemma applied_transaction_exists s t : 
  ∃ s', applied_transaction s s' t.
Proof.
  generalize dependent s.
  induction t as [|op t IH]; intros s.
  - exists s.
    rewrite /applied_transaction /latest_write_trans.
    set_solver.
  - destruct op as [|sig k v|].
    + destruct (IH s) as (s' & Happl1 & Happl2).
      exists s'.
      split; last set_solver.
      rewrite /latest_write_trans.
      intros k' v Hlookup.
      specialize (Happl1 k' v Hlookup).
      split; last set_solver.
      intros v' (sig' & Hwr_in & Hnot).
      destruct Happl1 as (Happl1 & _).
      apply Happl1.
      exists sig'.
      split; first set_solver.
      intros (sig'' & v'' & Hrel).
      apply Hnot.
      exists sig'', v''.
      by eapply rel_list_imp_cons.
    + assert (Decision (∃ op, op ∈ t ∧ (λ op, isWrOp op k = true) op)) as Hdec_pre.
      {
        apply list_exist_dec.
        apply _.
      }
      destruct (IH s) as (s' & IH').
      destruct (decide (∃ op, op ∈ t ∧ (λ op, isWrOp op k = true) op)) as [Hdec | Hdec].
      * exists s'.
        split.
        -- intros k' v' Hlookup.
           destruct IH' as (IH' & _).
           destruct (IH' k' v' Hlookup) as (IH'_1 & IH'_2).
           split; last set_solver.
           intros v'' (sig' & Hin & Hnot).
           apply IH'_1.
           exists sig'.
           rewrite elem_of_cons in Hin.
           destruct Hin as [Hin|Hin].
           ++ exfalso.
              apply Hnot.
              rewrite Hin.
              destruct Hdec as (op & Hop_in & Hwr).
              destruct op as [|sig'' k'' v'''|]; try done.
              exists sig'', v'''.
              assert (k = k') as <-; first set_solver.
              simpl in Hwr.
              rewrite bool_decide_decide in Hwr.
              destruct (decide (k = k'')) as [<-|Hneq]; last done.
              rewrite elem_of_list_lookup in Hop_in.
              destruct Hop_in as (j & Hop_in).
              exists 0, (S j).
              split_and!; first lia; set_solver.
           ++ split_and!; first set_solver.
              intros (sig'' & v''' & Hrel).
              apply Hnot.
              exists sig'', v'''.
              by eapply rel_list_imp_cons.
        -- intros k' Hor.
           destruct IH' as (_ & IH').
           apply IH'.
           destruct Hor as [(sig'' & v'' & Hin)|Hin]; last set_solver.
           left.
           rewrite elem_of_cons in Hin.
           destruct Hin as [Hin|Hin]; last set_solver.
           destruct Hdec as (op & Hin_op & Hwr).
           assert (k' = k) as ->; first set_solver.
           destruct op as [|sig''' k''' v'''|]; try done.
           simpl in Hwr.
           rewrite bool_decide_decide in Hwr.
           destruct (decide (k = k''')) as [<-|]; set_solver.
      * exists (<[k := v]> s').
        split.
        -- intros k' v'.
           destruct (decide (k = k')) as [Heq|Hneq].
           ++ subst.
              rewrite lookup_insert.
              intros Heq.
              split; last set_solver.
              intros  v'' (sig' & Hin & _).
              rewrite elem_of_cons in Hin.
              destruct Hin as [Hin|Hin]; first set_solver.
              exfalso.
              apply Hdec.
              exists (Wr sig' k' v'').
              split; try done.
              simpl.
              rewrite bool_decide_decide.
              destruct (decide (k' = k')); set_solver.
           ++ rewrite lookup_insert_ne; last done.
              intro Hlookup.
              destruct IH' as (IH' & _).
              destruct (IH' k' v' Hlookup) as (IH'_1 & IH'_2).
              split; last set_solver.
              intros v'' (sig' & Hin & Hnot).
              apply IH'_1.
              exists sig'.
              split_and!; first set_solver.
              intros (sig'' & v''' & Hrel).
              apply Hnot.
              exists sig'', v'''.
              by eapply rel_list_imp_cons.
        -- intros k' Hor. 
           destruct (decide (k = k')) as [<-|Hneq]; first set_solver.
           assert (k' ∈ dom s') as Hin; last set_solver.
           destruct IH' as (_ & IH').
           set_solver.
    + destruct (IH s) as (s' & Happl1 & Happl2).
      exists s'.
      split; last set_solver.
      rewrite /latest_write_trans.
      intros k' v Hlookup.
      specialize (Happl1 k' v Hlookup).
      split; last set_solver.
      intros v' (sig' & Hwr_in & Hnot).
      destruct Happl1 as (Happl1 & _).
      apply Happl1.
      exists sig'.
      split; first set_solver.
      intros (sig'' & v'' & Hrel).
      apply Hnot.
      exists sig'', v''.
      by eapply rel_list_imp_cons.
Qed.

Lemma optional_applied_transaction_exists exec t : 
  ∃ s, optional_applied_transaction exec s t.
Proof.
  destruct (last exec) as [(t', s') |] eqn:Hlast.
  - destruct (applied_transaction_exists s' t) as (s & Happlied).
    exists s.
    left.
    set_solver.
  - destruct (applied_transaction_exists ∅ t) as (s & Happlied).
    exists s.
    right.
    set_solver.
Qed.

Lemma split_lookup_eq (exec : execution) i p1 p1' p2 :
  (split exec).1 !! i = Some p1' →
  exec !! i = Some (p1, p2) → 
  p1 = p1'.
Proof.
  generalize dependent i.
  induction exec as [|(h1, h2) exec IH].
  - simpl. 
    set_solver.
  - intros i Hlookup1 Hlookup2.
    assert ((h1, h2) :: exec = [(h1, h2)] ++ exec) as Heq_cons_app; first set_solver.
    rewrite Heq_cons_app in Hlookup1.
    rewrite split_split in Hlookup1.
    simpl in Hlookup1.
    rewrite lookup_cons_Some in Hlookup2.
    destruct Hlookup2 as [(Heq_i & Heq_h)|(Hlength & Hlookup2)].
    + subst.
      assert (h1 :: (split exec).1 = [h1] ++ (split exec).1) as Heq_cons_app'; first set_solver.
      rewrite Heq_cons_app' in Hlookup1.
      rewrite lookup_app_Some in Hlookup1.
      destruct Hlookup1 as [Hlookup1 | Hfalse]; first set_solver.
      simpl in Hfalse.
      lia.
    + assert (h1 :: (split exec).1 = [h1] ++ (split exec).1) as Heq_cons_app'; first set_solver.
      rewrite Heq_cons_app' in Hlookup1.
      rewrite lookup_app_Some in Hlookup1.
      destruct Hlookup1 as [Hfalse | Hlookup1]; last set_solver.
      rewrite list_lookup_singleton_Some in Hfalse.
      lia.
Qed.

Lemma latest_write_read exec T k v trans test : 
  valid_execution test exec →
  based_on exec T →
  trans ∈ T →
  latest_write_trans k v trans →
  ∃ s, s ∈ (split exec).2 ∧ s !! k = Some v. 
Proof.
  intros (Hvalid & Hzero & _) Hbased Hin Hlatest.
  rewrite /based_on in Hbased.
  assert (trans ∈ (split exec).1) as Hin'; first set_solver.
  apply elem_of_list_lookup_1 in Hin'.
  destruct Hin' as (i & Hin').
  pose proof Hin' as Hlength.
  apply lookup_lt_Some in Hlength.
  rewrite split_length_l in Hlength.
  destruct (exec !! i) as [(trans', s)|] eqn:Hlookup.
  - exists s.
    assert (trans' = trans) as ->; first by eapply split_lookup_eq.
    split.
    + apply elem_of_list_In.
      assert ((trans, s).2 = s) as <-; first by simpl.
      apply in_split_r.
      apply elem_of_list_In.
      apply elem_of_list_lookup.
      set_solver.
    + destruct (exec !! (pred i)) as [p_prior|] eqn:Hlookup_prior.
      * assert (applied_transaction p_prior.2 (trans, s).2 (trans, s).1) as (Happlied1 & Happlied2).
        {
          eapply (Hvalid (pred i)); try done.
          assert ((pred i + 1) = i) as ->; last done.
          rewrite PeanoNat.Nat.add_1_r.
          apply Nat.succ_pred.
          intro Hfalse.
          subst.
          rewrite /latest_write_trans in Hlatest.
          assert ([] = trans) as <-; last set_solver.
          rewrite Hlookup in Hzero.
          by inversion Hzero.
        }
        simpl in Happlied1, Happlied2.
        destruct (s !! k) as [v'|] eqn:Hlookup_state; first set_solver.
        exfalso.
        assert (k ∈ dom s) as Hdom. 
        {
          apply Happlied2.
          left.
          rewrite /latest_write_trans in Hlatest.
          set_solver.
        }
        rewrite elem_of_dom Hlookup_state in Hdom.
        rewrite /is_Some in Hdom; set_solver.
      * apply lookup_ge_None_1 in Hlookup_prior.
        lia.
  - apply lookup_ge_None_1 in Hlookup.
    exfalso.
    lia.
Qed.

Lemma com_trans_eq1 op T1 T2 trans:
  ¬is_cm_op op →
  (∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false) →
  comTrans (T1 ++ trans :: T2) = comTrans (T1 ++ (trans ++ [op]) :: T2).
Proof.
  intros Hnot Hop.
  rewrite /comTrans.
  do 2 rewrite List.filter_app.
  simpl.
  destruct Hop as (op' & _ & Heq & Hcm_op).
  rewrite Heq.
  rewrite /isCmOp in Hcm_op.
  rewrite /is_cm_op in Hnot.
  destruct op'; last set_solver.
  all : destruct op.
  3, 6 : set_solver.
  all : rewrite last_snoc; done.
Qed.

Lemma com_trans_eq2 op T :
  ¬is_cm_op op →
  comTrans T = comTrans (T ++ [[op]]).
Proof.
  intros Hnot.
  rewrite /comTrans.
  rewrite List.filter_app.
  simpl.
  rewrite /is_cm_op in Hnot.
  destruct op; last set_solver; simpl; by rewrite app_nil_r.
Qed. 

Lemma com_trans_eq3 T1 T2 trans s:
  (∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false) →
  comTrans (T1 ++ trans :: T2) = comTrans (T1 ++ (trans ++ [Cm s false]) :: T2).
Proof.
  intros Hop.
  rewrite /comTrans.
  do 2 rewrite List.filter_app.
  simpl.
  rewrite last_snoc.
  destruct Hop as (op' & _ & Heq & Hcm_op).
  rewrite Heq.
  rewrite /isCmOp in Hcm_op.
  destruct op'; set_solver.
Qed.

Lemma com_trans_eq4 T1 T2 trans :
  (∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false) →
  comTrans (T1 ++ trans :: T2) = comTrans (T1 ++ T2).
Proof.
  intros Hop.
  rewrite /comTrans.
  do 2 rewrite List.filter_app.
  simpl.
  destruct Hop as (op' & _ & Heq & Hcm_op).
  rewrite Heq.
  rewrite /isCmOp in Hcm_op.
  destruct op'; set_solver.
Qed.

Lemma com_trans_imp1 T1 T2 trans t:
  t ∈ comTrans (T1 ++ T2) →
  t ∈ comTrans (T1 ++ trans :: T2).
Proof.
  rewrite /comTrans.
  do 2 rewrite List.filter_app.
  do 2 rewrite elem_of_app.
  intros Hin.
  simpl.
  destruct Hin as [Hin|Hin]; first set_solver.
  right.
  destruct (last trans) as [op|]; last set_solver.
  destruct op; try done.
  destruct b; set_solver.
Qed.

Lemma com_trans_imp2 t T :
  t ∈ comTrans T →
  t ∈ T.
Proof.
  induction T as [|h tail IH]; first (simpl; set_solver).
  simpl.
  destruct (last h) as [op|]; last set_solver.
  destruct op.
  1, 2 : set_solver.
  destruct b; set_solver.
Qed.

Lemma exists_execution : 
  ∀ T, (∀ t, t ∈ T → t ≠ []) → valid_transactions T →
    ∃ E, based_on E (comTrans T) ∧ valid_execution commit_test_ru E.
Proof.
  intros T Himp Hvalid_trans.
  induction T as [|t T IH].
  - exists [([], ∅)].
    split.
    + simpl.
      rewrite /based_on.
      intro t.
      simpl.
      set_solver.
    + rewrite /valid_execution /commit_test_ru.
      split.
      * intros.
        destruct i; set_solver.
      * do 2 (split; first set_solver).
        simpl.
        intros t1 t2 i j Hlookup_i Hlookup_j Heq.
        rewrite list_lookup_singleton_Some in Hlookup_i.
        rewrite list_lookup_singleton_Some in Hlookup_j.
        lia.
  - assert (∀ t : list operation, t ∈ T → t ≠ []) as Himp'.
    {
      intros t' Hin.
      apply Himp.
      set_solver.
    }
    assert (valid_transactions T) as Hvalid_trans'.
    {
      rewrite /valid_transactions in Hvalid_trans.
      split_and!; first set_solver.
      - intros t1 t2 op1 op2 i j c Hlookup_i Hlookup_j Hlast1 Hlast2 Hconn1 Hconn2 Hcm1 Hcm2.
        destruct Hvalid_trans as (_ & Hvalid_trans & _).
        assert ((S i) = (S j)) as Heq; last lia.
        eapply (Hvalid_trans); try done.
      - intros op1 op2 t1 t2 i j Hlookup_i Hlookup_j Hop1 Hop2 Heq.
        destruct Hvalid_trans as (_ & _ & Hvalid_trans).
        assert ((S i) = (S j)) as Heq'; last lia.
        eapply (Hvalid_trans); try done.
    }
    destruct (IH Himp' Hvalid_trans') as [E (Hbased & Hexec)].
    simpl.
    assert (∃ E0 : execution, based_on E0 (comTrans T) ∧ valid_execution commit_test_ru E0) as Hcase; first by exists E.
    destruct (last t); try done.
    destruct o; try done.
    destruct b; try done.
    destruct (last E) as [p|] eqn:Heq.
    + destruct (applied_transaction_exists p.2 t) as (s' & Happly).
      exists (E ++ [(t, s')]).
      split.
      * rewrite /based_on.
        intro t'.
        split.
        -- intros (Hin & Hneq).
           rewrite /based_on in Hbased.
           destruct (Hbased t') as (Hbased' & _).
           rewrite split_split in Hin.
           simpl in Hin.
           rewrite elem_of_app in Hin.
           destruct Hin as [Hin|Hin]; last set_solver.
           assert (t' ∈ comTrans T); last set_solver.
           by apply Hbased'.
        -- intro Hin. 
           rewrite elem_of_cons in Hin.
           destruct Hin as [-> | Hin].
           ++ rewrite split_split.
              simpl.
              set_solver.
           ++ split.
              ** specialize (Hbased t'). 
                 apply Hbased in Hin as (Hin & _).
                 by apply split_append.
              ** apply Himp'.
                 assert (comTrans T ⊆ T) as Hsub; last set_solver.
                 apply elem_of_subseteq.
                 intros t'' Hin''.
                 rewrite elem_of_list_In.
                 rewrite elem_of_list_In /comTrans filter_In in Hin''.
                 by destruct Hin'' as (Hgoal & _).
      * rewrite /valid_execution.
        split.
        -- intros i p1 p2 Hlookup1 Hlookup2.
           rewrite lookup_snoc_Some in Hlookup2.
           destruct Hlookup2 as [Hlookup2 | Hlookup2].
           ++ rewrite lookup_snoc_Some in Hlookup1.
              destruct Hlookup1 as [Hlookup1 | Hlookup1].
              ** destruct Hexec as (Hexec & _).
                 destruct Hlookup1 as (_  & Hlookup1).
                 destruct Hlookup2 as (_  & Hlookup2).
                 apply (Hexec i p1 p2 Hlookup1 Hlookup2).
              ** destruct Hlookup1 as (Hlookup1 & _).
                 destruct Hlookup2 as (Hlookup2 & _).
                 lia.
           ++ destruct Hlookup2 as (Hlength & <-).
              simpl.
              assert (p = p1) as ->; last done.
              assert (length (E ++ [(t, s')]) = i + 2) as Hlength'.
              {
                rewrite app_length.
                rewrite -Hlength.
                simpl.
                lia.
              }
              rewrite last_lookup in Heq.
              rewrite -Hlength in Heq.
              assert (i = pred (i + 1)) as Heq_i.
              {
                destruct i; simpl; lia.
              }
              rewrite -Heq_i in Heq.
              rewrite lookup_app_Some in Hlookup1.
              destruct Hlookup1 as [Heq_p1|(Hfalse & _)]; first set_solver.
              lia.
        -- destruct Hexec as (_ & Hexec1 & _ & Hexec2).
           split_and!.
           ++ rewrite lookup_app_Some.
              by left.
           ++ intros.
              by rewrite /commit_test_ru.
           ++ intros t1 t2 i j Hlookup_i Hlookup_j Heq_trans.
              rewrite split_split in Hlookup_i; simpl in Hlookup_i.
              rewrite split_split in Hlookup_j; simpl in Hlookup_j.
              rewrite lookup_app_Some in Hlookup_i.
              rewrite lookup_app_Some in Hlookup_j.
              destruct Hvalid_trans as (_ & Hvalid_trans).
              destruct Hlookup_i as [Hlookup_i|Hlookup_i].
              ** destruct Hlookup_j as [Hlookup_j|Hlookup_j]; first set_solver.
                 assert (t = t2) as Heq_trans'; 
                  first (rewrite list_lookup_singleton_Some in Hlookup_j; set_solver).
                 rewrite /based_on in Hbased.
                 assert (t ∈ T) as Ht_in.
                 {
                   apply com_trans_imp2, Hbased.
                   split; last set_solver. 
                   apply elem_of_list_lookup; set_solver.
                 }
                 rewrite /valid_transactions in Hvalid_trans.
                 rewrite elem_of_list_lookup in Ht_in.
                 destruct Ht_in as (i' & Ht_in).
                 assert ((t :: T) !! (S i') = Some t) as Hlookup_succ.
                 { 
                    apply lookup_cons_Some; right.
                    split; first lia.
                    simpl.
                    by assert (i' = i' - 0) as <-; first lia.
                 }
                 assert ((t :: T) !! 0 = Some t) as Hlookup_zero; first set_solver.
                 assert (0 = S i') as Hfalse; last lia.
                 destruct t as [|h t]; first set_solver.
                 assert (h ∈ h :: t) as Hin_h; first set_solver.
                 eapply Hvalid_trans; try done.
              ** destruct Hlookup_j as [Hlookup_j|Hlookup_j].
                 --- assert (t = t1) as Heq_trans'; 
                       first (rewrite list_lookup_singleton_Some in Hlookup_i; set_solver).
                     rewrite /based_on in Hbased.
                     assert (t ∈ T) as Ht_in.
                     {
                       apply com_trans_imp2, Hbased.
                       split; last set_solver. 
                       apply elem_of_list_lookup; set_solver.
                     }
                     rewrite /valid_transactions in Hvalid_trans.
                     rewrite elem_of_list_lookup in Ht_in.
                     destruct Ht_in as (i' & Ht_in).
                     assert ((t :: T) !! (S i') = Some t) as Hlookup_succ.
                     { 
                       apply lookup_cons_Some; right.
                       split; first lia.
                       simpl.
                       by assert (i' = i' - 0) as <-; first lia.
                     }
                     assert ((t :: T) !! 0 = Some t) as Hlookup_zero; first set_solver.
                     assert (0 = S i') as Hfalse; last lia.
                     destruct t as [|h t]; first set_solver.
                     assert (h ∈ h :: t) as Hin_h; first set_solver.
                     eapply Hvalid_trans; try done.
                 --- rewrite list_lookup_singleton_Some in Hlookup_i.
                     rewrite list_lookup_singleton_Some in Hlookup_j.
                     lia.
    + exfalso.
      rewrite /valid_execution in Hexec.
      destruct Hexec as (_ & (Hfalse & _)).
      rewrite last_None in Heq; subst.
      set_solver.
Qed.

Lemma tags_sub : 
  ∀ e t, tags t ⊆ tags (t ++ [e]).
Proof.
  intros e t.
  induction t as [|h t IH]; simpl; set_solver.
Qed.

Lemma tags_in : 
  ∀ e t tag, e ∈ t → tagOfEvent e = Some tag → tag ∈ tags t.
Proof.
  intros e t tag Hin Htag.
  induction t as [|h t IH]; first set_solver.
  rewrite /tagOfEvent in Htag.
  destruct e; try inversion Htag.
  destruct e1; try inversion Htag.
  destruct l; try inversion Htag.
  subst.
  rewrite elem_of_cons in Hin.
  destruct Hin as [<- | Hin];  first set_solver.
  assert (tag ∈ tags t); set_solver.
Qed.

Lemma pre_post_false :
  ∀ e, is_pre_event e → ¬ is_post_event e.
Proof.
  intros e H Hfalse.
  destruct H as [[tag [c ->]] | [[tag [c ->]] | 
    [[tag [c ->]]| [[tag [c ->]] | [tag ->]]]]];
    destruct Hfalse as [Hfalse | [Hfalse | [Hfalse | [Hfalse | Hfalse]]]];
    rewrite /is_st_post_event /is_rd_post_event /is_wr_post_event
    /is_cm_post_event /is_in_post_event in Hfalse; set_solver.
Qed.

Lemma post_lin_lin_post le e :
  (is_st_post_event e ∨ is_rd_post_event e ∨ is_wr_post_event e ∨ 
   is_cm_post_event e ∨ is_in_post_event e) →
  (postToLin e = Some le → linToPost le = Some e).
Proof.
  intros Hevent Hpost_lin.
  destruct Hevent as [[tag [c ->]] | [[[tag [k [c [v ->]]]] | [tag [k [c ->]]]] | 
    [[tag [k [c [v ->]]]] | [[tag [c [b ->]]] | [tag [c ->]]]]]]; try set_solver.
Qed.

Lemma tag_pre_post e_pre e_post tag :
  tagOfEvent e_pre = Some tag →
  is_post_event e_post →
  postToPre e_post = Some e_pre →
  tagOfEvent e_post = Some tag.
Proof.
  intros Htag Hpost Hpost_pre.
  destruct Hpost as [[tag' [c' ->]] | [[[tag' [c' [k' [v' ->]]]]| [tag' [k' [c' ->]]]] 
    | [[tag' [c' [k' [v' ->]]]]|[[tag' [c' [b' ->]]]|[tag' [c' ->]]]]]].
  all : simpl in Hpost_pre.
  all : inversion Hpost_pre.
  all : by subst.
Qed.

Lemma tag_event_op op tag :
  tagOfOp op = tag →
  tagOfEvent (toLinEvent op) = Some tag.
Proof.
  intro Htag.
  destruct op as [(tag', c) k ov | (tag', c) k v | (tag', c) b]; 
    try set_solver.
  destruct ov as [v|]; set_solver.
Qed.

Lemma lin_to_post le tag e_post :
  is_lin_event le →
  tagOfEvent le = Some tag →
  linToPost le = Some e_post →
  (is_post_event e_post ∧ tagOfEvent e_post = Some tag).
Proof.
  intros Hlin Htag Hlin_post.
  rewrite /is_lin_event in Hlin.
  destruct Hlin as [[tag' [c' ->]] | [[[tag' [c' [k' [v' ->]]]]| [tag' [k' [c' ->]]]] 
    | [[tag' [c' [k' [v' ->]]]] | [[tag' [c' [b' ->]]] | [tag' [c' ->]]]]]].
  all : simpl in Hlin_post.
  all : inversion Hlin_post.
  all : subst.
  all : split; last done.
  all : rewrite /is_post_event /is_st_post_event 
          /is_in_post_event /is_rd_post_event 
          /is_wr_post_event /is_cm_post_event; eauto;
        set_solver.
Qed.

Lemma later_commit_imp1 c e_st lt e tag: 
  tagOfEvent e = Some tag →
  is_st_lin_event e →
  (¬∃ e', e' ∈ lt ∧ tagOfEvent e' = Some tag) →
  later_commit c e_st lt →
  later_commit c e_st (lt ++ [e]).
Proof.
  rewrite /later_commit.
  intros Htag His_st Hnot_in (e_cm & Hconn & Hevent & Hrel & Hnot).
  exists e_cm.
  split_and!; try done.
  - destruct Hrel as (i & j & Hlt & Hlookup_i & Hlookup_j).
    exists i, j.
    split; first done.
    split; apply lookup_app_Some; by left.
  - intros (e_st' & Hconn' & Hevent' & Hrel1 & Hrel2).
    apply Hnot.
    exists e_st'.
    do 2 (split; first done).
    destruct Hrel1 as (i & j & Hlt & Hlookup_i & Hlookup_j).
    rewrite lookup_snoc_Some in Hlookup_i.
    destruct Hlookup_i as [(Hlength_i & Hlookup_i) | (Hlength_i & Hlookup_i)].
    + rewrite lookup_snoc_Some in Hlookup_j.
      destruct Hlookup_j as [(Hlength_j & Hlookup_j) | (Hlength_j & Hlookup_j)].
      * split; first by exists i, j.
        destruct Hrel2 as (i' & j' & Hlt' & Hlookup_i' & Hlookup_j').
        rewrite lookup_snoc_Some in Hlookup_i'.
        destruct Hlookup_i' as [(Hlength_i' & Hlookup_i') | (Hlength_i' & Hlookup_i')].
        -- rewrite lookup_snoc_Some in Hlookup_j'.
           destruct Hlookup_j' as [(Hlength_j' & Hlookup_j') | (Hlength_j' & Hlookup_j')];
            first by exists i', j'.
          subst.
          rewrite /is_st_lin_event in His_st.
          rewrite /is_cm_lin_event in Hevent.
          set_solver.
        -- subst.
           rewrite lookup_snoc_Some in Hlookup_j'.
           destruct Hlookup_j' as [(Hlength_j' & Hlookup_j') | (Hlength_j' & Hlookup_j')].
           ++ assert (length lt ≤ j) as Hfalse; first lia.
              apply lookup_ge_None_2 in Hfalse.
              set_solver.
           ++ subst.
              destruct Hevent as (tag' & c' & b' & ->).
              rewrite /is_st_lin_event in Hevent'.
              set_solver.
      * subst.
        destruct Hrel2 as (i' & j' & Hlt' & Hlookup_i' & Hlookup_j').
        rewrite lookup_snoc_Some in Hlookup_i'.
        destruct Hlookup_i' as [(Hlength_i' & Hlookup_i') | (Hlength_i' & Hlookup_i')].
        -- exfalso.
           apply Hnot_in.
           exists e_st'.
           split; last done.
           apply elem_of_list_lookup.
           by exists i'.
        -- subst.
           assert (length (lt ++ [e_st']) ≤ j') as Hfalse.
           {
             rewrite last_length.
             lia.
           }
           apply lookup_ge_None_2 in Hfalse.
           set_solver.
    + subst.
      assert (length (lt ++ [e_st]) ≤ j) as Hfalse.
      {
        rewrite last_length.
        lia.
      }
      apply lookup_ge_None_2 in Hfalse.
      set_solver.
Qed.

Lemma no_later_start_or_commit_impl e e' c c' lt: 
  connOfEvent e = Some c →
  connOfEvent e' = Some c' →
  c ≠ c' →
  no_later_start_or_commit c e lt →
  no_later_start_or_commit c e (lt ++ [e']).
Proof.
  intros Heq1 Heq2 Hneq Hlater.
  intros (e'' & Hconn & Hrel & HOr).
  apply Hlater.
  exists e''.
  split; first done.
  split; last done.
  destruct Hrel as (i & j & Hlt & Hlookup_i & Hlookup_j).
  rewrite lookup_app_Some in Hlookup_i.
  destruct Hlookup_i as [Hlookup_i | (Hlength & Hlookup_i)].
  - rewrite lookup_app_Some in Hlookup_j.
    destruct Hlookup_j as [Hlookup_j | (Hlength & Hlookup_j)].
    + by exists i, j.
    + assert (e' = e'') as ->; last set_solver.
      rewrite list_lookup_singleton_Some in Hlookup_j.
      set_solver.
  - assert (e' = e) as ->; last set_solver.
    rewrite list_lookup_singleton_Some in Hlookup_i.
    set_solver.
Qed.

Lemma prior_init_imp1 c lt i e :
  prior_init i c lt →
  prior_init i c (lt ++ [e]).
Proof.
  intros (e' & j & Hin & Hconn & Hinit & Hleq).
  exists e', j.
  split_and!; try done.
  by apply lookup_app_l_Some.
Qed.

Lemma prior_init_imp2 e e' lt c c' i :
  (∃ e, e ∈ lt ∧ connOfEvent e = Some c ∧ is_in_lin_event e) →
  connOfEvent e' = Some c' →
  connOfEvent e = Some c →
  valid_sequence lt →
  (lt ++ [e]) !! i = Some e' →
  prior_init i c' (lt ++ [e]).
Proof.
  intros (e_init & Hin & Hconn'' & Hinit) Hconn Hconn' (Hvalid & _) Hlookup_i.
  rewrite lookup_app_Some in Hlookup_i.
  destruct Hlookup_i as [Hlookup_i | (Hlength & Hlookup_i)].
  - apply prior_init_imp1. 
    by eapply Hvalid.
  - apply elem_of_list_lookup in Hin as (j & Hlookup_j).
    exists e_init, j.
    apply list_lookup_singleton_Some in Hlookup_i.
    assert (e = e') as ->; first set_solver.
    assert (c = c') as ->; first set_solver.
    split_and!; try set_solver.
    + apply lookup_app_Some.
      eauto.
    + apply lookup_lt_Some in Hlookup_j.
      lia.
Qed.

Lemma unique_init_events_imp lt e : 
  (¬is_in_lin_event e) →
  unique_init_events lt →
  unique_init_events (lt ++ [e]).
Proof.
  intros Hnot Hunique.
  intros e1 e2 c i j Hlookup_i Hevent Hconn Hlookup_j Hevent' Hconn'.
  rewrite lookup_snoc_Some in Hlookup_i.
  destruct Hlookup_i as [(_ & Hlookup_i)|(_ & ->)]; last done.
  rewrite lookup_snoc_Some in Hlookup_j.
  destruct Hlookup_j as [(_ & Hlookup_j)|(_ & ->)]; last done.  
  by eapply Hunique.
Qed.

Definition open_start (c : val) (ltrace tail : list val) : Prop := 
  ∃ le l, ltrace = l ++ [le] ++ tail ∧
    commit_closed c l ∧
    (∃ (tag : string), le = (#tag, (c, #"StLin"))%V) ∧
    (∀ le', le' ∈ tail → connOfEvent le' = Some c → 
            (is_wr_lin_event le' ∨ is_rd_lin_event le')).

Lemma prior_start_imp le c e lt tag :
  tagOfEvent le = Some tag →
  ¬(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag) →
  prior_start c e lt →
  prior_start c e (lt ++ [le]).
Proof.
  intros Htag Hnot (e_st & Hconn & Hstart & Hrel & Hnot').
  exists e_st.
  do 2 (split; first done).
  split; first by apply rel_list_imp.
  intros (e_cm & Hconn' & Hcom & Hrel1 & Hrel2).
  apply Hnot'.
  exists e_cm.
  do 2 (split; first done).
  split.
  - apply rel_list_last_neq in Hrel1; first done.
    intros ->.
    assert (e_cm ∈ lt) as He_cm_in; last set_solver.
    by eapply rel_list_in.
  - subst.
    apply rel_list_last_neq in Hrel2; first done.
    intros ->.
    destruct Hrel as (i & j & _ & _ & Hlookup_j).
    apply Hnot.
    exists e.
    split; last done.
    apply elem_of_list_lookup.
    by exists j.
Qed.

Lemma later_commit_imp2 c lt le le' :
  (is_wr_lin_event le ∨ is_rd_lin_event le ∨ is_in_lin_event le) →
  later_commit c le' lt →
  later_commit c le' (lt ++ [le]).
Proof.
  intros Hdisj (e_cm & Hconn & Hevent & Hrel & Hnot).
  exists e_cm.
  split_and!; try done.
  - by apply rel_list_imp.
  - intros (e_st & Hconn' & Hevent' & Hrel1 & Hrel2).
    apply Hnot.
    exists e_st.
    do 2 (split; first done).
    split.
    all : apply (rel_list_last_neq _ _ _ le); last done.
    all : intros ->.
    all : rewrite /is_wr_lin_event /is_rd_lin_event 
            /is_in_lin_event in Hdisj.
    all : rewrite /is_cm_lin_event in Hevent.
    all : rewrite /is_st_lin_event in Hevent'.
    all : set_solver.
Qed.

Lemma no_later_start_or_commit_wr_rd_imp le c e lt : 
  (is_wr_lin_event le ∨ is_rd_lin_event le ∨ is_in_lin_event le) →
  no_later_start_or_commit c e lt →
  no_later_start_or_commit c e (lt ++ [le]).
Proof.
  intros Hdisj Hlater.
  intros (e' & Hconn & Hrel & Hevent).
  apply Hlater.
  exists e'.
  split_and!; try done.
  apply (rel_list_last_neq _ _ _ le); last done.
  intros ->.
  rewrite /is_wr_lin_event /is_rd_lin_event /is_in_lin_event in Hdisj.
  rewrite /is_cm_lin_event /is_st_lin_event in Hevent.
  set_solver.
Qed.

Lemma later_commit_imp3 c lt le le' tag :
  tagOfEvent le = Some tag →
  ¬(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag) →
  is_cm_lin_event le →
  later_commit c le' lt →
  later_commit c le' (lt ++ [le]).
Proof.
  intros Htag Hnot_in Hevent (le_cm & Hcm_conn & Hcm_event & Hcm_rel & Hcm_imp).
  exists le_cm.
  split_and!; try done; first by apply rel_list_imp.
  intros (e_st & He_st_conn & He_st_event & He_st_rel1 & He_st_rel2).
  apply Hcm_imp.
  exists e_st.
  split_and!; try done.
  - eapply rel_list_last_neq; try done.
    rewrite /is_st_lin_event in He_st_event.
    rewrite /is_cm_lin_event in Hevent.
    set_solver.
  - eapply rel_list_last_neq; try done.
    intros ->.
    apply Hnot_in.
    exists le_cm; split; last done.
    destruct Hcm_rel as (i & j & _ & _ & Hlookup_j).
    by eapply elem_of_list_lookup_2.
Qed.

Lemma later_commit_imp4 c lt le le' tag :
  tagOfEvent le = Some tag →
  ¬(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag) →
  is_cm_lin_event le →
  connOfEvent le = Some c →
  connOfEvent le' = Some c →
  no_later_start_or_commit c le' lt →
  le' ∈ lt →
  later_commit c le' (lt ++ [le]).
Proof.
  intros Htag Hnot_in Hevent Hconn1 Hconn2 Hin Hlater.
  exists le.
  rewrite /no_later_start_or_commit in Hlater.
  split_and!; try done.
  - apply elem_of_list_lookup_1 in Hlater. 
    destruct Hlater as (i & Hlookup_i).
    exists i, (length lt).
    split_and!. 
    + by eapply lookup_lt_Some.
    + by eapply lookup_app_l_Some.
    + apply lookup_snoc_Some. 
      set_solver.
  - intros (e_st & He_st_conn & He_st_event & He_st_rel1 & He_st_rel2).
    assert (rel_list lt le' e_st) as He_st_rel3.
    {
      eapply rel_list_last_neq; try done.
      intros ->.
      rewrite /is_st_lin_event in He_st_event.
      rewrite /is_cm_lin_event in Hevent.
      set_solver.
    }
    apply Hin.
    set_solver.
Qed.

Lemma commit_closed_valid_seq lt le c tag :
  tagOfEvent le = Some tag →
  ¬(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag) →
  valid_sequence lt →
  is_cm_lin_event le →
  connOfEvent le = Some c →
  commit_closed c (lt ++ [le]).
Proof.
  intros Htag Hnot_in Hvalid Hcm Hconn e_st Hst_in Hst_conn Hst_event.
  rewrite elem_of_app in Hst_in.
  destruct Hst_in as [Hst_in | Hfalse].
  - destruct Hvalid as (_ & _ & _ & Hvalid & _).
    specialize (Hvalid e_st c Hst_in Hst_conn Hst_event).
    destruct Hvalid as [Hlater_com|Hno_later].
    + by eapply later_commit_imp3.
    + by eapply later_commit_imp4. 
  - rewrite /is_st_lin_event in Hst_event.
    rewrite /is_cm_lin_event in Hcm.
    set_solver.
Qed.

Lemma lin_trace_valid : 
  ∀ (tag : string) (e : val) (t lt : list val), 
    ((is_pre_event e ∧ tagOfEvent e = Some tag ∧ tag ∉ tags t) ∨
     (is_post_event e ∧ (∃ le, postToLin e = Some le ∧ le ∈ lt))) → 
    lin_trace_of lt t → lin_trace_of lt (t ++ [e]).
Proof.
  intros tag e t lt His_pre_post Hlin_trace.
  rewrite /lin_trace_of.
  destruct Hlin_trace as (?&?&?&?&?).
  split; first done.
  split.
  - intros e_post Hin le Hpost_lin.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin | Hin].
    {
      apply (H0 e_post); done.
    } 
    assert (e_post = e) as ->; first set_solver.
    destruct His_pre_post as [(His_pre & _ & _) | His_post].
    + exfalso.
      destruct His_pre as [[tag' [c' ->]]| His_pre].
      1 : simpl in Hpost_lin; destruct tag'; done.
      destruct His_pre as [[tag' [c' ->]]| His_pre].
      1 : simpl in Hpost_lin; destruct tag'; done.
      destruct His_pre as [[tag' [c' ->]]| His_pre].
      1 : by simpl in Hpost_lin.
      destruct His_pre as [[tag' [c' ->]]| [tag' ->]].
      all : simpl in Hpost_lin; destruct tag'; done.
    + destruct His_post as (le' & Hpost_lin' & Hin').
      set_solver.
  - split.
    + intros le Hin.
      destruct (H1 le Hin) as [e_pre (Hpre & HlinPre & Hin' & Himp)].
      exists e_pre.
      do 2 (split; first done).
      split; first set_solver.
      intros e_post Hassump.
      destruct His_pre_post as [(His_pre & _ & _) | His_post].
      * apply Himp.
        destruct Hassump as (Hassump1 & Hassump2).
        split; last done.
        rewrite elem_of_app in Hassump1.
        destruct Hassump1 as [Hassump1 | Hassump1]; first done.
        assert (e_post = e) as ->; first set_solver.
        exfalso.
        apply pre_post_false in His_pre.
        destruct Hassump2 as (His_post & _).
        by apply His_pre.
      * destruct Hassump as (Hassump1 & (Hassump2 & Hassump2')).
        rewrite elem_of_app in Hassump1.
        destruct Hassump1 as [Hassump1 | Hassump1]; first by apply Himp.
        assert (e_post = e) as ->; first set_solver.
        destruct His_post as (His_post & (le' & Hlin_post & Hin_le')).
        pose proof Hin as Hin_le.
        rewrite elem_of_list_lookup in Hin.
        destruct Hin as (i & Hlookup_i).
        rewrite elem_of_list_lookup in Hin_le'.
        destruct Hin_le' as (j & Hlookup_j).
        rewrite /is_post_event in His_post.
        destruct His_post as [[tag' [c' ->]]| [ [[tag' [k' [c' [v' ->]]]] | 
          [tag' [k' [c' ->]]]]| [[tag' [c' [k' [v' ->]]]] |
          [[tag' [k' [c' ->]]] | [tag' [c' ->]]]]]];
          pose proof Hlin_post as Hlin_post';
          apply post_lin_lin_post in Hlin_post; eauto.
        -- assert (tagOfEvent le' = Some tag') as Htag_of1; first set_solver.
           assert (tagOfEvent le = Some tag') as Htag_of2.
           {
             destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
               [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | 
               [[tag'' [c'' [b'' ->]]] | [tag'' [c'' ->]]]]]];
             set_solver.
           }
           assert (le = le') as ->; last done.
           assert (i = j) as ->; last set_solver.
           apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
        -- assert (tagOfEvent le' = Some tag') as Htag_of1; first set_solver.
           assert (tagOfEvent le = Some tag') as Htag_of2.
           {
             destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
               [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | 
               [[tag'' [c'' [b'' ->]]] | [tag'' [c'' ->]]]]]];
             set_solver.
           }
           assert (le = le') as ->; last done.
           assert (i = j) as ->; last set_solver.
           apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
        -- assert (tagOfEvent le' = Some tag') as Htag_of1; first set_solver.
           assert (tagOfEvent le = Some tag') as Htag_of2.
           {
             destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
               [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | 
               [[tag'' [c'' [b'' ->]]] | [tag'' [c'' ->]]]]]];
             set_solver.
           }
           assert (le = le') as ->; last done.
           assert (i = j) as ->; last set_solver.
           apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
        -- assert (tagOfEvent le' = Some tag') as Htag_of1; first set_solver.
           assert (tagOfEvent le = Some tag') as Htag_of2.
           {
             destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
               [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | 
               [[tag'' [c'' [b'' ->]]] | [tag'' [c'' ->]]]]]];
             set_solver.
           }
           assert (le = le') as ->; last done.
           assert (i = j) as ->; last set_solver.
           apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
        -- assert (tagOfEvent le' = Some tag') as Htag_of1; first set_solver.
           assert (tagOfEvent le = Some tag') as Htag_of2.
           {
             destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
               [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | 
               [[tag'' [c'' [b'' ->]]] | [tag'' [c'' ->]]]]]];
             set_solver.
           }
           assert (le = le') as ->; last done.
           assert (i = j) as ->; last set_solver.
           apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
        -- assert (tagOfEvent le' = Some tag') as Htag_of1; first set_solver.
           assert (tagOfEvent le = Some tag') as Htag_of2.
           {
             destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
               [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | 
               [[tag'' [c'' [b'' ->]]] | [tag'' [c'' ->]]]]]];
             set_solver.
           }
           assert (le = le') as ->; last done.
           assert (i = j) as ->; last set_solver.
           apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
    + split; last done. 
      intros le1 le2 Hrel Hfalse.
      destruct Hfalse as [e1_pre [e2_post (Hlinpre & Hlinpost & Hrel_e)]].
      pose proof Hrel as Hrel'.
      apply (H2 le1 le2) in Hrel'.
      apply Hrel'.
      assert (is_lin_event le1 ∧ is_lin_event le2) as (Hle1_lin & Hle2_lin).
      {
        destruct Hrel as [i [j (Hle & Hlookup_i & Hlookup_j)]].
        apply elem_of_list_lookup_2 in Hlookup_i, Hlookup_j.
        by apply H in Hlookup_i, Hlookup_j.
      }
      exists e1_pre, e2_post.
      do 2 (split; first done).
      destruct Hrel_e as [i [j (Hle & Hlookup_post & Hlookup_pre)]].
      rewrite lookup_snoc_Some in Hlookup_post.
      destruct Hlookup_post as [(Hle_length & Hlookup_post)|(Heq_lenght & Hlookup_post)].
      * pose proof Hlookup_pre as Hlookup_pre'.
        rewrite lookup_snoc_Some in Hlookup_pre.
        destruct Hlookup_pre as [(Hle_length' & Hlookup_pre)|(Heq_lenght' & Hlookup_pre)].
        -- by exists i, j.
        -- subst. 
           destruct His_pre_post as [(_ & Htag & Htags) | Hfalse].
           ++ exfalso.
              rewrite /rel_list in Hrel.
              destruct Hrel as [i' [j' (Hle' & Hlookup_le1 & Hlookup_le2)]].
              assert (le1 ∈ lt) as Hin_le1; first by eapply elem_of_list_lookup_2.
              destruct (H1 le1 Hin_le1) as [e1_pre' (His_pre' & Hlinpre' & Hin_pre' & _)].
              assert (e1_pre = e1_pre'); first set_solver.
              subst.
              assert (tag ∈ tags t) as Hfalse; last set_solver.
              eapply tags_in; done.
           ++ exfalso.
              destruct Hle1_lin as [[tag' [c' ->]] | [[[tag' [c' [k' [v' ->]]]]|[tag' [c' [k' ->]]]] | 
                [[tag' [c' [k' [v' ->]]]]|[[tag' [c' [b' ->]]]|[tag' [c' ->]]]]]]; 
                simpl in Hlinpre;
                destruct Hfalse as ([Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]] & _);
                inversion Hfalse; set_solver.
      * subst.
        exfalso.
        assert (e1_pre = e2_post) as ->.
        {
          rewrite lookup_snoc_Some in Hlookup_pre.
          destruct Hlookup_pre as [(Hfalse & _ ) | (_ & Hgoal)]; last done.
          lia.
        }
        destruct Hle2_lin as [[tag' [c' ->]] | [[[tag' [c' [k' [v' ->]]]]|[tag' [c' [k' ->]]]] | 
          [[tag' [c' [k' [v' ->]]]]|[[tag' [c' [b' ->]]]|[tag' [c' ->]]]]]];
          simpl in Hlinpost;
          inversion Hlinpost; subst;
          destruct Hle1_lin as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]]|[tag'' [c'' [k'' ->]]]] | 
            [[tag'' [c'' [k'' [v'' ->]]]]|[[tag'' [c'' [b'' ->]]]|[tag'' [c'' ->]]]]]]; by simpl in Hlinpre.
Qed.

Lemma lin_trace_lin lt e_pre e_lin (tag : string) c t :
  e_pre ∈ t →
  is_pre_event e_pre →
  is_lin_event e_lin →
  linToPre e_lin = Some e_pre → 
  connOfEvent e_lin = Some c →
  tagOfEvent e_lin = Some tag →
  tagOfEvent e_pre = Some tag →
  (¬∃ e, e ∈ lt ∧ tagOfEvent e = Some tag) →
  (¬∃ e, e ∈ t ∧ is_post_event e ∧ tagOfEvent e = Some tag) →
  lin_trace_of lt t →
  lin_trace_of (lt ++ [e_lin]) t.
Proof.
  intros Hpre_in His_pre His_lin Hlin_to_pre Hconn Htag Htag' Hnot1 Hnot2 H.
  destruct H as (?&?&?&?&?).
  split.
  {
    intros le Hin.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin | Hin].
    - by apply H.
    - assert (le = e_lin) as <-; set_solver.
  }
  split.
  {
    intros e_post Hin le Hpost_lin.
    rewrite elem_of_app.
    left.
    apply (H0 e_post Hin le Hpost_lin).
  }
  split.
  {
    intros le Hin.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin | Hin].
    - apply (H1 le Hin).
    - exists e_pre.
      assert (le = e_lin) as <-; first set_solver.
      do 3 (split; first done).
      intros e_post (Hpost_in & His_post & Hfalse).
      exfalso.
      apply Hnot2.
      exists e_post.
      do 2 (split; first done).
      by apply (tag_pre_post e_pre e_post).
  }
  split.
  { 
    intros le1 le2 Hrel.
    destruct Hrel as [i [j (Hlt & Hlookup_i & Hlookup_j)]].
    rewrite lookup_snoc_Some in Hlookup_i.
    destruct Hlookup_i as [(Hlength & Hlookup_i) | (Hlength & Hlookup_i)].
    - rewrite lookup_snoc_Some in Hlookup_j.
      destruct Hlookup_j as [(Hlength' & Hlookup_j) | (Hlength' & Hlookup_j)]. 
      + apply H2.
        by exists i, j.
      + intros (e1_pre & e2_post & (_ & Hlin_post & Hrel)).
        apply Hnot2.
        exists e2_post.
        subst.
        simpl in Hlin_post.
        split.
        * destruct Hrel as [i' [_ (_ & Hlookup_i' & _)]].
          apply elem_of_list_lookup.
          by exists i'.
        * by apply (lin_to_post le2); done.
    - rewrite lookup_snoc_Some in Hlookup_j.
      destruct Hlookup_j as [(Hlength' & Hlookup_j) | (Hlength' & Hlookup_j)]; lia.
  }
  intros le1 le2 i j tag' Hlookup_i Hlookup_j Htag_le1 Htag_le2.
  rewrite lookup_app_Some in Hlookup_i.
  rewrite lookup_app_Some in Hlookup_j.
  destruct Hlookup_i as [Hlookup_i | (Hlength_i & Hlookup_i)].
  - destruct Hlookup_j as [Hlookup_j | (Hlength_j & Hlookup_j)].
    + apply (H3 le1 le2 i j tag' Hlookup_i Hlookup_j Htag_le1 Htag_le2).
    + exfalso.
      apply Hnot1. 
      exists le1.
      split.
      * apply elem_of_list_lookup.
        by exists i.
      * apply list_lookup_singleton_Some in Hlookup_j.
        destruct Hlookup_j as (_ & <-).
        simpl in Htag_le2.
        set_solver.
  - destruct Hlookup_j as [Hlookup_j | (Hlength_j & Hlookup_j)].
    + exfalso.
      apply Hnot1. 
      exists le2.
      split.
      * apply elem_of_list_lookup.
        by exists j.
      * apply list_lookup_singleton_Some in Hlookup_i.
        destruct Hlookup_i as (_ & <-).
        simpl in Htag_le1.
        set_solver.
    + rewrite list_lookup_singleton_Some in Hlookup_i.
      rewrite list_lookup_singleton_Some in Hlookup_j.
      lia.
Qed.

Lemma valid_sequence_st_lin lt tag c : 
  (∃ e, e ∈ lt ∧ connOfEvent e = Some c ∧ is_in_lin_event e) →
  (¬∃ e, e ∈ lt ∧ tagOfEvent e = Some tag) →
  commit_closed c lt →
  valid_sequence lt → 
  valid_sequence (lt ++ [(#tag, (c, #"StLin"))%V]).
Proof.
  intros Hinit Hnot Hstart Hvalid_seq.
  split_and!.
  - intros e c' i Hlookup_i Hconn.
    eapply (prior_init_imp2 (#tag, (c, #"StLin"))%V e) ; try done.
  - destruct Hvalid_seq as (_ & Hvalid_seq & _).
    apply unique_init_events_imp; last done. 
    rewrite /is_in_lin_event; set_solver.
  - intros e c_e He_in He_conn He_event.
    rewrite elem_of_app in He_in.
    destruct He_in as [He_in | He_in].
    + destruct Hvalid_seq as (_ & _ & Hvalid_seq & _).
      destruct (Hvalid_seq e c_e He_in He_conn He_event) as 
        (e_st & He_st_conn & He_st_lin & He_st_rel & He_st_not ).
      exists e_st.
      do 2 (split; first done).
      split.
      * destruct He_st_rel as (i & j & Hneq & Hlookup_i & Hlookup_j).
        exists i, j.
        split; first done.
        split; by apply lookup_app_l_Some.
      * intros Hfalse.
        destruct Hfalse as (e_cm & Hcm_conn & Hcm_lin & Hcm_rel1 & Hcm_rel2).
        apply He_st_not.
        exists e_cm.
        do 2 (split; first done).
        split.
        -- destruct Hcm_rel1 as (i & j & Hle & Hlookup_i & Hlookup_j).
            exists i, j.
            split; first done.
            rewrite lookup_app_Some in Hlookup_i.
            destruct Hlookup_i as [Hlookup_i | (Hlength & Hlookup_i)].
            ++ split; first done.
              rewrite lookup_app_Some in Hlookup_j.
              destruct Hlookup_j as [Hlookup_j | (Hlength & Hlookup_j)]; first done.
              rewrite list_lookup_singleton_Some in Hlookup_j.
              destruct Hlookup_j as (_ & <-).
              rewrite /is_cm_lin_event in Hcm_lin.
              set_solver.
            ++ assert (length (lt ++ [(#tag, (c, #"StLin"))%V]) ≤ j) as Hfalse.
              {
                rewrite last_length.
                lia.
              }
              apply lookup_ge_None_2 in Hfalse.
              set_solver.
        -- destruct Hcm_rel2 as (i & j & Hle & Hlookup_i & Hlookup_j).
            exists i, j.
            split; first done.
            rewrite lookup_app_Some in Hlookup_i.
            destruct Hlookup_i as [Hlookup_i | (Hlength & Hlookup_i)].
            ++ split; first done.
              rewrite lookup_app_Some in Hlookup_j.
              destruct Hlookup_j as [Hlookup_j | (Hlength & Hlookup_j)]; first done.
              rewrite list_lookup_singleton_Some in Hlookup_j.
              destruct Hlookup_j as (_ & <-).
              destruct He_event as [Hfalse | [Hfalse | Hfalse]].
              ** rewrite /is_rd_lin_event in Hfalse.
                  set_solver.
              ** rewrite /is_wr_lin_event in Hfalse.
                  set_solver.
              ** rewrite /is_cm_lin_event in Hfalse.
                  set_solver.
            ++ assert (length (lt ++ [(#tag, (c, #"StLin"))%V]) ≤ j) as Hfalse.
              {
                rewrite last_length.
                lia.
              }
              apply lookup_ge_None_2 in Hfalse.
              set_solver. 
    + assert (e = (#tag, (c, #"StLin"))%V) as ->; first set_solver.
      destruct He_event as [[Hfalse | Hfalse] | [Hfalse | Hfalse]];
        rewrite /is_wr_lin_event /is_cm_lin_event in Hfalse;
        set_solver.
  - intros e_st c0 He_in He_conn He_event.
    rewrite elem_of_app in He_in.
    destruct He_in as [He_in | He_in].
    + destruct (decide (c = c0)) as [<-|Hneq].
      * left.
        apply (later_commit_imp1 _ _ _ _ tag); try done.
        -- by exists tag, c.
        -- by apply Hstart.
      * destruct Hvalid_seq as (_ & _ & _ & Hvalid_seq & _).
        specialize (Hvalid_seq e_st c0 He_in He_conn He_event).
        destruct Hvalid_seq as [Hvalid_seq | Hvalid_seq].
        -- left.
            apply (later_commit_imp1 _ _ _ _ tag); try done.
            by exists tag, c.
        -- right.
           eapply no_later_start_or_commit_impl; try done.
    + assert (e_st = (#tag, (c, #"StLin"))%V) as ->; first set_solver.
      right.
      intro Hfalse.
      destruct Hfalse as (e & _ & (i & j & Hneq & Hlookup_i & Hlookup_j) & _).
      rewrite lookup_app_Some in Hlookup_i.
      destruct Hlookup_i as [Hfalse |(Hlength & Hlookup_i)].
      * apply Hnot. 
        exists (#tag, (c, #"StLin"))%V.
        split; last by simpl.
        apply elem_of_list_lookup.
        by exists i.
      * rewrite lookup_app_Some in Hlookup_j.
        destruct Hlookup_j as [Hfalse |(_ & Hfalse)].
        -- rewrite list_lookup_singleton_Some in Hlookup_i.
            destruct Hlookup_i as (Hlookup_i & _ ).
            assert (i = length lt) as ->; first lia.
            assert (length lt ≤ j) as Hleq; first lia.
            apply lookup_ge_None_2 in Hleq.
            set_solver.
        -- rewrite list_lookup_singleton_Some in Hlookup_i. 
            destruct Hlookup_i as (Hlookup_i & _ ).
            rewrite list_lookup_singleton_Some in Hfalse. 
            destruct Hfalse as (Hfalse & _ ).
            lia.
  - intros i tag' c' k v Hlookup_i.
    destruct Hvalid_seq as (_ & _ & _ & _ & Hvalid_seq).
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i |(_ & Hfalse)].
    + destruct (Hvalid_seq _ _ _ _ _ Hlookup_i) as (j & tag_j & c_j & Hlt & Hlookup_j).
      eexists j, tag_j, c_j.
      split; first done.
      rewrite lookup_app_Some.
      by left. 
    + rewrite list_lookup_singleton_Some in Hfalse.
      set_solver.
Qed.

Lemma valid_sequence_wr_rd_cm_lin le lt (tag : string) c tail :
  (∃ e, e ∈ lt ∧ connOfEvent e = Some c ∧ is_in_lin_event e) →
  (¬∃ e, e ∈ lt ∧ tagOfEvent e = Some tag) →
  open_start c lt tail →
  (is_cm_lin_event le ∨ is_wr_lin_event le ∨ is_rd_lin_event le) →
  tagOfEvent le = Some tag →
  connOfEvent le = Some c →
  (∃ t, lin_trace_of lt t) →
  (∀ tag1 c1 k v, le = (#tag1, (c1, (#"RdLin", (#k, InjRV v))))%V → 
    ∃ (tag2 : string) c2, (#tag2, (c2, (#"WrLin", (#k, v))))%V ∈ lt) →
  valid_sequence lt → 
  valid_sequence (lt ++ [le]).
Proof.
  intros Hinit Hnot Hopen_start Hevent Htag_of Hconn_of Hlin Hread Hvalid.
  split_and!.
  - intros e c' i Hlookup_i Hconn.
    eapply (prior_init_imp2 le e); try done.
  - destruct Hvalid as (_ & Hvalid & _). 
    apply unique_init_events_imp; last done. 
    rewrite /is_in_lin_event.
    rewrite /is_wr_lin_event /is_rd_lin_event /is_cm_lin_event in Hevent; set_solver.
  - intros e c' Hin Hconn Hevents.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin].
    + destruct Hvalid as (_ & _ & Hvalid & _).
      specialize (Hvalid e c' Hin Hconn Hevents).
      apply (prior_start_imp le c' e lt tag); try done.
    + assert (e = le) as ->; first set_solver.
      destruct Hopen_start as (e_st & l & -> & _ & (tag' & ->) & Hnot').
      exists (#tag', (c, #"StLin"))%V.
      simpl.
      split_and!; first set_solver.
      * by exists tag', c.
      * exists (length l), (length (l ++ (#tag', (c, #"StLin"))%V :: tail)).
        split_and!.
        -- rewrite app_length.
           rewrite cons_length.
           lia.
        -- apply lookup_app_l_Some.
           by apply list_lookup_middle.
        -- assert (Init.Nat.pred (length ((l ++ (#tag', (c, #"StLin"))%V :: tail) ++ [le])) =
             length (l ++ (#tag', (c, #"StLin"))%V :: tail)) as <-. 
           {
            rewrite last_length.
            lia.
           } 
          rewrite -last_lookup.
          by rewrite last_snoc.
      * intros (e_cm & Hconn' & Hevent_cm & Hrel1 & Hrel2).
        assert (c = c') as ->; first set_solver.
        assert (rel_list (l ++ (#tag', (c', #"StLin"))%V :: tail)
          (#tag', (c', #"StLin"))%V e_cm) as Hrel3.
        {
          apply (rel_list_last_neq _ _ _ le); last done.
          intros ->.
          assert (e_cm ∈ (l ++ [(#tag', (c', #"StLin"))%V] ++ tail)) 
            as He_cm_in; last set_solver.
          by eapply rel_list_in.
        }
        destruct Hrel3 as (i & j & Hlt & Hlookup_i & Hlookup_j).
        rewrite lookup_app_Some in Hlookup_j.
        destruct Hlookup_j as [Hlookup_j | (Hlength_j & Hlookup_j)].
        -- rewrite lookup_app_Some in Hlookup_i.
           destruct Hlookup_i as [Hlookup_i | (Hlength_i & Hlookup_i)].
           ++ destruct Hlin as (t & _ & _ & _ & _ & Hlin). 
              specialize (Hlin (#tag', (c', #"StLin"))%V (#tag', (c', #"StLin"))%V 
                i (length l) tag').
              assert (i = length l) as ->.
              ** apply Hlin; try done.
                 --- by apply lookup_app_l_Some.
                 --- rewrite app_assoc. 
                     apply lookup_app_l_Some.
                     assert (Init.Nat.pred (length (l ++ [(#tag', (c', #"StLin"))%V])) = 
                      length l) as <-. 
                      {
                        rewrite last_length.
                        lia.
                      } 
                      rewrite -last_lookup.
                      by rewrite last_snoc.
              ** assert (length l ≤ length l) as Hleq; first lia.
                 apply lookup_ge_None_2 in Hleq.
                 set_solver.
           ++ assert (length l ≤ j) as Hfalse; first lia.
              apply lookup_ge_None_2 in Hfalse.
              set_solver.
        -- rewrite lookup_cons_Some in Hlookup_j.
           rewrite /is_cm_lin_event in Hevent_cm.
           destruct Hlookup_j as [(_ & <-)|(_ & Hlookup_j)]; first set_solver.
           assert (e_cm ∈ tail) as Hfalse.
           {
             apply elem_of_list_lookup.
             by eexists _.
           }
           specialize (Hnot' e_cm Hfalse Hconn').
           rewrite /is_wr_lin_event /is_rd_lin_event /is_cm_lin_event in Hnot'.
           set_solver.
  - intros e_st c' Hin Hconn Hstart.
    rewrite elem_of_app in Hin.
    destruct Hvalid as (_ & _ & _ & Hvalid & _).
    destruct Hin as [Hin|Hin].
    + destruct (Hvalid e_st c' Hin Hconn Hstart) as [Hlater | Hno_later].
      * left.
        destruct Hevent as [Hevent|Hevent].
        -- by eapply later_commit_imp3.
        -- apply later_commit_imp2; set_solver.
      * destruct (decide (c = c')) as [->|Hneq].
        -- destruct Hevent as [Hevent|Hevent].
           ++ left. 
              eapply later_commit_imp4; try done.
           ++ right.
              apply no_later_start_or_commit_wr_rd_imp; try done.
              set_solver.
        -- right.
           by eapply no_later_start_or_commit_impl.
    + assert (e_st = le) as ->; first set_solver.
      destruct Hstart as (tag'' & c'' & ->). 
      destruct Hevent as [Hevent|Hevent];
        rewrite /is_wr_lin_event /is_rd_lin_event /is_cm_lin_event in Hevent;
        set_solver.
  - intros i tag' c' k v Hlookup_i.
    destruct Hvalid as (_ & _ & _ & _ & Hvalid_seq).
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i |(Hlength_i & Hlookup_i)].
    + destruct (Hvalid_seq _ _ _ _ _ Hlookup_i) as (j & tag_j & c_j & Hlt & Hlookup_j).
      eexists j, tag_j, c_j.
      split; first done.
      rewrite lookup_app_Some.
      by left. 
    + rewrite list_lookup_singleton_Some in Hlookup_i.
      destruct Hlookup_i as (Hlength & Heq).
      destruct (Hread  _ _ _ _ Heq) as (tag2 & c2 & Hin).
      destruct (elem_of_list_lookup_total_1 _ _ Hin) as (j & Hlt & Hlookup_j).
      exists j, tag2, c2.
      split; first lia.
      apply lookup_app_l_Some.
      by apply list_lookup_alt.
Qed.

Lemma valid_sequence_in_lin lt tag c : 
  (¬∃ e, e ∈ lt ∧ tagOfEvent e = Some tag) →
  unique_init_events (lt ++ [(#tag, (c, #"InLin"))%V]) →
  valid_sequence lt → 
  valid_sequence (lt ++ [(#tag, (c, #"InLin"))%V]).
Proof.
  intros Hnot Hunique (Hvalid1 & Hvalid2 & Hvalid3 & Hvalid4 & Hvalid5).
  split_and!; try done.
  - intros e c' i Hlookup_i Hconn.
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i|(Hlength_i & Hlookup_i)].
    + apply prior_init_imp1.
      set_solver.
    + rewrite list_lookup_singleton_Some in Hlookup_i.
      destruct Hlookup_i as (Hlength & <-).
      exists (#tag, (c, #"InLin"))%V, (length lt); split_and!; try done.
      * assert (Init.Nat.pred (length (lt ++ [(#tag, (c, #"InLin"))%V])) =
          length lt) as <-. 
           {
            rewrite last_length.
            lia.
           } 
          rewrite -last_lookup.
          by rewrite last_snoc.
      * rewrite /is_in_lin_event; set_solver.
  - intros e c' Hin Hconn Hevent.
    apply (prior_start_imp _ _ _ _ tag); try done.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; first set_solver.
    rewrite /is_rd_lin_event /is_wr_lin_event /is_cm_lin_event in Hevent.
    set_solver.
  - intros e_st c' Hin Hconn Hevent.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; 
      rewrite /is_st_lin_event in Hevent; last set_solver.
    destruct (Hvalid4 e_st c' Hin Hconn Hevent) as [Hlater | Hno_later].
    + left.
      apply later_commit_imp2; try done.
      rewrite /is_in_lin_event; set_solver.
    + right.
      destruct (decide (c = c')) as [<-|Hneq].
      * apply no_later_start_or_commit_wr_rd_imp; try done.
        rewrite /is_in_lin_event; set_solver.
      * by eapply no_later_start_or_commit_impl.
  - intros i tag' c' k v Hlookup_i.
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i |(_ & Hfalse)].
    + destruct (Hvalid5 _ _ _ _ _ Hlookup_i) as (j & tag_j & c_j & Hlt & Hlookup_j).
      eexists j, tag_j, c_j.
      split; first done.
      rewrite lookup_app_Some.
      by left. 
    + rewrite list_lookup_singleton_Some in Hfalse.
      set_solver.
Qed.

Lemma extraction_of_add1 lt T le op : 
  toLinEvent op = le →
  linToOp le = Some op →
  extraction_of lt T →
  extraction_of (lt ++ [le]) (T ++ [[op]]).
Proof.
  intros Hevent Hlin (Hextract1 & Hextract2 & Hextract3).
  split_and!.
  - intros le' op' Hin Heq. 
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; first set_solver.
    exists [op].
    assert (le = le') as ->; first set_solver.
    assert (op = op') as ->; set_solver.
  - intros t op' Hin Hin'.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin].
    + assert (toLinEvent op' ∈ lt) as Hin''; last set_solver.
      by eapply Hextract2.
    + assert ([op] = t) as <-; first set_solver.
      assert (op' = op) as ->; first set_solver.
      rewrite Hevent.
      set_solver.
  - intros t op1 op2 Hin Hrel.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin].
    + apply rel_list_imp.
      by eapply Hextract3.
    + assert (t = [op]) as ->; first set_solver.
      destruct Hrel as (i & j & Hlt & Hlookup_i & Hlookup_j).
      rewrite list_lookup_singleton_Some in Hlookup_i.
      rewrite list_lookup_singleton_Some in Hlookup_j.
      lia.
Qed.

Lemma extraction_of_add2 lt t T1 T2 le op : 
  toLinEvent op = le →
  linToOp le = Some op →
  extraction_of lt (T1 ++ t :: T2) →
  extraction_of (lt ++ [le]) (T1 ++ (t ++ [op]) :: T2).
Proof.
  intros Hevent Hlin Hextract.
  split_and!.
  - intros le' op' Hin Hlin'.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]. 
    + destruct Hextract as (Hextract & _ ).
      destruct (Hextract le' op' Hin Hlin') as (t' & Ht'_in & Hop'_in). 
      rewrite elem_of_app in Ht'_in.
      destruct Ht'_in as [Ht'_in|Ht'_in]; first set_solver.
      rewrite elem_of_cons in Ht'_in.
      destruct Ht'_in as [->|Ht'_in]; last set_solver.
      exists (t ++ [op]); set_solver.
    + assert (op' = op) as ->; first set_solver.
      exists (t ++ [op]); set_solver.
  - intros t' op' Ht'_in Hop'_in.
    destruct Hextract as (_ & Hextract & _ ).
    rewrite elem_of_app in Ht'_in.
    destruct Ht'_in as [Ht'_in|Ht'_in]; first set_solver.
    rewrite elem_of_cons in Ht'_in.
    destruct Ht'_in as [->|Ht'_in]; last set_solver.
    rewrite elem_of_app in Hop'_in.
    destruct Hop'_in as [Hop'_in|Hop'_in]; set_solver.
  - intros t' op1 op2 Ht'_in Hrel. 
    destruct Hextract as (_ & Hextract1 & Hextract2).
    rewrite elem_of_app in Ht'_in.
    destruct Ht'_in as [Ht'_in|Ht'_in]; 
      first apply rel_list_imp; first set_solver.
    rewrite elem_of_cons in Ht'_in.
    destruct Ht'_in as [->|Ht'_in].
    + destruct Hrel as (i & j & Hlt & Hlookup_i & Hlookup_j).
      apply lookup_snoc_Some in Hlookup_i, Hlookup_j.
      destruct Hlookup_i as [(Hlength & Hlookup_i) | (-> & ->)]; last lia.
      destruct Hlookup_j as [(Hlength' & Hlookup_j) | (-> & ->)].
      * apply rel_list_imp.
        rewrite /rel_list in Hextract2.
        apply (Hextract2 t op1 op2); set_solver.
      * rewrite Hevent.
        assert (toLinEvent op1 ∈ lt) as Hin_lt.
        {
          apply (Hextract1 t op1); first set_solver.
          apply elem_of_list_lookup; eauto.
        }
        rewrite elem_of_list_lookup in Hin_lt.
        destruct Hin_lt as (i' & Hlookup_i').
        exists i', (length lt).
        split_and!.
        -- apply lookup_lt_is_Some_1.
           set_solver.
        -- rewrite lookup_app_Some; eauto.
        -- assert (length lt = Init.Nat.pred (length (lt ++ [le]))) as ->;  
            last by rewrite -last_lookup last_snoc.
           rewrite last_length; lia.
    + apply rel_list_imp.
      apply (Hextract2 t' op1 op2); set_solver.
Qed.

Lemma extraction_of_not_tag t lt tag T : 
  (¬∃ e, e ∈ lt ∧ tagOfEvent e = Some tag) →
  t ∈ T →
  extraction_of lt T →
  (¬∃ op, op ∈ t ∧ tagOfOp op = tag).
Proof.
  intros Hnot Hin Hextract.
  intros (op & Hop_in & Htag).
  apply Hnot.
  destruct Hextract as (_ & Hextract & _).
  specialize (Hextract t op Hin Hop_in).
  exists (toLinEvent op); split; first done.
  by apply tag_event_op.
Qed.

Lemma extraction_of_not_in (tag : string) lt T op : 
  tagOfOp op = tag →
  (¬(∃ e, e ∈ lt ∧ tagOfEvent e = Some tag)) →
  extraction_of lt T →
  ¬ (∃ t', t' ∈ T ∧ op ∈ t').
Proof.
  intros Htag Hnot Hextract (t' & Ht_in & Hop_in).
  apply Hnot.
  destruct Hextract as (_ & Hextract & _).
  specialize (Hextract t' op Ht_in Hop_in).
  exists (toLinEvent op).
  split; first done.
  by apply tag_event_op.
Qed.

Lemma extraction_of_add_init_lin le lt T :
  is_in_lin_event le →
  extraction_of lt T →
  extraction_of (lt ++ [le]) T.
Proof.
  intros Hevent (Hextract1 & Hextract2 & Hextract3).
  split_and!.
  - intros le' op Hin Hlin_op.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; 
      rewrite /is_in_lin_event in Hevent;
      set_solver.
  - set_solver.
  - intros t op1 op2 Hin Hrel.
    apply rel_list_imp.
    set_solver.
Qed.

Lemma trans_add_non_empty T1 T2 t' (op : operation) :
  (∀ t, t ∈ T1 ++ t' :: T2 → t ≠ []) →
  (∀ t, t ∈ T1 ++ (t' ++ [op]) :: T2 → t ≠ []).
Proof.
  intros Hhyp t Ht_in.
  specialize (Hhyp t).
  rewrite elem_of_app in Ht_in.
  destruct Ht_in as [Ht_in | Ht_in]; first set_solver.
  apply elem_of_cons in Ht_in.
  destruct Ht_in as [-> | Ht_in]; last set_solver.
  apply (elem_of_not_nil op).
  set_solver.
Qed.

Lemma valid_transaction_singleton op : 
  valid_transaction [op].
Proof.
  split_and!; try set_solver.
  - intros op1 op2 i j Hin1 Hin2 <-.
    rewrite list_lookup_singleton_Some in Hin1.
    rewrite list_lookup_singleton_Some in Hin2.
    lia.
  - intros tag c key ov tag1 v1 Hfalse. 
    exfalso.
    apply (rel_singleton_false _ _ _ Hfalse).
Qed.

Lemma valid_transactions_add1 T op c :
  (¬∃ t', t' ∈ T ∧ op ∈ t') →
  (∀ s k v, Rd s k (Some v) = op → ∃ t' s', t' ∈ T ∧ Wr s' k v ∈ t') →
  connOfOp op = c →
  valid_transaction [op] →
  (¬ (∃ t', t' ∈ T ∧ (∃ op, op ∈ t' ∧ last t' = Some op ∧ 
    connOfOp op = c ∧ (¬is_cm_op op)))) →
  valid_transactions T →
  valid_transactions (T ++ [[op]]).
Proof.
  intros Hnin Hread Hconn Hvalid Hnot Hvalid_trans.
  split_and!.
  - intros t' Hin.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; last set_solver.
    destruct Hvalid_trans as (Hvalid_trans & _).
    by apply Hvalid_trans.
  - intros t1 t2 op1 op2 i j c' Hlookup_i Hlookup_j Hlast_1 Hlast_2
    Hconn_1 Hconn_2 Hcm_1 Hcm_2.
    destruct Hvalid as (_ & Hvalid).
    destruct Hvalid_trans as (_ & Hvalid_trans & _).
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i | (Hlength_i & Hlookup_i)].
    + rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j | (Hlength_j & Hlookup_j)].
      * by eapply (Hvalid_trans).
      * rewrite list_lookup_singleton_Some in Hlookup_j.
        destruct Hlookup_j as (_ & <-).
        exfalso.
        apply Hnot.
        exists t1.
        split.
        -- apply elem_of_list_lookup; eauto.
        -- exists op1.
           split_and!; try done.
           ++ by apply last_Some_elem_of.
           ++ set_solver.
    + rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j | (Hlength_j & Hlookup_j)].
      * rewrite list_lookup_singleton_Some in Hlookup_i.
        destruct Hlookup_i as (_ & <-).
        exfalso.
        apply Hnot.
        exists t2.
        split.
        -- apply elem_of_list_lookup; eauto.
        -- exists op2.
           split_and!; try done.
           ++ by apply last_Some_elem_of.
           ++ set_solver.
      * rewrite list_lookup_singleton_Some in Hlookup_i.
        rewrite list_lookup_singleton_Some in Hlookup_j.
        lia.
  - intros op1 op2 t1 t2 i j Hlookup_i Hlookup_j Hop1 Hop2 Heq_op'.
    rewrite lookup_snoc_Some in Hlookup_i.
    rewrite lookup_snoc_Some in Hlookup_j.
    destruct Hvalid_trans as (_ & _ & Hvalid_trans).
    destruct Hlookup_i as [Hlookup_i|Hlookup_i].
    + destruct Hlookup_j as [Hlookup_j|Hlookup_j]; first set_solver.
      exfalso.
      apply Hnin.
      exists t1.
      split; first (apply elem_of_list_lookup; set_solver).
      destruct Hlookup_j as (_ & Heq_t2).
      subst.
      set_solver.
    + destruct Hlookup_j as [Hlookup_j|Hlookup_j]; last set_solver.
      exfalso.
      apply Hnin.
      exists t2.
      split; first (apply elem_of_list_lookup; set_solver).
      destruct Hlookup_i as (_ & Heq_t1).
      subst.
      set_solver.
Qed.

Lemma valid_transaction_add_op t op c tag : 
  (¬∃op, op ∈ t ∧ tagOfOp op = tag) →
  tagOfOp op = tag →
  connOfOp op = c → 
  (∃ op, op ∈ t ∧ last t = Some op ∧ 
      connOfOp op = c ∧ (¬is_cm_op op)) →
  (∀ s k ov tag1 v1, op = Rd s k ov → (Wr (tag1, c) k v1) ∈ t →
    (¬∃ tag2 v2, rel_list (t ++ [op]) (Wr (tag1, c) k v1) (Wr (tag2, c) k v2) ∧
                 rel_list (t ++ [op]) (Wr (tag2, c) k v2) op) →
    ov = Some v1) →
  valid_transaction t →
  valid_transaction (t ++ [op]).
Proof.
  intros Hnot Htag Hconn (op_last & Hin_last & Hlast & Hconn_last 
    & Hcm_last) Hread Hvalid.
  rewrite /is_cm_op in Hcm_last.
  split_and!.
  - intros op' s b Hop_in Hcm.
    rewrite elem_of_app in Hop_in.
    destruct Hop_in as [Hop_in|Hop_in].
    + destruct Hvalid as (Hvalid & _); set_solver. 
    + assert (op' = op) as <-; first set_solver.
      by rewrite last_snoc.
  - intros op1 op2 Hop1_in Hop2_in.
    destruct Hvalid as (_ & Hvalid & _).
    rewrite elem_of_app in Hop1_in.
    destruct Hop1_in as [Hop1_in|Hop1_in].
    + rewrite elem_of_app in Hop2_in.
      destruct Hop2_in as [Hop2_in|Hop2_in]; first set_solver.
      assert (op2 = op) as ->; first set_solver.
      rewrite Hconn -Hconn_last; set_solver.
    + assert (op1 = op) as ->; first set_solver.
      rewrite elem_of_app in Hop2_in.
      destruct Hop2_in as [Hop2_in|Hop2_in]; last set_solver.
      rewrite Hconn -Hconn_last; set_solver.
  - intros op1 op2 i j Hlookup_i Hlookup_j <-.
    destruct Hvalid as (_ & _ & Hvalid & _).
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i|(Hlength_i & Hlookup_i)].
    + rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j|(_ & Hlookup_j)]; first set_solver.
      assert (op = op1) as <-.
      {
        apply list_lookup_singleton_Some in Hlookup_j.
        set_solver.
      }
      assert (op ∈ t) as Hin; last set_solver.
      apply elem_of_list_lookup; eauto.
    + assert (op = op1) as <-.
      {
        apply list_lookup_singleton_Some in Hlookup_i.
        set_solver.
      }
      rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j|(Hlength_j & Hlookup_j)]. 
      * assert (op ∈ t) as Hin; last set_solver.
        apply elem_of_list_lookup; eauto.
      * rewrite list_lookup_singleton_Some in Hlookup_i.
        rewrite list_lookup_singleton_Some in Hlookup_j.
        lia.
  - intros tag' c' k ov tag1 v1 Hrel Hnot'.
    destruct Hvalid as (_ & Hvalid1 & _ & Hvalid2).
    assert (¬ (∃ (tag2 : string) (v2 : val),
              rel_list t (Wr (tag1, c') k v1)
              (Wr (tag2, c') k v2)
              ∧ rel_list t (Wr (tag2, c') k v2)
              (Rd (tag', c') k ov))) as Hnot''.
    {
      intros (tag2 & v2 & Hrel1 & Hrel2).
      apply Hnot'.
      exists tag2, v2.
      split; by apply rel_list_imp.
    }
    destruct Hrel as (i & j & Hlt & Hlookup_i & Hlookup_j).
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i|(Hlength_i & Hlookup_i)].
    + rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j|(Hlength_j & Hlookup_j)].
      * apply (Hvalid2 tag' c' k ov tag1 v1); last done. 
        rewrite /rel_list; eauto.
      * assert (c = c') as <-.
        {
          rewrite -Hconn_last.
          assert (connOfOp (Wr (tag1, c') k v1) = c') as <-;
            first by simpl.
          assert ((Wr (tag1, c') k v1) ∈ t); 
            first apply elem_of_list_lookup; first eauto.
          by apply Hvalid1.
        }
        assert (op = Rd (tag', c) k ov) as ->.
        {
          rewrite list_lookup_singleton_Some in Hlookup_j.
          set_solver.
        }
        apply (Hread (tag', c) k ov tag1 v1); try done.
        apply elem_of_list_lookup; eauto.
    + rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j|(Hlength_j & Hlookup_j)].
      * apply lookup_lt_Some in Hlookup_j.
        lia.
      * rewrite list_lookup_singleton_Some in Hlookup_i. 
        rewrite list_lookup_singleton_Some in Hlookup_j.
        lia.
Qed.

Lemma valid_transactions_add2 T1 T2 tag op t c :
  (¬∃ t', t' ∈ (T1 ++ t :: T2) ∧ op ∈ t') →
  (¬∃op, op ∈ t ∧ tagOfOp op = tag) →
  tagOfOp op = tag →
  (∀ s k ov tag1 v1, op = Rd s k ov → (Wr (tag1, c) k v1) ∈ t →
    (¬∃ tag2 v2, rel_list (t ++ [op]) (Wr (tag1, c) k v1) (Wr (tag2, c) k v2) ∧
                 rel_list (t ++ [op]) (Wr (tag2, c) k v2) op) →
    ov = Some v1) →
  connOfOp op = c → 
  (∃ op, op ∈ t ∧ last t = Some op ∧ 
    connOfOp op = c ∧ (¬is_cm_op op)) →
  valid_transactions (T1 ++ t :: T2) →
  valid_transactions (T1 ++ (t ++ [op]) :: T2).
Proof.
  intros Hnin Hnot Htag Hread Hconn Hlast Hvalid.
  split_and!.
  - intros t' Ht'_in.
    destruct Hvalid as (Hvalid & _).
    rewrite elem_of_app in Ht'_in.
    destruct Ht'_in as [Ht'_in|Ht'_in]; first set_solver.
    rewrite elem_of_cons in Ht'_in.
    destruct Ht'_in as [->|Ht'_in]; last set_solver.
    assert (valid_transaction t); first set_solver.
    eapply valid_transaction_add_op; try done.
  - intros t1 t2 op1 op2 i j c' Hlookup_i Hlookup_j
      Hlast1 Hlast2 Hconn1 Hconn2 Hcm1 Hcm2.
    destruct Hvalid as (_ & Hvalid & _).
    pose proof Hvalid as Hvalid'.
    specialize (Hvalid t1 t2 op1 op2 i j c').
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i|(Hlength_i & Hlookup_i)].
    + rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j|(_ & Hlookup_j)].
      * eapply Hvalid; try done; apply lookup_app_Some; by left.
      * rewrite lookup_cons_Some in Hlookup_j.
        destruct Hlookup_j as [(Hlength & <-)|(Hlength & Hlookup_j)].
        -- assert (i = length T1) as Heq.
           {
             destruct Hlast as (op_l & Hop_l_in & Hop_l_last & 
              Hop_l_conn & Hop_l_cm).
             apply (Hvalid' t1 t op1 op_l i (length T1) c'); try done.
             - apply lookup_app_Some; by left.
             - by apply list_lookup_middle.
             - rewrite last_snoc in Hlast2.
               inversion Hlast2 as [Heq].
               rewrite -Hconn2; set_solver.
           }
           apply lookup_lt_Some in Hlookup_i; lia.
        -- eapply Hvalid; try done; apply lookup_app_Some; first by left.
           right.
           split; first lia.
           apply lookup_cons_Some; eauto.
    + rewrite lookup_cons_Some in Hlookup_i.
      destruct Hlookup_i as [(Hlength_i' & <-)|(Hlength_i' & Hlookup_i)].
      * rewrite lookup_app_Some in Hlookup_j.
        destruct Hlookup_j as [Hlookup_j|(Hlength_j & Hlookup_j)].
        -- assert (length T1 = j) as Heq.
           {
             destruct Hlast as (op_l & Hop_l_in & Hop_l_last & 
              Hop_l_conn & Hop_l_cm).
             apply (Hvalid' t t2 op_l op2 (length T1) j c'); try done.
             - by apply list_lookup_middle.
             - apply lookup_app_Some; by left.
             - rewrite last_snoc in Hlast1.
               inversion Hlast1 as [Heq].
               rewrite -Hconn1; set_solver.
           }
           apply lookup_lt_Some in Hlookup_j; lia.
        -- rewrite lookup_cons_Some in Hlookup_j.
           destruct Hlookup_j as [(Hlength_j' & <-)|(Hlength_j' & Hlookup_j)];
            first lia.
           assert (length T1 = j) as Heq.
           {
             destruct Hlast as (op_l & Hop_l_in & Hop_l_last & 
              Hop_l_conn & Hop_l_cm).
             apply (Hvalid' t t2 op_l op2 (length T1) j c'); try done.
             - by apply list_lookup_middle.
             - apply lookup_app_Some; right.
               split; first done.
               apply lookup_cons_Some; right; auto.
             - rewrite last_snoc in Hlast1.
               inversion Hlast1 as [Heq].
               rewrite -Hconn1; set_solver.
           }
           apply lookup_lt_Some in Hlookup_j; lia.
      * rewrite lookup_app_Some in Hlookup_j.
        destruct Hlookup_j as [Hlookup_j|(Hlength_j & Hlookup_j)].
        -- eapply Hvalid; try done; apply lookup_app_Some; last by left.
           right.
           split; first lia.
           apply lookup_cons_Some; eauto.
        -- rewrite lookup_cons_Some in Hlookup_j.
           destruct Hlookup_j as [(Hlength_j' & <-)|(Hlength_j' & Hlookup_j)].
           ++ assert (i = length T1) as Heq.
              {
                destruct Hlast as (op_l & Hop_l_in & Hop_l_last & 
                Hop_l_conn & Hop_l_cm).
                apply (Hvalid' t1 t op1 op_l i (length T1) c'); try done.
                - apply lookup_app_Some; right.
                  split; first done.
                  apply lookup_cons_Some; right; auto.
                - by apply list_lookup_middle.
                - rewrite last_snoc in Hlast2.
                  inversion Hlast2 as [Heq].
                  rewrite -Hconn2; set_solver.
              }
              apply lookup_lt_Some in Hlookup_i; lia.
           ++ eapply Hvalid; try done; apply lookup_app_Some; right.
              all : split; first lia.
              all : apply lookup_cons_Some; eauto.
  - intros op1 op2 t1 t2 i j Hlookup_i Hlookup_j Hop1 Hop2 Heq_op.
    destruct Hvalid as (_ & _ & Hvalid).
    rewrite lookup_app_Some in Hlookup_i.
    rewrite lookup_app_Some in Hlookup_j.
    destruct Hlookup_i as [Hlookup_i|(Hlength_i & Hlookup_i)];
      destruct Hlookup_j as [Hlookup_j|(Hlength_j & Hlookup_j)].
    + eapply (Hvalid op1 op2 t1 t2 i j); try done; by eapply lookup_app_l_Some.
    + rewrite lookup_cons_Some in Hlookup_j.
      destruct Hlookup_j as [(Hlength_j' & Hlookup_j)|Hlookup_j].
      * rewrite -Hlookup_j in Hop2.
        rewrite elem_of_app in Hop2.
        destruct Hop2 as [Hop2|Hop2].
        -- eapply (Hvalid _ _ t1 t); try done.
           ++ apply lookup_app_Some; set_solver.
           ++ apply lookup_app_Some; right.
              split; first done.
              apply lookup_cons_Some; left; set_solver.
        -- exfalso.
           apply Hnin.
           exists t1.
           split.
           ++ rewrite elem_of_app; left.
              apply elem_of_list_lookup; eauto.
           ++ assert (op2 = op) as ->; set_solver.
      * eapply (Hvalid _ _ t1 t2); try done.
        -- apply lookup_app_Some; set_solver.
        -- apply lookup_app_Some; right.
           split; first done.
           apply lookup_cons_Some; set_solver.
    + rewrite lookup_cons_Some in Hlookup_i.
      destruct Hlookup_i as [(Hlength_i' & Hlookup_i)|Hlookup_i].
      * rewrite -Hlookup_i in Hop1.
        rewrite elem_of_app in Hop1.
        destruct Hop1 as [Hop1|Hop1]. 
        -- eapply (Hvalid _ _ t t2); try done.
           ++ apply lookup_app_Some; right.
              split; first done.
              apply lookup_cons_Some; left; set_solver.
           ++ apply lookup_app_Some; set_solver.
        -- exfalso.
           apply Hnin.
           exists t2.
           split.
           ++ rewrite elem_of_app; left.
              apply elem_of_list_lookup; eauto.
           ++ assert (op1 = op) as ->; set_solver.
      * eapply (Hvalid _ _ t1 t2); try done.
        -- apply lookup_app_Some; right.
           split; first done.
           apply lookup_cons_Some; set_solver.
        -- apply lookup_app_Some; set_solver.
    + rewrite lookup_cons_Some in Hlookup_i.
      rewrite lookup_cons_Some in Hlookup_j.
      destruct Hlookup_i as [(Hlength_i' & Hlookup_i)|(Hlength_i' & Hlookup_i)];
        destruct Hlookup_j as [(Hlength_j' & Hlookup_j)|(Hlength_j' & Hlookup_j)].
      * lia.
      * rewrite -Hlookup_i in Hop1.
        rewrite elem_of_app in Hop1.
        destruct Hop1 as [Hop1|Hop1]. 
        -- eapply (Hvalid _ _ t t2); try done.
           all : apply lookup_app_Some; right.
           all : split; first done.
           1 : apply lookup_cons_Some; left; set_solver.
           apply lookup_cons_Some; right; set_solver.
        -- exfalso.
           apply Hnin.
           exists t2.
           split.
           ++ rewrite elem_of_app; right.
              rewrite elem_of_cons; right.
              apply elem_of_list_lookup; eauto.
           ++ assert (op1 = op) as ->; set_solver.
      * rewrite -Hlookup_j in Hop2.
        rewrite elem_of_app in Hop2.
        destruct Hop2 as [Hop2|Hop2]. 
        -- eapply (Hvalid _ _ t1 t); try done.
           all : apply lookup_app_Some; right.
           all : split; first done.
           1 : apply lookup_cons_Some; right; set_solver.
           apply lookup_cons_Some; left; set_solver.
        -- exfalso.
           apply Hnin.
           exists t1.
           split.
           ++ rewrite elem_of_app; right.
              rewrite elem_of_cons; right.
              apply elem_of_list_lookup; eauto.
           ++ assert (op2 = op) as ->; set_solver.
      * eapply (Hvalid _ _ t1 t2); try done.
        1, 2 : apply lookup_app_Some; right.
        1, 2 : split; first done.
        1, 2 : apply lookup_cons_Some; set_solver.
Qed.

Lemma based_on_add1 op exec T1 T2 trans :
  ¬is_cm_op op →
  (∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false) →
  based_on exec (comTrans (T1 ++ trans :: T2)) →
  based_on exec (comTrans (T1 ++ (trans ++ [op]) :: T2)).
Proof.
  intros Hnot Hop Hbased.
  by rewrite -com_trans_eq1.
Qed.

Lemma based_on_add2 op exec T :
  ¬is_cm_op op →
  based_on exec (comTrans T) →
  based_on exec (comTrans (T ++ [[op]])). 
Proof.
  intros Hnot Hbased.
  by rewrite -com_trans_eq2.
Qed.

Lemma based_on_add3 sig b exec T s :
  based_on exec (comTrans T) →
  based_on (optionalExtendExecution exec [Cm sig b] s) (comTrans (T ++ [[Cm sig b]])).
Proof. 
  intros Hbased.
  rewrite /optionalExtendExecution /comTrans.
  rewrite List.filter_app.
  simpl.
  destruct b.
  - intros t.
    split.
    + intros Hhyp.
      rewrite split_split in Hhyp.
      simpl in Hhyp.
      destruct (Hbased t) as (Himp & _).
      set_solver.
    + intros Hhyp.
      rewrite elem_of_app in Hhyp.
      destruct Hhyp as [Hhyp|Hhyp].
      * destruct (Hbased t) as (_ & Himp).
        destruct (Himp Hhyp) as (Hin & Hneq).
        split; last done.
        rewrite split_split.
        simpl.
        set_solver.
      * split; last set_solver.
        rewrite split_split.
        simpl.
        set_solver.
  - rewrite app_nil_r.
    by rewrite /comTrans in Hbased.
Qed.

Lemma based_on_add4 s sig b exec T1 T2 trans :
  (∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false) ->
  based_on exec (comTrans (T1 ++ trans :: T2)) →
  based_on (optionalExtendExecution exec (trans ++ [Cm sig b]) s) (comTrans (T1 ++ (trans ++ [Cm sig b]) :: T2)).
Proof.
  intros Hop Hbased.
  rewrite /optionalExtendExecution /comTrans.
  rewrite List.filter_app.
  simpl.
  rewrite last_snoc.
  destruct b.
  - intros t.
    split.
    + intros Hhyp.
      rewrite split_split in Hhyp.
      simpl in Hhyp.
      destruct (Hbased t) as (Himp & _).
      destruct Hhyp as (Hin & Hneq).
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin]; last set_solver.
      assert (t ∈ comTrans (T1 ++ trans :: T2)) as Hin'; first set_solver.
      assert (comTrans (T1 ++ trans :: T2) = comTrans (T1 ++ T2)) as Heq.
      {
        rewrite /comTrans. 
        do 2 rewrite List.filter_app.
        simpl.
        destruct Hop as (op & _ & -> & Hcm).
        rewrite /isCmOp in Hcm.
        destruct op; simpl; set_solver.
      }
      rewrite Heq in Hin'.
      rewrite /comTrans List.filter_app in Hin'.
      set_solver.
    + intros Hhyp.
      rewrite elem_of_app in Hhyp.
      destruct Hhyp as [Hhyp|Hhyp].
      * destruct (Hbased t) as (_ & Himp).
        assert (t ∈ comTrans (T1 ++ trans :: T2)) as Hin.
        {
          rewrite /comTrans List.filter_app.
          set_solver.
        }
        destruct (Himp Hin) as (Hin' & Hneq).
        split; last done.
        rewrite split_split.
        simpl.
        set_solver.
      * rewrite elem_of_cons in Hhyp. 
        destruct Hhyp as [->|Hhyp].
        -- split.
           ++ rewrite split_split.
              simpl.
              set_solver.
           ++ intros Hfalse; rewrite app_nil in Hfalse.
              set_solver.
        -- destruct (Hbased t) as (_ & Himp).
           assert (t ∈ comTrans (T1 ++ trans :: T2)) as Hin.
           {
             rewrite /comTrans List.filter_app; simpl.
             destruct Hop as (op & _ & -> & Hcm).
             destruct op; simpl; set_solver.
           }
           destruct (Himp Hin) as (Hin' & Hneq).
           split; last done.
           rewrite split_split.
           simpl.
           set_solver.
  - rewrite /comTrans List.filter_app in Hbased.
    simpl in Hbased.
    destruct Hop as (op & _ & Heq & Hcm).
    rewrite Heq in Hbased.
    rewrite /isCmOp in Hcm.
    destruct op; simpl; set_solver.
Qed.

Lemma extend_execution_imp test i e1 e2 exec trans sig t s s' :
  last exec = Some (t, s) →
  applied_transaction s s' (trans ++ [Cm sig true]) →
  valid_execution test exec →
  (exec ++ [(trans ++ [Cm sig true], s')]) !! i = Some e1 →
  (exec ++ [(trans ++ [Cm sig true], s')]) !! (i + 1) = Some e2 →
  applied_transaction e1.2 e2.2 e2.1.
Proof.
  intros Hlast Happl (Hvalid & _) Hlookup1 Hlookup2.
  simpl.
  rewrite lookup_snoc_Some in Hlookup1.
  rewrite lookup_snoc_Some in Hlookup2.
  destruct Hlookup2 as [Hlookup2|(Hlength & <-)].
  - destruct Hlookup1 as [Hlookup1|Hlookup1]; last lia.
    set_solver.
  - destruct Hlookup1 as [Hlookup1|Hlookup1]; last lia.
    simpl.
    rewrite last_lookup in Hlast.
    assert (i = Init.Nat.pred (length exec)) as Heq; first lia.
    assert (e1 = (t, s)) as ->; set_solver.
Qed.

Lemma valid_trace_pre T tag t e lt exec test : 
  lin_trace_of lt t →
  is_pre_event e →
  tagOfEvent e = Some tag →
  tag ∉ tags t →
  valid_sequence lt →
  valid_transactions T → 
  extraction_of lt T →
  (∀ t, t ∈ T → t ≠ []) →
  based_on exec (comTrans T) →
  valid_execution test exec →
  valid_trace test (t ++ [e]).
Proof.
  intros Hlin Hexists Hpost Htag Hvalid Hvalid_trans 
    Hextract Hempty Hbased Hvalid_exec.
  exists lt.
  split_and!; try done.
  - apply (lin_trace_valid tag); try done; eauto.
  - exists T, exec.
    split_and!; try done.
Qed.

Lemma valid_trace_post T tag t e lt exec test : 
  lin_trace_of lt t →
  (∃ le, postToLin e = Some le ∧ le ∈ lt) →
  is_post_event e →
  tagOfEvent e = Some tag →
  valid_sequence lt →
  valid_transactions T → 
  extraction_of lt T →
  (∀ t, t ∈ T → t ≠ []) →
  based_on exec (comTrans T) →
  valid_execution test exec →
  valid_trace test (t ++ [e]).
Proof.
  intros Hlin Hexists Hpost Htag Hvalid Hvalid_trans 
    Hextract Hempty Hbased Hvalid_exec.
  exists lt.
  split_and!; try done.
  - apply (lin_trace_valid tag); try done.
    right.
    rewrite /is_post_event in Hpost.
    set_solver.
  - exists T, exec. 
    split_and!; try done.
Qed.