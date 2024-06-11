From iris.algebra Require Import gmap list.
From aneris.examples.transactional_consistency Require Import user_params.
From stdpp Require Import strings.
From aneris.aneris_lang Require Import network resources.

(* Type for tag-connection pairs. 
  We assume:
    - tags are unique 
    - at most one transactions can be active per connection *)
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

Definition connOfEvent (event : val) : option val :=
  match event with 
    | (_, (c, _))%V => Some c
    | (_, c)%V => Some c
    | _ => None
  end.

Definition tagOfEvent (event : val) : option string :=
  match event with 
    | (#(LitString tag), _)%V => Some tag
    | _ => None
  end.

Definition transaction : Type := list operation.

Definition valid_transaction (t : transaction) : Prop :=
  (* The last operation is the commit operation *)
  (∃ s b, last t = Some (Cm s b)) ∧ 
  (* There is only one commit operation *)
  (∀ op s b, op ∈ t → op = Cm s b → last t = Some op) ∧
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
  (∀ t tag c k ov tag1 v1, t ∈ T → 
                          rel_list t (Wr (tag1, c) k v1) (Rd (tag, c) k ov) →
                          (¬∃ tag2 v2, rel_list t (Wr (tag1, c) k v1) (Wr (tag2, c) k v2) ∧
                                       rel_list t (Wr (tag2, c) k v2) (Rd (tag, c) k ov)) →
                            ov = Some v1) ∧ 
  (* Transactions read from some write *)
  (∀ t s k v, t ∈ T → 
                  Rd s k (Some v) ∈ t →
                  ∃ t' s', t' ∈ T ∧ Wr s' k v ∈ t') ∧
  (* Transactions satisfy the baseline transaction contraints *)
  (∀ t, t ∈ T → valid_transaction t) ∧
  (* No duplicate transactions *)
  (∀ t1 t2 i j, T !! i = Some t1 → T !! j = Some t2 → t1 = t2 → i = j) ∧
  (* No mixing of connections *) 
  (∀ t1 t2 op1 op2, t1 ∈ T → t2 ∈ T → op1 ∈ t1 → op2 ∈ t2 → connOfOp op1 = connOfOp op2 → t1 = t2).

Definition state : Type := gmap Key val.

Definition execution : Type := list (transaction * state).

Definition commitTest : Type := execution -> transaction -> Prop.

Definition applyTransaction (s : state) (t : transaction) : state := 
  foldl (λ s op, match op with | Wr sig k v => <[k := v]> s | _ => s end) s t.

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
  ∀ tag c k ov, (Rd (tag, c) k ov) ∈ t →  ∃ s, read_state c k ov exec s.

Definition commit_test_rc : commitTest := 
  λ exec trans, pre_read exec trans.

(** Snapshot Isolation *)

Definition complete (exec : execution) (t : transaction)  (s : state): Prop := 
  ∀ tag c k ov, (Rd (tag, c) k ov) ∈ t → read_state c k ov exec s.

Definition parent_state (exec : execution) (t : transaction) (s : state) : Prop :=
  ∃ i t' s', exec !! i = Some (t' , s) ∧ exec !! (i + 1) = Some (t, s').

Definition no_conf (exec : execution) (t : transaction) (s : state) : Prop := 
  ¬(∃ k, (∃ sig v, Wr sig k v ∈ t) ∧ 
         (∀ sp, parent_state exec t sp → s !! k ≠ sp !! k)). 

Definition commit_test_si : commitTest := 
  λ exec trans, ∃ s, s ∈ (split exec).2 ∧ 
                complete exec trans s ∧ 
                no_conf exec trans s.

(** Embedding into the trace infrastructure *)

Definition toPostEvent (op : operation) : val := 
  match op with 
    | Rd (tag, c) k None => (#tag, (c, (#"RdPost", (#k, NONEV))))
    | Rd (tag, c) k (Some v) => (#tag, (c, (#"RdPost", (#k, SOMEV v))))
    | Wr (tag, c) k v => (#tag, (c, (#"WrPost", (#k, v))))
    | Cm (tag, c) b => (#tag, (c, (#"CmPost", #b)))
  end.

Definition toPreEvent (op : operation) : val := 
  match op with 
    | Rd (tag, c) _ _ => (#tag, (c, #"RdPre")) 
    | Wr (tag, c) k v => (#tag, (c, (#"WrPre", (#k, v))))
    | Cm (tag, c) _ => (#tag, (c, #"CmPre"))
  end.

Definition postToPre (event : val) : option val := 
  match event with 
    | (#(LitString tag), (c, (#"StPost")))%V => Some (#tag, (c, #"StPre"))%V
    | (#(LitString tag), (c, (#"RdPost", (#(LitString k), NONEV))))%V => Some (#tag, (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"RdPost", (#(LitString k), SOMEV v))))%V => Some (#tag, (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"WrPost", (#(LitString k), v))))%V => Some (#tag, (c, (#"WrPre", (#k, v))))%V
    | (#(LitString tag), (c, (#"CmPost", #(LitBool b))))%V => Some (#tag, (c, #"CmPre"))%V
    | (#(LitString tag), (c, #"InitPost"))%V => Some (#tag, (#"", #"InitPre"))%V
    | _ => None 
  end.

Definition toLinEvent (op : operation) : val := 
  match op with 
    | Rd (tag, c) k None => (#tag, (c, (#"Rd", (#k, NONEV))))
    | Rd (tag, c) k (Some v) => (#tag, (c, (#"Rd", (#k, SOMEV v))))
    | Wr (tag, c) k v => (#tag, (c, (#"Wr", (#k, v))))
    | Cm (tag, c) b => (#tag, (c, (#"Cm", #b)))
  end.

Definition linToOp (le : val) : option operation := 
  match le with 
    | (#(LitString tag), (c, (#"Rd", (#(LitString k), NONEV))))%V => Some (Rd (tag, c) k None)
    | (#(LitString tag), (c, (#"Rd", (#(LitString k), SOMEV v))))%V => Some (Rd (tag, c) k (Some v))
    | (#(LitString tag), (c, (#"Wr", (#(LitString k), v))))%V => Some (Wr (tag, c) k v)
    | (#(LitString tag), (c, (#"Cm", #(LitBool b))))%V => Some (Cm (tag, c) b)
    | _ => None 
  end.

Definition is_init_pre_event (v : val) : Prop := ∃ tag, v = (#tag, (#"", #"InitPre"))%V.

Definition is_init_post_event (v : val) : Prop := ∃ tag c, v = (#tag, (c, #"InitPost"))%V.

Definition is_st_pre_event (v : val) : Prop := ∃ tag c, v = (#tag, (c, #"StPre"))%V.

Definition is_st_post_event (v : val) : Prop := ∃ tag c, v = (#tag, (c, #"StPost"))%V.

Definition is_rd_pre_event (v : val) : Prop := ∃ tag c, v = (#tag, (c, #"RdPre"))%V.

Definition is_rd_post_event (v : val) : Prop := 
  (∃ tag c k v', v = (#tag, (c, (#"RdPost", (#k, SOMEV v'))))%V) ∨ 
  (∃ tag c k, v = (#tag, (c, (#"RdPost", (#k, NONEV))))%V).

Definition is_wr_pre_event (v : val) : Prop := ∃ tag c k v', v = (tag, (c, (#"WrPre", (#k, v'))))%V.

Definition is_wr_post_event (v : val) : Prop := ∃ tag c k v', v = (tag, (c, (#"WrPost", (#k, v'))))%V.

Definition is_cm_pre_event (v : val) : Prop := ∃ tag c, v = (#tag, (c, #"CmPre"))%V.

Definition is_cm_post_event (v : val) : Prop := ∃ tag c b, v = (tag, (c, (#"CmPost", #b)))%V.

Definition is_pre_event (v : val) : Prop := 
  is_st_pre_event v ∨ is_rd_pre_event v ∨ is_wr_pre_event v ∨ is_cm_pre_event v ∨ is_init_pre_event v.

Definition is_post_event (v : val) : Prop := 
  is_st_post_event v ∨ is_rd_post_event v ∨ is_wr_post_event v ∨ is_cm_post_event v ∨ is_init_post_event v.

Definition is_st_lin_event (v : val) : Prop := ∃ tag c, v = (#tag, (c, #"StLin"))%V.

Definition is_rd_lin_event (v : val) : Prop := 
  (∃ tag c k v', v = (#tag, (c, (#"RdLin", (#k, SOMEV v'))))%V) ∨ 
  (∃ tag c k, v = (#tag, (c, (#"RdLin", (#k, NONEV))))%V).

Definition is_wr_lin_event (v : val) : Prop := ∃ tag c k v', v = (#tag, (c, (#"WrLin", (#k, v'))))%V.

Definition is_cm_lin_event (v : val) : Prop := ∃ tag c b, v = (#tag, (c, (#"CmLin", #b)))%V.

Definition is_lin_event (v : val) : Prop := 
  is_st_lin_event v ∨ is_rd_lin_event v ∨ is_wr_lin_event v ∨ is_cm_lin_event v.

Definition extraction_of (lin_trace : list val) (T : list transaction) : Prop := 
  (* Linerization point trace and transactions contain the same operations *)
  (∀ le op, le ∈ lin_trace → linToOp le = Some op → ∃ t, t ∈ T → op ∈ t) ∧
  (∀ t op, t ∈ T → op ∈ t → (toLinEvent op) ∈ lin_trace) ∧
  (* Order amongst operations is preserved *)
  (∀ t op1 op2, t ∈ T → rel_list t op1 op2 → rel_list lin_trace (toLinEvent op1) (toLinEvent op2)).

(* This is to be used with traces of linearization point events *)
Definition valid_sequence (lin_trace : list val) : Prop :=
  (* Read, write and commit events have a prior start event *)
  (∀ e c, e ∈ lin_trace → 
          connOfEvent e = Some c → 
          (is_rd_lin_event e ∨ is_wr_lin_event e ∨ is_cm_lin_event e) → 
          (∃ e_st, connOfEvent e_st = Some c ∧ is_st_lin_event e_st ∧ rel_list lin_trace e_st e ∧ 
                   (¬∃ e_cm, connOfEvent e_cm = Some c ∧ is_cm_lin_event e_cm ∧
                             rel_list lin_trace e_st e_cm ∧ rel_list lin_trace e_cm e))) ∧
  (* There is at most one active transaction per connection *)
  (∀ e_st c, e_st ∈ lin_trace → 
             connOfEvent e_st = Some c → 
             is_st_lin_event e_st → 
             ((∃ e_cm, connOfEvent e_cm = Some c ∧ is_cm_lin_event e_cm ∧ rel_list lin_trace e_st e_cm ∧ 
                       (¬∃ e_st', connOfEvent e_st' = Some c ∧ is_st_lin_event e_st' ∧ 
                                  rel_list lin_trace e_st e_st' ∧ rel_list lin_trace e_st' e_cm)) ∨ 
             (¬∃ e,  connOfEvent e = Some c ∧ rel_list lin_trace e_st e ∧
                     (is_st_lin_event e ∨ is_cm_lin_event e)))).

Definition comTrans (T : list transaction) : list transaction := 
  List.filter (λ t, match last t with | Some (Cm s true) => true | _ => false end) T.

Definition based_on (exec : execution) (transactions : list transaction) : Prop :=
  ∀ t, (t ∈ (split exec).1 ∧ t ≠ []) ↔ t ∈ transactions.

Definition linToPost (lin_event : val) : option val := 
  match lin_event with 
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
    | (#(LitString tag), (c, (#"StLin")))%V => 
      Some (#(LitString tag), (c, #"StPre"))%V
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), NONEV))))%V => 
      Some (#(LitString tag), (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V => 
      Some (#(LitString tag), (c, #"RdPre"))%V
    | (#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V => 
      Some (#(LitString tag), (c, (#"WrPre", (#(LitString k), v))))%V
    | (#(LitString tag), (c, (#"CmLin", #(LitBool b))))%V => 
      Some (#(LitString tag), (c, #"CmPre"))%V
    | _ => None 
  end.

Definition postToLin (event : val) : option val := 
  match event with 
    | (#(LitString tag), (c, (#"StPost")))%V => 
      Some (#(LitString tag), (c, (#"StLin")))%V
    | (#(LitString tag), (c, (#"RdPost", (#(LitString k), NONEV))))%V => 
      Some (#(LitString tag), (c, (#"RdLin", (#(LitString k), NONEV))))%V
    | (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V => 
      Some (#(LitString tag), (c, (#"RdLin", (#(LitString k), SOMEV v))))%V
    | (#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V => 
      Some (#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V
    | (#(LitString tag), (c, (#"CmLin", #(LitBool b))))%V => 
      Some (#(LitString tag), (c, (#"CmLin", #(LitBool b))))%V
    | _ => None
  end.

Definition lin_trace_of (lin_trace trace : list val) : Prop := 
  (* Elements are preserved *)
  (∀ e_post, e_post ∈ trace → ∃ le, postToLin e_post = Some le → le ∈ lin_trace) ∧
  (∀ le, le ∈ lin_trace → ∃ e_pre, is_pre_event e_pre ∧ linToPre le = Some e_pre ∧ e_pre ∈ trace ∧ 
                                    (∀ e_post, (e_post ∈ trace ∧ is_post_event e_post ∧ postToPre e_post = Some e_pre) 
                                               → linToPost le = Some e_post)) ∧
  (* Only one linerization point per operation *)
  (∀ le1 le2, le1 ∈ lin_trace → le2 ∈ lin_trace → 
              ∃ e_pre, linToPre le1 = Some e_pre → linToPre le2 = Some e_pre → le1 = le2) ∧
  (* Order is preserved *)
  (∀ le1 le2, rel_list lin_trace le1 le2 → 
              ¬(∃ e1_pre e2_post, linToPre le1 = Some e1_pre ∧
                                  linToPost le2 = Some e2_post  ∧
                                  rel_list trace e2_post e1_pre)) ∧
  (* No duplicates *)
  (∀ le1 le2 i j, lin_trace !! i = Some le1 → lin_trace !! j = Some le2 → le1 = le2 → i = j).

Definition valid_trace (test : commitTest) : list val → Prop :=
  λ trace, ∃ lin_trace, lin_trace_of lin_trace trace ∧ valid_sequence lin_trace ∧ 
           (∃ T exec, valid_transactions T ∧ extraction_of lin_trace T ∧  
                      based_on exec (comTrans T) ∧ valid_execution test exec).

Definition valid_trace_ru : list val → Prop := valid_trace commit_test_ru.

Definition valid_trace_rc : list val → Prop := valid_trace commit_test_rc.

Definition valid_trace_si : list val → Prop := valid_trace commit_test_si.

Lemma valid_trace_ru_empty : valid_trace_ru [].
Proof.
  rewrite /valid_trace_ru /valid_trace.
  exists [].
  split.
  - rewrite /lin_trace_of.
    do 3 (split; first set_solver).
    split; last set_solver.
    rewrite /rel_list.
    set_solver.
  - split. 
    + rewrite /valid_sequence.
      split; intros; set_solver.
    + intros.
      exists [], [([], ∅)].
      split.
      * rewrite /valid_transactions.
        split; first set_solver.
        split; set_solver.
      * split.
        -- rewrite /extraction_of.
            do 2 (split; first set_solver).
            set_solver.
        -- split.
            ++ rewrite /based_on.
               intro t.
               split; set_solver.
            ++ rewrite /valid_execution.
               split; last done.
               intros.
               destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
               destruct i; first done.
               set_solver.
Qed.

Lemma valid_trace_rc_empty : valid_trace_rc [].
  rewrite /valid_trace_rc /valid_trace.
  exists [].
  split.
  - rewrite /lin_trace_of.
    do 3 (split; first set_solver).
    split; last set_solver.
    rewrite /rel_list.
    set_solver.
  - split. 
    + rewrite /valid_sequence.
      split; intros; set_solver.
    + intros.
      exists [], [([], ∅)].
      split.
      * rewrite /valid_transactions.
        split; first set_solver.
        split; set_solver.
      * split.
        -- rewrite /extraction_of.
           do 2 (split; first set_solver).
           set_solver.
        -- split.
          ++ rewrite /based_on.
             intro t.
             split; set_solver.
          ++ rewrite /valid_execution.
             split.
             ** intros.
                destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
                destruct i; first done.
                set_solver.
             ** split; first done.
                intros.
                rewrite /commit_test_rc /pre_read.
                assert (t = []) as ->; set_solver.
Qed.

Lemma valid_trace_si_empty : valid_trace_si [].
  rewrite /valid_trace_si /valid_trace.
  exists [].
  split.
  - rewrite /lin_trace_of.
    do 3 (split; first set_solver).
    split; last set_solver.
    rewrite /rel_list.
    set_solver.
  - split.
    + rewrite /valid_sequence.
      split; intros; set_solver.
    + intros.
      exists [], [([], ∅)].
      split.
      * rewrite /valid_transactions.
        split; first set_solver.
        split; set_solver.
      * split.
        -- rewrite /extraction_of.
           do 2 (split; first set_solver).
           set_solver.
        -- split.
           ++ rewrite /based_on.
              intro t.
              split; set_solver.
           ++ rewrite /valid_execution.
              split.
              ** intros.
                 destruct (decide (i = 0)) as [->|Hfalse]; first set_solver.
                 destruct i; first done.
                 set_solver.
              ** split; first done.
                 intros.
                 rewrite /commit_test_si.
                 exists ∅.
                 simpl.
                 split; first set_solver.
                 assert (t = []) as ->; first set_solver.
                 split.
                 --- rewrite /complete.
                     set_solver.
                 --- rewrite /no_conf.
                     set_solver.
Qed.