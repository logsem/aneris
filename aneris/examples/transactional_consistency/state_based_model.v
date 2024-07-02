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

Definition is_init_pre_event (v : val) : Prop := ∃ (tag : string), v = (#tag, (#"", #"InitPre"))%V.

Definition is_init_post_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"InitPost"))%V.

Definition is_st_pre_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"StPre"))%V.

Definition is_st_post_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"StPost"))%V.

Definition is_rd_pre_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"RdPre"))%V.

Definition is_rd_post_event (v : val) : Prop := 
  (∃ (tag k : string) (c v': val), v = (#tag, (c, (#"RdPost", (#k, SOMEV v'))))%V) ∨ 
  (∃ (tag k : string) (c : val), v = (#tag, (c, (#"RdPost", (#k, NONEV))))%V).

Definition is_wr_pre_event (v : val) : Prop := ∃ (tag k : string) (c v' : val), v = (#tag, (c, (#"WrPre", (#k, v'))))%V.

Definition is_wr_post_event (v : val) : Prop := ∃ (tag k : string) (c v' : val), v = (#tag, (c, (#"WrPost", (#k, v'))))%V.

Definition is_cm_pre_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"CmPre"))%V.

Definition is_cm_post_event (v : val) : Prop := ∃ (tag : string) (c : val) (b : bool), v = (#tag, (c, (#"CmPost", #b)))%V.

Definition is_pre_event (v : val) : Prop := 
  is_st_pre_event v ∨ is_rd_pre_event v ∨ is_wr_pre_event v ∨ is_cm_pre_event v ∨ is_init_pre_event v.

Definition is_post_event (v : val) : Prop := 
  is_st_post_event v ∨ is_rd_post_event v ∨ is_wr_post_event v ∨ is_cm_post_event v ∨ is_init_post_event v.

Definition is_st_lin_event (v : val) : Prop := ∃ (tag : string) (c : val), v = (#tag, (c, #"StLin"))%V.

Definition is_rd_lin_event (v : val) : Prop := 
  (∃ (tag k : string) (c v' : val), v = (#tag, (c, (#"RdLin", (#k, SOMEV v'))))%V) ∨ 
  (∃ (tag k : string) (c : val), v = (#tag, (c, (#"RdLin", (#k, NONEV))))%V).

Definition is_wr_lin_event (v : val) : Prop := ∃ (tag k : string) (c v' : val), v = (#tag, (c, (#"WrLin", (#k, v'))))%V.

Definition is_cm_lin_event (v : val) : Prop := ∃ (tag : string) (c : val) (b : bool), v = (#tag, (c, (#"CmLin", #b)))%V.

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

Definition based_on (exec : execution) (T : list transaction) : Prop :=
  ∀ t, (t ∈ (split exec).1 ∧ t ≠ []) ↔ t ∈ T.

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

(** Helper lemmas  *)

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

Lemma exists_execution : 
  ∀ T, (∀ t, t ∈ T → t ≠ []) → 
    ∃ E, based_on E (comTrans T) ∧ valid_execution commit_test_ru E.
Proof.
  intros T Himp.
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
      * split; set_solver.
  - assert (∀ t : list operation, t ∈ T → t ≠ []) as Himp'.
    {
      intros t' Hin.
      apply Himp.
      set_solver.
    }
    destruct (IH Himp') as [E (Hbased & Hexec)].
    simpl.
    assert (∃ E0 : execution, based_on E0 (comTrans T) ∧ valid_execution commit_test_ru E0) as Hcase; first by exists E.
    destruct (last t); try done.
    destruct o; try done.
    destruct b; try done.
    destruct (last E) as [p|] eqn:Heq.
    + exists (E ++ [(t, applyTransaction p.2 t)]).
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
           ++ assert ((t, applyTransaction p.2 t).1 = t) as <-; first set_solver.
              split.
              ** rewrite elem_of_list_In.
                 apply in_split_l.
                 simpl.
                 rewrite -elem_of_list_In.
                 set_solver.
              ** simpl.
                 apply Himp.
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
              assert (length (E ++ [(t, applyTransaction p.2 t)]) = i + 2) as Hlength'.
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
        -- destruct Hexec as (_ & Hexec & _).
           split.
           ++ rewrite lookup_app_Some.
              by left.
           ++ intros.
              by rewrite /commit_test_ru.
    + exfalso.
      rewrite /valid_execution in Hexec.
      destruct Hexec as (_ & (Hfalse & _)).
      rewrite last_None in Heq; subst.
      set_solver.
Qed.

Lemma pre_post_false :
  ∀ e, is_pre_event e → ¬ is_post_event e.
Proof.
  intros e H Hfalse.
  destruct H as [[tag [c ->]] | H].
  {
    destruct Hfalse as [Hfalse | Hfalse].
    - rewrite /is_st_post_event in Hfalse.
      set_solver.
    - destruct Hfalse as [Hfalse | Hfalse].
      + rewrite /is_rd_post_event in Hfalse.
        set_solver.
      + destruct Hfalse as [Hfalse | Hfalse].
        * rewrite /is_wr_post_event in Hfalse.
          set_solver.
        * destruct Hfalse as [Hfalse | Hfalse].
          -- rewrite /is_cm_post_event in Hfalse.
            set_solver.
          -- rewrite /is_init_post_event in Hfalse.
            set_solver.
  }
  destruct H as [[tag [c ->]] | H].
  {
    destruct Hfalse as [Hfalse | Hfalse].
    - rewrite /is_st_post_event in Hfalse.
      set_solver.
    - destruct Hfalse as [Hfalse | Hfalse].
      + rewrite /is_rd_post_event in Hfalse.
        set_solver.
      + destruct Hfalse as [Hfalse | Hfalse].
        * rewrite /is_wr_post_event in Hfalse.
          set_solver.
        * destruct Hfalse as [Hfalse | Hfalse].
          -- rewrite /is_cm_post_event in Hfalse.
            set_solver.
          -- rewrite /is_init_post_event in Hfalse.
            set_solver.
  }
  destruct H as [[tag [c [k [v ->]]]]| H].
  {
    destruct Hfalse as [Hfalse | Hfalse].
    - rewrite /is_st_post_event in Hfalse.
      set_solver.
    - destruct Hfalse as [Hfalse | Hfalse].
      + rewrite /is_rd_post_event in Hfalse.
        set_solver.
      + destruct Hfalse as [Hfalse | Hfalse].
        * rewrite /is_wr_post_event in Hfalse.
          set_solver.
        * destruct Hfalse as [Hfalse | Hfalse].
          -- rewrite /is_cm_post_event in Hfalse.
            set_solver.
          -- rewrite /is_init_post_event in Hfalse.
            set_solver.
  }
  destruct H as [[tag [c ->]] | [tag ->]].
  {
    destruct Hfalse as [Hfalse | Hfalse].
    - rewrite /is_st_post_event in Hfalse.
      set_solver.
    - destruct Hfalse as [Hfalse | Hfalse].
      + rewrite /is_rd_post_event in Hfalse.
        set_solver.
      + destruct Hfalse as [Hfalse | Hfalse].
        * rewrite /is_wr_post_event in Hfalse.
          set_solver.
        * destruct Hfalse as [Hfalse | Hfalse].
          -- rewrite /is_cm_post_event in Hfalse.
            set_solver.
          -- rewrite /is_init_post_event in Hfalse.
            set_solver.
  }
  destruct Hfalse as [Hfalse | Hfalse].
  - rewrite /is_st_post_event in Hfalse.
    set_solver.
  - destruct Hfalse as [Hfalse | Hfalse].
    + rewrite /is_rd_post_event in Hfalse.
      set_solver.
    + destruct Hfalse as [Hfalse | Hfalse].
      * rewrite /is_wr_post_event in Hfalse.
        set_solver.
      * destruct Hfalse as [Hfalse | Hfalse].
        -- rewrite /is_cm_post_event in Hfalse.
           set_solver.
        -- rewrite /is_init_post_event in Hfalse.
           set_solver.
Qed.

Lemma tags_in : 
  ∀ e t tag, e ∈ t → tagOfEvent e = Some tag → tag ∈ tags t.
Proof.
  intros e t tag Hin Htag.
  induction t as [|h t IH].
  - inversion Hin.
  - rewrite /tagOfEvent in Htag.
    destruct e; try inversion Htag.
    destruct e1; try inversion Htag.
    destruct l; try inversion Htag.
    subst.
    rewrite elem_of_cons in Hin.
    destruct Hin as [<- | Hin];  first set_solver.
    assert (tag ∈ tags t); set_solver.
Qed.

Lemma post_lin_lin_post le e :
  (is_st_post_event e ∨ is_rd_post_event e ∨ is_wr_post_event e ∨ is_cm_post_event e) →
  (postToLin e = Some le → linToPost le = Some e).
Proof.
  intros Hevent Hpost_lin.
  destruct Hevent as [Hevent | [[Hevent | Hevent] | [Hevent | Hevent]]].
  - destruct Hevent as [tag [c ->]].
    simpl in Hpost_lin.
    assert (le = (#tag, (c, #"StLin"))%V) as ->; first set_solver.
    by simpl.
  - destruct Hevent as [tag [k [c [v ->]]]].
    simpl in Hpost_lin.
    assert (le = (#tag, (c, (#"RdLin", (#k, InjRV v))))%V) as ->; first set_solver.
    by simpl.
  - destruct Hevent as [tag [k [c ->]]].
    simpl in Hpost_lin.
    assert (le = (#tag, (c, (#"RdLin", (#k, InjLV #()))))%V) as ->; first set_solver.
    by simpl.
  - destruct Hevent as [tag [k [c [v ->]]]].
    simpl in Hpost_lin.
    assert (le = (#tag, (c, (#"WrLin", (#k, v))))%V) as ->; first set_solver.
    by simpl.
  - destruct Hevent as [tag [c [b ->]]].
    simpl in Hpost_lin.
    assert (le = (#tag, (c, (#"CmLin", #b)))%V) as ->; first set_solver.
    by simpl.
Qed.

Lemma lin_trace_valid : 
  ∀ (tag : string) (e : val) (t lt : list val), 
    ((is_pre_event e ∧ tagOfEvent e = Some tag ∧ tag ∉ tags t) ∨ 
      is_init_post_event e ∨
      ((is_st_post_event e ∨ is_wr_post_event e ∨ is_rd_post_event e ∨ 
        is_cm_post_event e) ∧ (∃ le, postToLin e = Some le ∧ le ∈ lt))) → 
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
    destruct His_pre_post as [(His_pre & _ & _) | [His_init_post | His_post]].
    + exfalso.
      destruct His_pre as [[tag' [c' ->]]| His_pre].
      1 : simpl in Hpost_lin; destruct tag'; done.
      destruct His_pre as [[tag' [c' ->]]| His_pre].
      1 : simpl in Hpost_lin; destruct tag'; done.
      destruct His_pre as [[tag' [c' [k' [v' ->]]]]| His_pre].
      1 : by simpl in Hpost_lin.
      destruct His_pre as [[tag' [c' ->]]| [tag' ->]].
      all : simpl in Hpost_lin; destruct tag'; done.
    + exfalso.
      destruct His_init_post as [tag' [c ->]].
      simpl in Hpost_lin.
      destruct tag'; done.
    + destruct His_post as (le' & Hpost_lin' & Hin').
      set_solver.
  - split.
    + intros le Hin.
      destruct (H1 le Hin) as [e_pre (Hpre & HlinPre & Hin' & Himp)].
      exists e_pre.
      do 2 (split; first done).
      split; first set_solver.
      intros e_post Hassump.
      destruct His_pre_post as [(His_pre & _ & _) | [His_post | His_post]].
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
      * apply Himp.
        destruct Hassump as (Hassump1 & Hassump2).
        split; last done.
        rewrite elem_of_app in Hassump1.
        destruct Hassump1 as [Hassump1 | Hassump1]; first done.
        assert (e_post = e) as ->; first set_solver.
        exfalso.
        destruct His_post as [tag' [c ->]].
        destruct Hassump2 as (_ & Hassump2).
        simpl in Hassump2.
        inversion Hassump2.
        subst.
        specialize (H le Hin).
        destruct H as [H | H].
        -- destruct H as [tag'' [c' ->]].
           simpl in HlinPre.
           by destruct tag'.
        -- destruct H as [H | H].
           ++ destruct H as [H | H].
              ** destruct H as [tag'' [c' [k' [v' ->]]]].
                 by simpl in HlinPre.
              ** destruct H as [tag'' [c' [k' ->]]].
                 by simpl in HlinPre.
           ++ destruct H as [H | H].
              ** destruct H as [tag'' [c' [k' [v' ->]]]].
                 by simpl in HlinPre.
              ** destruct H as [tag'' [c' [b' ->]]].
                 by simpl in HlinPre.
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
        destruct His_post as [His_post | [His_post | [[His_post | His_post] | His_post]]].
        -- pose proof Hlin_post as Hlin_post'. 
           apply post_lin_lin_post in Hlin_post.
           ++ destruct His_post as [tag' [c' ->]]. 
              assert (tagOfEvent le' = Some tag') as Htag_of1.
              {
                simpl in Hlin_post'.
                injection Hlin_post' as <-.
                by simpl.
              }
              simpl in Hassump2'.
              assert (e_pre = (#tag', (c', #"StPre"))%V) as ->; first set_solver.
              assert (tagOfEvent le = Some tag') as Htag_of2.
              {
                destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
                  [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | [tag'' [c'' [b'' ->]]]]]].
                all : simpl in HlinPre.
                all : assert (tag'' = tag') as ->; first set_solver.
                all : by simpl.
              }
              assert (le = le') as ->; last done.
              assert (i = j) as ->; last set_solver.
              apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
           ++ by left.
        -- pose proof Hlin_post as Hlin_post'. 
           apply post_lin_lin_post in Hlin_post.
           ++ destruct His_post as [tag' [c' [k' [v' ->]]]]. 
              assert (tagOfEvent le' = Some tag') as Htag_of1.
              {
                simpl in Hlin_post'.
                injection Hlin_post' as <-.
                by simpl.
              }
              simpl in Hassump2'.
              assert (e_pre = (#tag', (k', (#"WrPre", (#c', v'))))%V) as ->; first set_solver.
              assert (tagOfEvent le = Some tag') as Htag_of2.
              {
                destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
                  [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | [tag'' [c'' [b'' ->]]]]]].
                all : simpl in HlinPre.
                all : assert (tag'' = tag') as ->; first set_solver.
                all : by simpl.
              }
              assert (le = le') as ->; last done.
              assert (i = j) as ->; last set_solver.
              apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
           ++ do 2 right.
              by left.
        -- pose proof Hlin_post as Hlin_post'. 
           apply post_lin_lin_post in Hlin_post.
           ++ destruct His_post as [tag' [k' [c' [v' ->]]]]. 
              assert (tagOfEvent le' = Some tag') as Htag_of1.
              {
                simpl in Hlin_post'.
                injection Hlin_post' as <-.
                by simpl.
              }
              simpl in Hassump2'.
              assert (e_pre = (#tag', (c', #"RdPre"))%V) as ->; first set_solver.
              assert (tagOfEvent le = Some tag') as Htag_of2.
              {
                destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
                  [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | [tag'' [c'' [b'' ->]]]]]].
                all : simpl in HlinPre.
                all : assert (tag'' = tag') as ->; first set_solver.
                all : by simpl.
              }
              assert (le = le') as ->; last done.
              assert (i = j) as ->; last set_solver.
              apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
           ++ right. 
              by do 2 left.
        -- pose proof Hlin_post as Hlin_post'.
           apply post_lin_lin_post in Hlin_post.
           ++ destruct His_post as [tag' [k' [c' ->]]]. 
              assert (tagOfEvent le' = Some tag') as Htag_of1.
              {
                simpl in Hlin_post'.
                injection Hlin_post' as <-.
                by simpl.
              }
              simpl in Hassump2'.
              assert (e_pre = (#tag', (c', #"RdPre"))%V) as ->; first set_solver.
              assert (tagOfEvent le = Some tag') as Htag_of2.
              {
                destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
                  [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | [tag'' [c'' [b'' ->]]]]]].
                all : simpl in HlinPre.
                all : assert (tag'' = tag') as ->; first set_solver.
                all : by simpl.
              }
              assert (le = le') as ->; last done.
              assert (i = j) as ->; last set_solver.
              apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
           ++ right.
              left.
              by right.
        -- pose proof Hlin_post as Hlin_post'.
           apply post_lin_lin_post in Hlin_post.
           ++ destruct His_post as [tag' [c' [b' ->]]]. 
              assert (tagOfEvent le' = Some tag') as Htag_of1.
              {
                simpl in Hlin_post'.
                injection Hlin_post' as <-.
                by simpl.
              }
              simpl in Hassump2'.
              assert (e_pre = (#tag', (c', #"CmPre"))%V) as ->; first set_solver.
              assert (tagOfEvent le = Some tag') as Htag_of2.
              {
                destruct (H le Hin_le) as [[tag'' [c'' ->]] | [[[tag'' [c'' [k'' [v'' ->]]]] | 
                  [tag'' [k'' [c'' ->]]]] | [[tag'' [c'' [k'' [v'' ->]]]] | [tag'' [c'' [b'' ->]]]]]].
                all : simpl in HlinPre.
                all : assert (tag'' = tag') as ->; first set_solver.
                all : by simpl.
              }
              assert (le = le') as ->; last done.
              assert (i = j) as ->; last set_solver.
              apply (H3 le le' i j tag' Hlookup_i Hlookup_j Htag_of2 Htag_of1).
           ++ by do 3 right.
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
              destruct Hle1_lin as [Hle1_lin | Hle1_lin].
              ** destruct Hle1_lin as [tag' [c' ->]].
                  destruct Hfalse as [Hfalse | ([Hfalse | [Hfalse | [Hfalse | Hfalse]]] & _)].
                  all : inversion Hfalse; set_solver.
              ** destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                  --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                      +++ destruct Hle1_lin as [tag' [c' [k' [v' ->]]]].
                          simpl in Hlinpre.
                          destruct Hfalse as [Hfalse | ([Hfalse | [Hfalse | [Hfalse | Hfalse]]] & _)].
                          all : inversion Hfalse; set_solver.
                      +++ destruct Hle1_lin as [tag' [c' [k' ->]]].
                          simpl in Hlinpre.
                          destruct Hfalse as [Hfalse | ([Hfalse | [Hfalse | [Hfalse | Hfalse]]] & _)].
                          all : inversion Hfalse; set_solver.
                  --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                      +++ destruct Hle1_lin as [tag' [c' [k' [v' ->]]]].
                          simpl in Hlinpre.
                          destruct Hfalse as [Hfalse | ([Hfalse | [Hfalse | [Hfalse | Hfalse]]] & _)].
                          all : inversion Hfalse; set_solver.
                      +++ destruct Hle1_lin as [tag' [c' [b' ->]]].
                          simpl in Hlinpre.
                          destruct Hfalse as [Hfalse | ([Hfalse | [Hfalse | [Hfalse | Hfalse]]] & _)].
                          all : inversion Hfalse; set_solver.
      * subst.
        exfalso.
        assert (e1_pre = e2_post) as ->.
        {
          rewrite lookup_snoc_Some in Hlookup_pre.
          destruct Hlookup_pre as [(Hfalse & _ ) | (_ & Hgoal)]; last done.
          lia.
        }
        destruct Hle2_lin as [Hle2_lin | Hle2_lin].
        -- destruct Hle2_lin as [tag' [c' ->]].
           simpl in Hlinpost.
           inversion Hlinpost; subst.
           destruct Hle1_lin as [Hle1_lin | Hle1_lin].
           ** destruct Hle1_lin as [tag'' [c'' ->]].
              simpl in Hlinpre.
              destruct tag''; try done.
           ** destruct Hle1_lin as [Hle1_lin | Hle1_lin].
              --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                  +++ destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                      by simpl in Hlinpost.
                  +++ destruct Hle1_lin as [tag'' [c'' [k'' ->]]].
                      by simpl in Hlinpost.
              --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                  +++ destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                      by simpl in Hlinpost.
                  +++ destruct Hle1_lin as [tag'' [c'' [b'' ->]]].
                      by simpl in Hlinpost.
        -- destruct Hle2_lin as [Hle2_lin | Hle2_lin].
           ++ destruct Hle2_lin as [Hle2_lin | Hle2_lin].
              ** destruct Hle2_lin as [tag' [c' [k' [v' ->]]]].
                 simpl in Hlinpost.
                 inversion Hlinpost; subst.
                 destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                 --- destruct Hle1_lin as [tag'' [c'' ->]].
                     simpl in Hlinpre.
                     destruct tag''; try done.
                 --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [k'' ->]]].
                             by simpl in Hlinpost.
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [b'' ->]]].
                             by simpl in Hlinpost.
              ** destruct Hle2_lin as [tag' [c' [k' ->]]]. 
                 simpl in Hlinpost.
                 inversion Hlinpost; subst.
                 destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                 --- destruct Hle1_lin as [tag'' [c'' ->]].
                     by simpl in Hlinpre.
                 --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [k'' ->]]].
                             by simpl in Hlinpost.
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [b'' ->]]].
                             by simpl in Hlinpost.
           ++ destruct Hle2_lin as [Hle2_lin | Hle2_lin].
              ** destruct Hle2_lin as [tag' [c' [k' [v' ->]]]].
                 simpl in Hlinpost.
                 inversion Hlinpost; subst.
                 destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                 --- destruct Hle1_lin as [tag'' [c'' ->]].
                     by simpl in Hlinpre.
                 --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [k'' ->]]].
                             by simpl in Hlinpost.
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [b'' ->]]].
                             by simpl in Hlinpost.
              ** destruct Hle2_lin as [tag' [c' [b' ->]]].
                 simpl in Hlinpost.
                 inversion Hlinpost; subst.
                 destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                 --- destruct Hle1_lin as [tag'' [c'' ->]].
                     by simpl in Hlinpre.
                 --- destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [k'' ->]]].
                             by simpl in Hlinpost.
                     +++ destruct Hle1_lin as [Hle1_lin | Hle1_lin].
                         *** destruct Hle1_lin as [tag'' [c'' [k'' [v'' ->]]]].
                             by simpl in Hlinpost.
                         *** destruct Hle1_lin as [tag'' [c'' [b'' ->]]].
                             by simpl in Hlinpost.
Qed.

Lemma valid_sequence_st_lin lt tag c : 
  valid_sequence lt → valid_sequence (lt ++ [(#tag, (c, #"StLin"))%V]).
Proof.
  intro Hvalid_seq.
  rewrite /valid_sequence.
  split.
  - intros e c_e He_in He_conn He_event.
    rewrite elem_of_app in He_in.
    destruct He_in as [He_in | He_in].
    + destruct Hvalid_seq as (Hvalid_seq & _).
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
            destruct Hlookup_i as [Hlookup_i | (Hlenght & Hlookup_i)].
            ++ split; first done.
              rewrite lookup_app_Some in Hlookup_j.
              destruct Hlookup_j as [Hlookup_j | (Hlenght & Hlookup_j)]; first done.
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
            destruct Hlookup_i as [Hlookup_i | (Hlenght & Hlookup_i)].
            ++ split; first done.
              rewrite lookup_app_Some in Hlookup_j.
              destruct Hlookup_j as [Hlookup_j | (Hlenght & Hlookup_j)]; first done.
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
      destruct He_event as [Hfalse | [Hfalse | Hfalse]].
      * destruct Hfalse as [Hfalse | Hfalse]; set_solver.
      * rewrite /is_wr_lin_event in Hfalse; set_solver.
      * rewrite /is_cm_lin_event in Hfalse; set_solver.
  - intros e_st c0 He_in He_conn He_event.
    rewrite elem_of_app in He_in.
    destruct He_in as [He_in | He_in].
    + destruct Hvalid_seq as (_ & Hvalid_seq).
      destruct (Hvalid_seq e_st c0 He_in He_conn He_event) as 
        [Hvalid_seq' | Hvalid_seq'].
      * left.
        destruct Hvalid_seq' as (e_cm & Hcm_conn & Hcm_lin & Hcm_rel & Hcm_not).
        exists e_cm.
        do 2 (split; first done).
        split.
        -- destruct Hcm_rel as (i & j & Hneq & Hlookup_i & Hlookup_j).
            exists i, j.
            split; first done.
            split; by apply lookup_app_l_Some.
        -- intros Hmain.
            apply Hcm_not.
            destruct Hmain as (e_st' & He_st'_conn & He_st'_lin & He_st'_rel1 & He_st'_rel2).
            exists e_st'.
            do 2 (split; first done).
            destruct He_st'_rel1 as (i & j & Hlt & Hlookup_i & Hlookup_j).
            rewrite lookup_app_Some in Hlookup_i.
            rewrite lookup_app_Some in Hlookup_j.
            destruct Hlookup_i as [Hlookup_i |(Hlength & Hlookup_i)].
            ** destruct Hlookup_j as [Hlookup_j |(Hlength & Hlookup_j)].
              --- split; first by exists i, j.
                  destruct He_st'_rel2 as (i' & j' & Hneq' & Hlookup_i' & Hlookup_j').
                  rewrite lookup_app_Some in Hlookup_i'.
                  destruct Hlookup_i' as [Hlookup_i' | (Hlength' & Hlookup_i')].
                  +++ rewrite lookup_app_Some in Hlookup_j'.
                      destruct Hlookup_j' as [Hlookup_j' | (Hlength'' & Hlookup_j')]; 
                        first by exists i', j'.
                      rewrite list_lookup_singleton_Some in Hlookup_j'.
                      destruct Hlookup_j' as (_ & <-).
                      rewrite /is_cm_lin_event in Hcm_lin.
                      set_solver.
                  +++ assert (length (lt ++ [(#tag, (c, #"StLin"))%V]) ≤ j') as Hfalse.
                      {
                        rewrite last_length.
                        lia.
                      }
                      apply lookup_ge_None_2 in Hfalse.
                      set_solver.
              --- destruct He_st'_rel2 as (i' & j' & Hneq' & Hlookup_i' & Hlookup_j').
                  rewrite lookup_app_Some in Hlookup_i'.
                  destruct Hlookup_i' as [Hlookup_i' | (Hlength' & Hlookup_i')].
                  +++ rewrite lookup_app_Some in Hlookup_j'.
                      destruct Hlookup_j' as [Hlookup_j' | (Hlength'' & Hlookup_j')].
                      *** admit.
                      *** rewrite list_lookup_singleton_Some in Hlookup_j'.
                          destruct Hlookup_j' as (_ & <-).
                          rewrite /is_cm_lin_event in Hcm_lin.
                          set_solver.
                  +++ rewrite lookup_app_Some in Hlookup_j'.
                      destruct Hlookup_j' as [Hlookup_j' | (Hlength'' & Hlookup_j')].
                      *** assert (length lt ≤ j') as Hfalse; first lia.
                          apply lookup_ge_None_2 in Hfalse.
                          set_solver.
                      *** rewrite list_lookup_singleton_Some in Hlookup_j'.
                          destruct Hlookup_j' as (_ & <-).
                          rewrite /is_cm_lin_event in Hcm_lin.
                          set_solver.
            ** destruct Hlookup_j as [Hlookup_j |(Hlength' & Hlookup_j)].
              --- assert (length lt ≤ j) as Hfalse; first lia.
                  apply lookup_ge_None_2 in Hfalse.
                  set_solver.
              --- rewrite list_lookup_singleton_Some in Hlookup_j.
                  destruct Hlookup_j as (Hfalse & _); lia.
      * right.
        intros Hmain.
        apply Hvalid_seq'.
        destruct Hmain as (e & He_conn' & He_rel' & He_lin').
        exists e.
        split; first done.
        split; last done.
        admit.
    + assert (e_st = (#tag, (c, #"StLin"))%V) as ->; first set_solver.
      right.
      intro Hfalse.
      destruct Hfalse as (e & _ & (i & j & Hneq & Hlookup_i & Hlookup_j) & _).
      rewrite lookup_app_Some in Hlookup_i.
      destruct Hlookup_i as [Hfalse |(Hlength & Hlookup_i)].
      * admit.
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
Admitted.

Lemma lin_trace_start_lin lt (tag : string) c t :
  lin_trace_of lt t →
  lin_trace_of (lt ++ [(#tag, (c, #"StLin"))%V]) t.
Proof.
  intros H.
  destruct H as (?&?&?&?&?).
  split.
  {
    intros le Hin.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin | Hin].
    -  by apply H.
    - assert (le = (#tag, (c, #"StLin"))%V) as ->; first set_solver.
      left.
      by exists tag, c.
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
    - admit.
  }
  split.
  { 
    intros le1 le2 Hrel.
    admit.
  }
  intros le1 le2 i j tag' Hlookup_i Hlookup_j Htag_le1 Htag_le2.
  rewrite lookup_app_Some in Hlookup_i.
  rewrite lookup_app_Some in Hlookup_j.
  destruct Hlookup_i as [Hlookup_i | (Hlength_i & Hlookup_i)].
  - destruct Hlookup_j as [Hlookup_j | (Hlength_j & Hlookup_j)].
    + apply (H3 le1 le2 i j tag' Hlookup_i Hlookup_j Htag_le1 Htag_le2).
    + admit.
  - destruct Hlookup_j as [Hlookup_j | (Hlength_j & Hlookup_j)].
    + admit.
    + rewrite list_lookup_singleton_Some in Hlookup_i.
      rewrite list_lookup_singleton_Some in Hlookup_j.
      lia.
Admitted.