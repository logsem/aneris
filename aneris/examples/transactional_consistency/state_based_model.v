From iris.algebra Require Import gmap gset list.
From aneris.examples.transactional_consistency Require Import user_params.
From stdpp Require Import strings.
From aneris.aneris_lang Require Import network resources.

(* The string argument below is an identifier *)
Inductive operation : Type :=
  | Rd (s : string) (k : Key) (ov : option val) : operation 
  | Wr (s : string) (k : Key) (v : val) : operation
  | Cm (s : string) (b : bool) : operation.

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

Definition execution : Type := list ((gmap Key val) * transaction).

Definition valid_execution (exec : execution): Prop := true.

Definition commitTest : Type := execution -> transaction -> bool.

Definition executionTest : Type := execution -> list transaction -> bool.

Definition executionTestGen (test : commitTest) : executionTest := 
  λ (exec : execution) (transactions : list transaction), forallb (test exec) transactions.

(** Read Uncommitted  *)

Definition commitTestRU : commitTest := 
  λ exec trans, true.

Definition executionTestRU : executionTest := 
  λ exec transactions, executionTestGen commitTestRU exec transactions.

(** Read Committed  *)

Fixpoint cut_inner {A : Type} (l acc : list A) (test : A → bool) : list A := 
  match l with 
  | h :: t => if test h then (app acc [h]) else cut_inner t (app acc [h]) test
  | [] => acc
  end.

Definition cut {A : Type} (l : list A) (test : A → bool) : list A := cut_inner l [] test.

Definition transIdEquiv (s : string) (trans : transaction) : bool := 
  match head trans with 
  | Some op => 
    match op with 
    | Rd s' _ _ => bool_decide (s = s')
    | Wr s' _ _ => bool_decide (s = s')
    | Cm s' _ => bool_decide (s = s')
    end
  | None => false
  end. 

Definition readStates (s : string) (k : Key) (ov : option val) 
(exec : execution) : list ((gmap Key val) * transaction) := 
  let priorStates := cut exec (λ e, let (_, trans) := e in transIdEquiv s trans) in 
  filter (λ (e : (gmap Key val) * transaction), let (map, _) := e in map !! k = ov) priorStates. 

Definition preRead (trans : transaction) (exec : execution): bool :=
  forallb 
    (λ (op : operation), match op with 
                          | Rd s k ov => bool_decide (readStates s k ov exec ≠ []) 
                          | _ => true 
                         end) 
    trans.

Definition commitTestRC : commitTest := 
  λ exec trans, preRead trans exec.

Definition executionTestRC : executionTest := 
  λ exec transactions, executionTestGen commitTestRC exec transactions.
  
(** Snapshot Isolation *)

(* Definition complete (state : (gmap Key val) * transaction) (trans : transaction) 
(exec : execution) : bool := 
  forallb 
    (λ (op : operation), match op with 
                          | Rd s k ov => bool_decide (In state (readStates s k ov exec)) 
                          | _ => true 
                        end) 
    trans. 

Definition commitTestSI : commitTest := 
  λ exec trans, 
    existsb (λ e, let (map, _) := e in 
                    complete e trans exec  && 
                    true) 
            exec.

Definition executionTestSI : executionTest := 
  λ exec transactions, executionTestGen commitTestSI exec transactions. *)

(** Embedding of into the trace infrastructure  *)

Definition valid_ru (t : list val): Prop := true.

Definition valid_rc (t : list val): Prop := true.

Definition valid_si (t : list val): Prop := true.