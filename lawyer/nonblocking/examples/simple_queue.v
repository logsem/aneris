From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Close Scope Z.


Section MaxExact.
  Context {Σ: gFunctors}.
  Context (γ: gname). 

  Definition me_auth (n: nat): iProp Σ. Admitted. 
  Definition me_exact (n: nat): iProp Σ. Admitted. 
  Definition me_lb (n: nat): iProp Σ. Admitted. 

End MaxExact. 


Class QueueG := {
    Head: loc; Tail: loc; BeingRead: loc; 
    FreeLater: loc; OldHeadVal: loc;
    γHead: gname; γTail: gname; γBeingRead: gname; 
    γFreeLater: gname; γOldHeadVal: gname;

    γHob: gname;
}.


Section SimpleQueue.

  Definition loc_head: val := λ: "q", Fst "q".
  Definition loc_tail: val := λ: "q", Fst $ Snd "q".
  Definition loc_BR: val := λ: "q", Fst $ Snd $ Snd "q".
  Definition loc_FL: val := λ: "q", Fst $ Snd $ Snd $ Snd "q".
  Definition loc_OHV: val := λ: "q", Snd $ Snd $ Snd $ Snd "q".

  Definition get_val: val := λ: "nd", ! (Fst "nd").
  Definition get_next: val := λ: "nd", ! (Snd "nd").

  Definition free_el: val. Admitted.

  Definition dequeue: val :=
    λ: "q",
      let: "c" := ! (loc_head "q") in
      if: ("c" = ! (loc_tail "q"))
        then NONE
        else
          let: "v" := get_val "c" in
          (loc_OHV "q") <- "v" ;;
          let: "to_free" :=
            if: ("c" = ! (loc_BR "q"))
            then
              let: "old_br" := ! (loc_FL "q") in
              (loc_FL "q") <- "c" ;;
              "old_vr"
            else "c"
          in free_el "to_free" ;;
          (SOME "v")
  .

  Definition Node: Set := val * loc. 
  Definition HistQueue: Set := list (loc * Node).

  Context (QL: QueueG).  
  (* Let H := Head. QL. *)
  (* Let T := Tail QL. *)
  (* Let BR := BeingRead QL. *)
  (* Let FL := FreeLater QL. *)
  (* Let OHV := OldHeadVal QL. *)

  Section QueueResources. 

    Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.
  
    Definition queue_interp (hq: HistQueue) (h t br fl: nat): iProp Σ.
    Admitted.
  
    Definition dangle (od: option loc): iProp Σ. Admitted.
  
    Definition auths (h t br fl hob: nat): iProp Σ :=
      me_exact γHead h ∗ me_exact γTail t ∗ me_exact γBeingRead br ∗
      me_exact γFreeLater fl ∗ me_exact γHob hob.
  
    Definition safe_BR (h br fl hob: nat) (od: option loc): Prop :=
      br = h \/ (* reading the current queue head *)
      br = h - 1 /\ is_Some od \/ (* reading the dangling head *)
      br <= h - 1 /\ ( (* read of some old node that: *)
        fl = br \/ (* is protected by FreeLater *)
        hob > br (* won't actually be read, since a newer head has   been observed *)
      ).
  
    Definition read_head_resources (t br hob: nat): iProp Σ :=
      me_exact γTail t ∗ me_exact γBeingRead br ∗ me_exact γHob hob. 
  
    Definition dequeue_resources (h fl: nat): iProp Σ :=
      me_exact γHead h ∗ me_exact γFreeLater fl.
  
    Definition read_head_token: iProp Σ. Admitted. 
    Definition dequeue_token: iProp Σ. Admitted. 
  
    Definition queue_inv_inner (hq: HistQueue) (h t br fl hob: nat)
      (od: option loc) (ohv: val): iProp Σ :=
      queue_interp hq h t br fl ∗ dangle od ∗ OldHeadVal ↦ ohv ∗
      ⌜ fl <= br <= hob /\ hob <= h /\ (fl < h) ⌝ ∗
      auths h t br fl hob ∗
      ⌜ safe_BR h br fl hob od ⌝ ∗
      (read_head_resources t br hob ∨ read_head_token) ∗ 
      (dequeue_resources h fl ∨ dequeue_token)
    .
  
    Definition queue_ns := nroot .@ "queue".

    (* Definition queue_at (q: loc): iProp Σ := *)
      (* pointsto q DfracDiscarded (#Head, #Tail, #BeingRead, #FreeLater, #OldHeadVal)%V.  *)
    Definition queue_at (q: val): iProp Σ :=
      ⌜ q = (#Head, (#Tail, (#BeingRead, (#FreeLater, #OldHeadVal))))%V ⌝. 
  
    (* Definition queue_inv (q: loc): iProp Σ := *)
    Definition queue_inv (q: val): iProp Σ :=
      queue_at q ∗ inv queue_ns 
        (∃ hq h t br fl hob od ohv, queue_inv_inner hq h t br fl hob   od ohv)
    .
  
  End QueueResources.


  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.
  (* Existing Instance OHE.  *)

  Context (d: Degree).

  Definition get_loc_fuel := 5. 

  Lemma get_head_spec l τ π q:
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_at l) ∗
        th_phase_frag τ π q ∗ cp_mul π d get_loc_fuel }}}
      loc_head l @ τ
    {{{ RET #Head; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "(#QAT & PH & CPS) POST". rewrite /loc_head.
    rewrite /queue_at. iDestruct "QAT" as %->.
    pure_steps. by iApply "POST".
  Qed.    

  Lemma dequeue_spec l (τ: locale heap_lang) (π: Phase) (q: Qp):
    {{{ (let _: heap1GS Σ := iem_phys _ EM in queue_inv l) ∗
        (let _: heap1GS Σ := iem_phys _ EM in dequeue_token) ∗ 
          th_phase_frag τ π q ∗ cp_mul π d 50 }}}
      dequeue l @ τ
    {{{ v, RET #v; th_phase_frag τ π q }}}.
  Proof using.
    simpl. iIntros (Φ) "([#QAT #INV] & TOK & PH & CPS) POST". rewrite /dequeue.
    pure_steps.

    split_cps "CPS" get_loc_fuel.
    { cbv. lia. } 
    iApply (get_head_spec with "[$QAT $CPS' $PH]").
    iIntros "!> PH".

    
End SimpleQueue.
