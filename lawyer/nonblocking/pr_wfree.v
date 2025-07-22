From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From trillium.program_logic Require Import execution_model weakestpre adequacy simulation_adequacy_em_cond. 
From trillium.prelude Require Import classical.
From fairness Require Import fairness.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination.
From heap_lang Require Import lang.
From lawyer.nonblocking Require Import trace_context.

Definition LoopingModel: Model :=
  {| mstate := unit; mlabel := unit; mtrans := fun _ _ _ => True |}.

(* Class LoopIrisG {Λ: language} Σ := { *)
(*     lig_inner :: irisG Λ LoopingModel Σ *)
(* }. *)


  (* Program Definition WptpPR {Σ} {Hinv : @IEMGS _ _ LG_EM EM Σ} *)
  (*   (iG := IEM_irisG LG_EM EM) *)
  (*   : ProgressResource state_interp (fun _ _ => ⌜ True ⌝%I) fork_post C := *)
  (*   {| pr_pr := (fun s etr Φs => wptp s (trace_last etr).1 Φs) |}.  *)
  (* Next Obligation.  *)
  (*   intros. apply wptp_of_val_post. *)
  (* Qed. *)
  (* Next Obligation.  *)
  (*   clear R FILTER_PCL C_DEC. *)
  (*   intros. rewrite H0. *)
  (*   iIntros "? WPS". *)
  (*   iMod (wptp_not_stuck_same _ _ _ _ [] with "[$] [WPS]") as "(?&?&%NS)".  *)
  (*   3: by iFrame. *)
  (*   { eauto. } *)
  (*   { erewrite app_nil_l, app_nil_r. *)
  (*     erewrite <- surjective_pairing. apply trace_ends_in_last. } *)
  (*   iModIntro. iFrame. *)
  (*   iPureIntro. intros. subst. rewrite -H0. *)
  (*   eapply NS; eauto. *)
  (*   apply last_eq_trace_ends_in in H0. rewrite H0. simpl. set_solver. *)
  (* Qed. *)
  (* Final Obligation.  *)
  (*   intros. *)
  (*   iIntros "?? _ ? _". (** for usual wptp with the same TI, trivial trace invariant and any trace condition don't matter *) *)
  (*   iMod (take_step with "[$] [$] [$]") as "X". *)
  (*   1, 2: by eauto. *)
  (*   { by rewrite H0. } *)
  (*   iModIntro. iApply (step_fupdN_mono with "[$]"). *)
  (*   iIntros "X". iMod "X" as "(?&?)". iModIntro. iFrame.  *)
  (*   setoid_rewrite bi.True_sep'. by rewrite H0. *)
  (* Qed. *)

