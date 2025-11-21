From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context wptp_gen pwp wfree_traces calls.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em.
From lawyer Require Import program_logic.  
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From heap_lang Require Import sswp_logic lang.


Close Scope Z. 


Section CallTracker.

  Class CallTrackerPre Σ := {
    ct_pre_expr :: inG Σ (excl_authUR (option expr));
  }.

  Class CallTracker Σ := {
    ct_pre :: CallTrackerPre Σ;
    ct_γ: gname;
  }.

  Context `{CallTracker Σ}.

  Definition ct_auth (oe: option expr) := own ct_γ $ ● (Some $ Excl oe).
  Definition ct_frag (oe: option expr) := own ct_γ $ ◯ (Some $ Excl oe).

End CallTracker.


Section PwpExtra.
  Context (LG: LangEM heap_lang).
  Context `{invGS_gen HasNoLc Σ} {lGS: lgem_GS Σ} {ctGS: CallTracker Σ}.

  Context (m: val) (τ: locale heap_lang).

  Definition inside_call (K: ectx heap_lang) (i: nat) (etr: execution_trace heap_lang) (e: expr) :=
    let κ := TpoolCtx K τ in
    let last_ind := trace_length etr - 1 in
    exists (a: val),      
      (exists s, etr !! i = Some s /\ call_at κ s m a (APP := App)) /\
      i < last_ind /\ 
      (** finite_trace_to_trace reverses the trace; use alt def of no_return_before instead *)
      (* no_return_before (finite_trace_to_trace etr) κ i (trace_length etr - 1) /\ *)
      (forall j, i <= j <= last_ind -> from_option (nval_at κ) False (etr !! j)) /\
      from_option (fun eτ => under_ctx K eτ = Some e) False ((trace_last etr).1 !! τ)
  . 

  Context (tok: iProp Σ).

  Definition ct_interp (etr: execution_trace heap_lang): iProp Σ
    (* (oe: option expr) *)
    :=
    ∃ (oe: option expr), ct_auth oe ∗
    (tok ∗ ⌜ oe = None ⌝ ∨ ∃ e K s, ⌜ oe = Some e /\ inside_call K s etr e⌝)
  .

  (* Definition irisG_phys_cti (LG: LangEM heap_lang) `{invGS_gen HasNoLc Σ} {lG: lgem_GS Σ}: *)
  (*   irisG heap_lang LoopingModel Σ := {| *)
  (*     state_interp etr mtr := (phys_SI LG etr mtr (lG := lG) ∗ ct_interp etr)%I; *)
  (*     fork_post := fun _ _ => (⌜ True ⌝)%I; *)
  (* |}. *)
  
End PwpExtra.

(* (* TODO: rename *) *)
(* Definition iris_OM_into_phys_cti {Σ} `(Hinv : @IEMGS heap_lang M LG EM Σ) (CT: CallTracker Σ) *)
(*   (m: val) (τ: locale heap_lang) (tok: iProp Σ) *)
(*   : *)
(*   irisG heap_lang LoopingModel Σ. *)
(* Proof using. *)
(*   eapply (irisG_phys_cti m τ tok); apply Hinv. *)
(* Defined. *)
