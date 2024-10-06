From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness.
From trillium.fairness.lawyer.obligations Require Import obligations_model.


Section Termination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.


  Section NoInfExpects.
    Context (tr: obls_trace OP).
    Context {last_expect: SignalId -> nat}.
    Hypothesis (LAST_EXP_SPEC: 
                 forall sid δ1 δ2 τ k π d,
                   tr !! k = Some (δ1, Some (τ, δ2)) ->
                   expects_ep OP δ1 τ δ2 sid π d -> 
                   k <= last_expect sid).

    Definition PF (i: nat): gmultiset (@CallPermission Degree) :=
      from_option (ps_cps OP) ∅ (tr S!! i) ⊎
      (* ([^op set] ('(s, (π, d)) ∈ (∅: gset ExpectPermission)), ∅).  *)
      ([^op set] ep ∈ (∅: gset (@ExpectPermission Degree)),
        let '(sid, π, d) := ep in 
        (last_expect sid - i) *: {[+ (π, d) +]}
      ).

    (* TODO: move into ObligationsParams *)
    Context (deg_le: relation Degree). 
    Context (DEG_PO: PartialOrder deg_le).

    Definition cp_le: relation (@CallPermission Degree) :=
      (* lexprod *)
      fun '(_, d1) '(_, d2) => deg_le d1 d2.

    (** TODO:
        1) do we need to care about phases?
        2) how to implement comparison of CPs multisets?
     *)
   
  End NoInfExpects.

  Lemma obls_fair_trace_terminate (tr: obls_trace OP):
    obls_trace_valid OP tr ->
    (∀ τ, obls_trace_fair OP τ tr) ->
    terminating_trace tr.
  Proof using.
    
  Admitted. 


End Termination.
