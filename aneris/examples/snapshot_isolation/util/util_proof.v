(* From aneris.examples.snapshot_isolation.util Require Import util_code.
From aneris.aneris_lang Require Import tactics adequacy proofmode.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.instantiation
      Require Import snapshot_isolation_api_implementation.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From iris.algebra Require Import gmap.


Section proof.
  
Context `{!anerisG Mdl Σ, !User_params, !KVSG Σ,
                !SI_resources Mdl Σ}.

  Lemma commitU_spec :
    ∀ c sa E,
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    commit_spec -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
        ConnectionState c (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, k ↦ₖ h) ∗
        ([∗ map] k ↦ p ∈ mc, k ↦{c} p.1  ∗ KeyUpdStatus c k p.2) >>>
      commitU c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState c CanStart ∗
        (** Transaction has been commited. *)
        ((⌜can_commit m ms mc⌝ ∗
         ∃ (t: Time), ⌜max_timestamp t m⌝ ∗
          ([∗ map] k↦ eo;p ∈ m; mc, k ↦ₖ commit_event k t p eo)) ∨
        (** Transaction has been aborted. *)
         (⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ eo ∈ m, k ↦ₖ eo)) >>>.
  Proof.

  Qed.


End proof.





 *)
