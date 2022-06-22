From stdpp Require Import list.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Export db_params time events.

Section Predicates.
  Context `{!anerisG Mdl Σ, !DB_time, !DB_params}.
  Reserved Notation "k ↦ₖ{ q } v" (at level 20).
  Reserved Notation "k ↦ₖ v" (at level 20).

  Class DB_resources := {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInvPersistent :> Persistent GlobalInv;

    (** Logical points-to connective *)
    OwnMemKey : Key → frac → option we → iProp Σ
    where "k ↦ₖ{ q } v" := (OwnMemKey k q v)
    and "k ↦ₖ v" := (OwnMemKey k 1 v);

    (** Observed requests *)
    Obs : socket_address → ghst → iProp Σ;

    (** Properties of points-to connective *)
    OwnMemKey_timeless k q v :> Timeless (k ↦ₖ{ q } v);
    OwnMemKey_exclusive k q v v' :
      k ↦ₖ{ 1 } v ⊢ k ↦ₖ{ q } v' -∗ False;
    OwnMemKey_fractioal k v :>
      Fractional (λ q, k ↦ₖ{ q } v);
    OwnMemKey_as_fractioal k q v :>
      AsFractional (k ↦ₖ{ q } v) (λ q, k ↦ₖ{ q } v) q ;
    OwnMemKey_combine k q q' v v' :
      k ↦ₖ{ q } v ∗ k ↦ₖ{ q' } v' ⊢
      k ↦ₖ{ q + q'} v ∗ ⌜v = v'⌝ ;
    OwnMemKey_split k q1 q2 v :
      k ↦ₖ{ q1 + q2 } v ⊢ k ↦ₖ{ q1 } v ∗ k ↦ₖ{ q2 } v ;
    OwnMemKey_key k q we E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢
      k ↦ₖ{q} Some we ={E}=∗
      k ↦ₖ{q} Some we ∗ ⌜we_key we = k⌝;

    (** Properties of observed requests *)
    Obs_timeless a h :> Timeless (Obs a h);
    Obs_persistent a h :> Persistent (Obs a h);
    Obs_compare a a' h h' :
      Obs a h -∗ Obs a' h' -∗
      ⌜h ≤ₚ h'⌝ ∨ ⌜h' ≤ₚ h⌝;
    Obs_exists_at_leader a1 h1 E: ↑DB_InvName ⊆ E → GlobalInv ⊢
      Obs a1 h1 ={E}=∗ ∃ h2, Obs DB_addr h2 ∗ ⌜h1 ≤ₚ h2⌝;
    Obs_get_smaller a h h' :
      h ≤ₚ h' → Obs a h' -∗ Obs a h;
    Obs_snoc_time a h1 e1 h2 E :
      nclose DB_InvName ⊆ E →
      Obs a (h1 ++ [e1] ++ h2) ={E}=∗
      ⌜∀ e0, e0 ∈ h1 → e0 <ₜ e1⌝ ∧
      ⌜∀ e2, e2 ∈ h2 → e1 <ₜ e2⌝;
    Obs_ext_we a a' h h' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Obs a h -∗ Obs a' h' ={E}=∗
      ⌜∀ e e', e ∈ h → e' ∈ h' → e =ₜ e' → e = e'⌝;
    Obs_ext_hist a1 a2 h1 h2 k E :
      nclose DB_InvName ⊆ E →
      at_key k h1 = at_key k h2 →
      GlobalInv ⊢ Obs a1 h1 -∗ Obs a2 h2 ={E}=∗
      ⌜hist_at_key k h1 = hist_at_key k h2⌝;

    (** Relations between points-to connective and observed requests *)
    OwnMemKey_some_obs_we k q we E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢
      k ↦ₖ{ q } Some we ={E}=∗
      k ↦ₖ{ q } Some we ∗
        ∃ h, Obs DB_addr h ∗ ⌜at_key k h = Some we⌝;
    OwnMemKey_obs_frame_prefix a k q h h' E :
      nclose DB_InvName ⊆ E →
      h ≤ₚ h' →
      GlobalInv ⊢
      k ↦ₖ{ q } (at_key k h) ∗ Obs a h' ={E}=∗
      k ↦ₖ{ q } (at_key k h) ∗ ⌜at_key k h = at_key k h'⌝;
    OwnMemKey_obs_frame_prefix_some a k q h h' we E :
      nclose DB_InvName ⊆ E →
      h ≤ₚ h' →
      at_key k h = Some we →
      GlobalInv ⊢
      k ↦ₖ{ q } Some we ∗ Obs a h' ={E}=∗
      k ↦ₖ{ q } Some we ∗ ⌜at_key k h' = Some we⌝;
    OwnMemKey_some_obs_frame a k q we h hf E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢
      k ↦ₖ{ q } (Some we) ∗ Obs a (h ++ [we] ++ hf) ={E}=∗
      k ↦ₖ{ q } (Some we) ∗ ⌜at_key k hf = None⌝;
    OwnMemKey_none_obs a k q h E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢
      k ↦ₖ{ q } None ∗ Obs a h ={E}=∗
      k ↦ₖ{ q } None ∗ ⌜hist_at_key k h = []⌝;
    OwnMemKey_allocated k q h0 h1 we0 E :
      nclose DB_InvName ⊆ E →
      h0 ≤ₚ h1 →
      at_key k h0 = Some we0 →
      GlobalInv ⊢
      k ↦ₖ{ q } (at_key k h1) ={E}=∗
      ∃ we1, k ↦ₖ{ q } (at_key k h1) ∗
            ⌜at_key k h1 = Some we1⌝ ∗ ⌜we0 ≤ₜ we1⌝;
   }.

End Predicates.

Arguments DB_resources {_ _ _ _ _}.

Notation "k ↦ₖ v" := (OwnMemKey k 1 v) (at level 20).
Notation "k ↦ₖ{ q } v" := (OwnMemKey k q v) (at level 20).
