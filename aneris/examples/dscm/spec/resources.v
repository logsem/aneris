From stdpp Require Import list.
From iris.algebra Require Import frac.
From iris.bi.lib Require Import fractional.
From aneris.aneris_lang Require Export resources.
From aneris.examples.dscm.spec Require Export base time events.

Section Predicates.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events}.

  (* Definition at_time (t : Time) (h : ghst) : option we := *)
  (*   find (λ e, bool_decide (e.(WE_timed) = t)) h. *)
  (* Lemma event_at_time (e: we) (h : ghst) : *)
  (*   e ∈ h -> at_time e.(WE_timed) h = Some e. *)
  (* Proof. Admitted. *)


  Reserved Notation "k ↦ₖ{ q } v" (at level 20).
  Reserved Notation "k ↦ₖ v" (at level 20).

  Class DB_resources := {

    (** System global invariant *)
    GlobalInv : iProp Σ;
    GlobalInvPersistent :> Persistent GlobalInv;

    (* Do we need to state it here as reserved name of system protocol? *)
    (** System socket protocol *)
    DB_socket_proto : socket_interp Σ;

    (** Logical points-to connective *)
    OwnMemKey : Key → frac → option mval → iProp Σ
    where "k ↦ₖ{ q } v" := (OwnMemKey k q v)
    and "k ↦ₖ v" := (OwnMemKey k 1 v);

    (** Observed requests *)
    Obs :  ghst → iProp Σ;

    (** Local history of write events *)
    Writes : socket_address → ghst → iProp Σ;

    (** Properties of points-to connective *)
    OwnMemKey_timeless k q v :> Timeless (k ↦ₖ{ q } v);
    OwnMemKey_exclusive k q v v' :
      k ↦ₖ{ 1 } v ⊢ k ↦ₖ{ q } v' -∗ False;
    OwnMemKey_fractioal k v :>
      Fractional (λ q, k ↦ₖ{ q } v);
    (* Do we need more of these axioms, e.g. combine, as_fractional, etc. ? *)
    OwnMemKey_as_fractioal k q v :>
      AsFractional (k ↦ₖ{ q } v) (λ q, k ↦ₖ{ q } v) q ;
    OwnMemKey_combine k q q' v v' :
      k ↦ₖ{ q } v ∗ k ↦ₖ{ q' } v' ⊢
      k ↦ₖ{ q + q'} v ∗ ⌜v = v'⌝ ;
    OwnMemKey_split k q1 q2 v :
      k ↦ₖ{ q1 + q2 } v ⊢ k ↦ₖ{ q1 } v ∗ k ↦ₖ{ q2 } v ;
    OwnMemKey_key k q e E :
      nclose DB_InvName ⊆ E →
      k ↦ₖ{q} Some (mval_of_we e) ={E}=∗
      k ↦ₖ{q} Some (mval_of_we e) ∗ ⌜WE_key e = k⌝;
    (** Properties of observed requests *)
    Obs_timeless h :> Timeless (Obs h);
    Obs_persistent h :> Persistent (Obs h);
    Obs_compare h h' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Obs h -∗ Obs h' ={E}=∗
      ⌜h ≤ₚ h'⌝ ∨ ⌜h' ≤ₚ h⌝;
    Obs_lub h1 h2 E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Obs h1 -∗ Obs h2 ={E}=∗
      ∃ h3,  ⌜h1 ≤ₚ h3⌝ ∗ ⌜h2 ≤ₚ h3⌝ ∗ Obs(h3);
    Obs_get_smaller h h' E :
      nclose DB_InvName ⊆ E →
      h ≤ₚ h' →
      Obs(h') ={E}=∗ Obs(h);
    Obs_snoc_time h1 e1 h2 E :
      nclose DB_InvName ⊆ E →
      Obs(h1 ++ [e1] ++ h2) ={E}=∗
      ⌜∀ e0, e0 ∈ h1 → e0 <ₜ e1⌝ ∧
      ⌜∀ e2, e2 ∈ h2 → e1 <ₜ e2⌝;
    Obs_ext_we h h' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Obs h -∗ Obs h' ={E}=∗
      ⌜∀ e e', e ∈ h → e' ∈ h' → e =ₜ e' → e = e'⌝;
    Obs_ext_hist h1 h2 k E :
      nclose DB_InvName ⊆ E →
      at_key k h1 = at_key k h2 →
      GlobalInv ⊢ Obs h1 -∗ Obs h2 ={E}=∗
      ⌜hist_at_key k h1 = hist_at_key k h2⌝;
    (* Ohter properties .... ? *)
    (*Obs_nodup (h);
    Obs_total_order_time
    Obs_...*)

    (** Relations between points-to connective and observed requests *)
    (* TODO: Delete after we change *)
    OwnMemKey_some_obs k q v E :
      nclose DB_InvName ⊆ E →
      k ↦ₖ{ q } Some v ={E}=∗
      k ↦ₖ{ q } Some v ∗
      ∃ h e, Obs(h) ∗ ⌜at_key k h = Some e ∧ mval_of_we e = v⌝;
    OwnMemKey_some_obs_we k q we E :
      nclose DB_InvName ⊆ E →
      k ↦ₖ{ q } Some (mval_of_we we) ={E}=∗
      k ↦ₖ{ q } Some (mval_of_we we) ∗
        ∃ h, Obs(h) ∗ ⌜at_key k h = Some we⌝;
    OwnMemKey_obs_frame_prefix k q h h' E :
      nclose DB_InvName ⊆ E →
      h ≤ₚ h' →
      k ↦ₖ{ q } (mval_of_we_opt (at_key k h)) ∗ Obs(h') ={E}=∗
      k ↦ₖ{ q } (mval_of_we_opt (at_key k h)) ∗ ⌜at_key k h = at_key k h'⌝;
    OwnMemKey_obs_frame_prefix_some k q h h' e v E :
      nclose DB_InvName ⊆ E →
      h ≤ₚ h' →
      at_key k h = Some e →
      mval_of_we e = v →
      k ↦ₖ{ q } Some v ∗ Obs(h') ={E}=∗
      k ↦ₖ{ q } Some v ∗ ⌜at_key k h' = Some e⌝;
    OwnMemKey_some_obs_frame k q e h hf E :
      nclose DB_InvName ⊆ E →
       k ↦ₖ{ q } (Some (mval_of_we e)) ∗ Obs(h ++ [e] ++ hf) ={E}=∗
       k ↦ₖ{ q } (Some (mval_of_we e)) ∗ ⌜at_key k hf = None⌝;
    OwnMemKey_none_obs k q h E :
      nclose DB_InvName ⊆ E →
      k ↦ₖ{ q } None ∗ Obs(h) ={E}=∗
      k ↦ₖ{ q } None ∗ ⌜hist_at_key k h = []⌝;
    OwnMemKey_allocated k q h0 h1 e0 E :
      nclose DB_InvName ⊆ E →
      h0 ≤ₚ h1 →
      at_key k h0 = Some e0 →
      k ↦ₖ{ q } mval_of_we_opt (at_key k h1) ={E}=∗
      ∃ e1, k ↦ₖ{ q } mval_of_we_opt (at_key k h1) ∗
            ⌜at_key k h1 = Some e1⌝ ∗ ⌜e0 ≤ₜ e1⌝;
    (* Ohter properties .... ? *)

    (** Properties of local writes history predicate *)
    Writes_timeless sa s :> Timeless (Writes sa s);
    Writes_exclusive sa s s' :
      Writes sa s ⊢ Writes sa s' -∗ False;
    Writes_origin sa s :
      Writes sa s ⊢ ⌜∀ e, e ∈ s → WE_origin e = sa⌝;
    (** Relations of local writes and observed global history *)
    Writes_obs_exists sa s :
      Writes sa s ⊢ ∃ h, Obs h ∗ ⌜s `sublist_of` h⌝;
    Writes_obs_at_origin sa s h E :
      Writes sa s ∗ Obs(h) ={E}=∗ Writes sa s ∗ ⌜hist_at_origin sa h ≤ₚ s⌝
    (* Other properties .... ? *)
   }.

End Predicates.

Notation "k ↦ₖ v" := (OwnMemKey k 1 v) (at level 20).
Notation "k ↦ₖ{ q } v" := (OwnMemKey k q v) (at level 20).

Arguments DB_resources _ _ {_ _ _ _}.
