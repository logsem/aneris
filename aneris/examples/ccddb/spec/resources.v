From aneris.aneris_lang Require Import resources.
From aneris.examples.ccddb.spec Require Import base time events.

(** Embedding of the model in the Iris logic. *)

Section Predicates.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events}.

  Class DB_resources := {

    (** Global Invariant *)
    GlobalInv : iProp Σ;

    GlobalInvPersistent :> Persistent GlobalInv;

    (** Global memory abstract state *)

    OwnMemUser : Key → gmem → iProp Σ;
    OwnMemSys : Key → gmem → iProp Σ;
    OwnMemSnapshot : Key → gmem → iProp Σ;

    (** Properties on global memory *)

    OwnMemUser_timeless k h :> Timeless (OwnMemUser k h);
    OwnMemSys_timeless k h :> Timeless (OwnMemSys k h);
    OwnMemSnapshot_timeless k h :> Timeless (OwnMemSnapshot k h);

    OwnMemUser_Exclusive k h h' : OwnMemUser k h ⊢ OwnMemUser k h' -∗ False;
    OwnMemSnapshotPersistent :> ∀ k h, Persistent (OwnMemSnapshot k h);
    OwnMemSnapshot_union k h h' :
      OwnMemSnapshot k h ⊢ OwnMemSnapshot k h' -∗ OwnMemSnapshot k (h ∪ h');
    OwnMem_update k h h' : h ⊆ h' →
      OwnMemUser k h ⊢ OwnMemSys k h ==∗ OwnMemUser k h' ∗ OwnMemSys k h';
    User_Sys_agree k h h' : OwnMemUser k h ⊢ OwnMemSys k h' -∗ ⌜h = h'⌝;
    User_Snapshot k h : OwnMemUser k h ⊢ OwnMemUser k h ∗ OwnMemSnapshot k h;
    Sys_Snapshot k h : OwnMemSys k h ⊢ OwnMemSys k h ∗ OwnMemSnapshot k h;
    OwnMemSnapshot_included k h h' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢
      OwnMemUser k h -∗ OwnMemSnapshot k h' ={E}=∗ OwnMemUser k h ∗ ⌜h' ⊆ h⌝;

    Snapshot_ext k k' h h' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ OwnMemSnapshot k h -∗
        OwnMemSnapshot k' h' ={E}=∗
          ⌜∀ a a', a ∈ h → a' ∈ h' → a =ₜ a' → a = a'⌝;

    (** Local history *)

    Seen : nat → lhst → iProp Σ;

    Observe : lhst → ae;

    (** Properties on local histories *)

    Seen_timeless i s :> Timeless (Seen i s);
    SeenPersistent :> ∀ n s, Persistent (Seen n s);
    Seen_union n s s' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Seen n s -∗ Seen n s' ={E}=∗ Seen n (s ∪ s');
    Seen_ext n n' s s' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Seen n s -∗ Seen n' s' ={E}=∗
        ⌜∀ e e', e ∈ s → e' ∈ s' → e =ₜ e'
                 → AE_key e = AE_key e' ∧ AE_val e = AE_val e'⌝;

    Seen_strong_ext n s s' E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Seen n s -∗ Seen n s' ={E}=∗
                   ⌜∀ e e', e ∈ s → e' ∈ s' → e =ₜ e' → e = e'⌝;

    Seen_provenance n s e E :
      nclose DB_InvName ⊆ E → e ∈ s →
      GlobalInv ⊢ Seen n s ={E}=∗
        ∃ h, OwnMemSnapshot (AE_key e) h ∧ ⌜erasure e ∈ h⌝;

    (** Causality property *)

    Causality n s k h E :
      nclose DB_InvName ⊆ E →
      GlobalInv ⊢ Seen n s -∗ OwnMemSnapshot k h ={E}=∗
        ⌜∀ a e, a ∈ h → e ∈ s → a <ₜ e →
                ∃ e', e' ∈ (restrict_key k s) ∧ erasure e' = a⌝;

    init_token : nat → iProp Σ;

    (** Socket protocol *)

    DB_socket_proto : socket_interp Σ;
 }.

End Predicates.

Arguments DB_resources _ _ {_ _ _ _}.

Notation "k '↦ᵤ' h" := (OwnMemUser k h) (at level 20).
Notation "k '↦ₛ' h" := (OwnMemSys k h) (at level 20).
