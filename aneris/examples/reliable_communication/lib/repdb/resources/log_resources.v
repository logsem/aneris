From iris.algebra Require Import auth dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof.

(* ------------------------------------------------------------------------ *)
 Section Logical_Log_Resources.
  Context `{!anerisG Mdl Σ}.
  Context {Aty : Type}.
  Notation A := (leibnizO Aty).
  Context `{inG Σ (mono_listUR A)}.

  (** Log resources. *)


  (** ** Owned by global invariant of the system. *)
  Definition own_log_auth (γ : gname) (q : Qp) (l : list A) : iProp Σ :=
    own γ (●ML{ DfracOwn q } l).

  (** ** Duplicable observation describing the prefix of a log. *)
  Definition own_log_obs (γ : gname) (l : list A) : iProp Σ :=
    own γ (◯ML l).

  Lemma get_obs (γ : gname) (q : Qp) (l : list A) :
    own_log_auth γ q l ⊢ own_log_obs γ l.
  Proof.
   iIntros "Hown".
   rewrite /own_log_obs.
   iApply (own_mono with "Hown").
   apply mono_list_included.
  Qed.

  Lemma own_obs_prefix (γ : gname) (q : Qp) (L l : list A) :
    own_log_auth γ q L ⊢ own_log_obs γ l -∗ ⌜l `prefix_of` L⌝.
  Proof.
   iIntros "Hown Hobs".
   rewrite /own_log_obs.
   iDestruct (own_valid_2 with "[$Hown][$Hobs]") as "%Hvalid".
   apply mono_list_both_dfrac_valid_L in Hvalid.
   naive_solver.
  Qed.

End Logical_Log_Resources.

Section Physical_Log_Spec.
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context {Aty : Type}.
  Notation A := (leibnizO Aty).
  Context `{inG Σ (mono_listUR A)}.
  Context `{!Inject A val}.

  Definition inject_log (xs : list A) :=
    ($xs, #(List.length xs))%V.

  Global Program Instance Inject_log `{!Inject A val}
    : Inject (list A) val := {| inject := inject_log |}.
  Next Obligation.
    intros ? [] xs ys.
    - inversion ys as [[Hinj Hinj2]].
      symmetry. apply nil_length_inv. naive_solver.
    - inversion ys as [[Hinj Hinj2]].
      destruct xs as [| x xs]; first done.
      simplify_eq.
      inversion Hinj as [[Hinj3]]. apply Inject_list in Hinj3.
      naive_solver.
  Qed.

  Definition is_log (logM : list A) (logV : val) :=
    ∃ (lV : val), logV = (lV, #(List.length logM))%V ∧ is_list logM lV.

  Definition log_monitor_inv_def
    (ip : ip_address) (γlog : gname) (q: Qp)
    (logL : loc) (Res : list A → iProp Σ) : iProp Σ :=
    ∃ logV logM,
      ⌜is_log logM logV⌝ ∗
      logL ↦[ip] logV ∗
      own_log_auth γlog q logM ∗
      Res logM.

  Definition log_monitor_inv monN ip monγ monV γlog q logL monR :=
    is_monitor monN ip monγ monV (log_monitor_inv_def ip γlog q logL monR).

End Physical_Log_Spec.
