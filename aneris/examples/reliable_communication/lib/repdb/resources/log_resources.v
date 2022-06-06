From iris.algebra Require Import auth dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang resources.


(* ------------------------------------------------------------------------ *)
 Section Log_Resources_definition.
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

End Log_Resources_definition.
