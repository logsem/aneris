From stdpp Require Import gmap.
From iris.algebra Require Import auth csum excl agree.
From iris.base_logic Require Import invariants.
From aneris.algebra Require Import monotone.
From aneris.prelude Require Import time.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.rcb.spec Require Import base events resources.
From aneris.examples.crdt.spec Require Import crdt_base crdt_events crdt_time crdt_resources.
From aneris.examples.crdt.oplib.spec Require Import events spec.
From aneris.examples.crdt.oplib.proof Require Import time params.

Section RAs.

  Context `{!EqDecision LogOp, !Countable LogOp, !@OpLibG LogOp _ _ Σ}.

  (* RAs needed by OpLib  *)
  Class Internal_OpLibG Σ := mkInternalG {
      (* Global state, global snap and local state *)
      Int_OpLibG_auth_gset_ev :> inG Σ (authUR (gsetUR (Event LogOp)));
      (* Local state *)
      Int_OpLibG_frac_agree :> inG Σ (prodR fracR (agreeR (gsetO (Event LogOp))));
      (* Local and global snapshots *)
      Int_OpLibG_mono :> inG Σ (authUR (monotoneUR (@cc_subseteq LogOp _ _)));
      Int_OpLibG_lockG :> lockG Σ;
      (* Tracking invariant states *)
      Int_OpLibG_oneshot :> inG Σ oneShotR;
    }.

  (* TODO: move to instantiation *)
  Global Instance: Internal_OpLibG Σ :=
    mkInternalG
      Σ
      (@OpLibG_auth_gset_ev _ _ _ _ _)
      (@OpLibG_frac_agree _ _  _ _ _)
      (@OpLibG_mono _ _ _ _ _)
      (@OpLibG_lockG _ _ _ _ _)
      (@OpLibG_oneshot _ _ _ _ _).

End RAs.

Arguments Internal_OpLibG (LogOp) {_ _} (Σ).

Section GhostParams.

  (* These are all ghost names taken as parameters and used in the global invariant
     maintained by oplib. There are exactly N names per list, where N is the
     number of participants. *)
  Class OpLib_InvGhostNames `{!CRDT_Params} := {
    γ_glob : gname;
    γ_own : list gname;
    γ_for : list gname;
    γ_sub : list gname;
    γ_cc : list gname;
    γ_inv : list gname;
    γ_own_len : length γ_own = length CRDT_Addresses;
    γ_for_len : length γ_for = length CRDT_Addresses;
    γ_sub_len : length γ_sub = length CRDT_Addresses;
    γ_cc_len : length γ_cc = length CRDT_Addresses;
    γ_inv_len : length γ_inv = length CRDT_Addresses;
  }.

End GhostParams.

Section OneShot.

  Context `{!anerisG Mdl Σ, inG Σ oneShotR}.
  Definition invSt := csum (excl unit) (agree unit).

  (* invariant is uninitialized: exclusive knowledge *)
  Definition inv_uninit : invSt := Cinl (Excl ()).
  (* invariant is initialized: ownsership is persistent *)
  Definition inv_init : invSt := Cinr (to_agree ()).

  (* Check that the instances exist *)
  Section check_instances.
    Instance inv_uninit_excl_instance : Exclusive inv_uninit.
    Proof. apply _. Qed.

    Instance inv_init_pers γ : Persistent (own γ inv_init).
    Proof. apply _. Qed.
  End check_instances.

  (* We can update from uninit to init *)
  Lemma inv_update : inv_uninit ~~> inv_init.
  Proof. by apply cmra_update_exclusive. Qed.

  Lemma inv_own_update γ : own γ inv_uninit ==∗ own γ inv_init.
  Proof. apply own_update, inv_update. Qed.

  Lemma inv_uninit_excl γ (e : oneShotR) : own γ inv_uninit ⊢ own γ e -∗ False.
  Proof.
    iIntros "Hun Hother".
    iDestruct (own_valid_2 with "Hun Hother") as "%Hv".
    exfalso.
    apply (exclusive0_l inv_uninit e).
    by apply cmra_valid_validN.
  Qed.

End OneShot.

(** * Instantiation of OpLib resources *)
Section Resources.

  Context {LogOp LogSt : Type}.

  Context `{!anerisG Mdl Σ,
            !EqDecision LogOp,
            !Countable LogOp,
            !OpLib_Params LogOp LogSt,
            !RCB_events,
            !Internal_OpLibG LogOp Σ,
            !CRDT_Params,
            !RCB_resources Mdl Σ,
            !OpLib_InvGhostNames}.

  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Hint Resolve rcb_invname_subseteq' : core.
  Hint Resolve rcb_invname_subseteq_mask : core.

  (** * Coherence for global events *)

  (* Events are coherent if all their fields are either coherent or equal. *)
  Definition glob_st_coh (olEv : Event LogOp) (rcbEv : ge) : Prop :=
    OpLib_Op_Coh  (EV_Op olEv) (GE_payload rcbEv) ∧
    olEv.(EV_Orig) = (GE_origin rcbEv) ∧
    olEv.(EV_Time) = (GE_vc rcbEv).

  (* TODO: consider alternative formulation that establishes a bijection.
     As it stands, s can be larger than h, because coherence is injective but
     not necesarily functional. *)
  Definition glob_st_set_coh (h : gset (Event LogOp)) (s : gset ge) : Prop :=
    (∀ p, p ∈ h -> ∃ q, q ∈ s ∧ glob_st_coh p q) ∧
    (∀ q, q ∈ s -> ∃ p, p ∈ h ∧ glob_st_coh p q).

  Lemma glob_st_set_coh_union h h' s s' :
    glob_st_set_coh h s -> glob_st_set_coh h' s' -> glob_st_set_coh (h ∪ h') (s ∪ s').
  Proof.
    intros Hcoh Hcoh'.
    split.
    - intros p [Hl | Hr]%elem_of_union.
      + apply Hcoh in Hl as [q [? ?]].
        assert (q ∈ s ∪ s') by set_solver.
        eauto.
      + apply Hcoh' in Hr as [q [? ?]].
        assert (q ∈ s ∪ s') by set_solver.
        eauto.
    - intros q [Hl | Hr]%elem_of_union.
      + apply Hcoh in Hl as [p [? ?]].
        assert (p ∈ h ∪ h') by set_solver.
        eauto.
      + apply Hcoh' in Hr as [p [? ?]].
        assert (p ∈ h ∪ h') by set_solver.
        eauto.
  Qed.

  Lemma glob_st_coh_inj p p' q :
    glob_st_coh p q -> glob_st_coh p' q -> p = p'.
  Proof.
    intros Hpq Hp'q.
    destruct p, p'.
    unfold glob_st_coh in *.
    simpl in *.
    destruct Hpq as (Hop & Horig & Hvc).
    destruct Hp'q as (Hop' & Horig' & Hvc').
    subst.
    rewrite (OpLib_Op_Coh_Inj _ _ _ Hop Hop').
    done.
  Qed.

  (* Can only prove one direction because of injectivity *)
  Lemma glob_st_set_coh_subseteq h h' s s' :
    glob_st_set_coh h s -> glob_st_set_coh h' s' -> s ⊆ s' -> h ⊆ h'.
  Proof.
    intros Hcoh Hcoh'.
    intros Hsub x Hx.
    apply Hcoh in Hx as [q [Hin Hxq]].
    assert (q ∈ s') as Hqs' by set_solver.
    apply Hcoh' in Hqs' as [p [Hpin Hpq]].
    rewrite (glob_st_coh_inj _ _ _ Hxq Hpq).
    done.
  Qed.

  Lemma glob_st_set_coh_singleton p q :
    glob_st_coh p q -> glob_st_set_coh {[p]} {[q]}.
  Proof.
    intros coh.
    split; intros x ->%elem_of_singleton;
      [exists q | exists p]; auto with set_solver.
  Qed.

  Lemma glob_st_coh_orig p q :
    glob_st_coh p q -> (EV_Orig p) = (GE_origin q).
  Proof.
    rewrite /glob_st_coh.
    intros (? & ? & ?); done.
  Qed.

  (** * Local state coherence *)
  Definition loc_st_coh (olEv : Event LogOp) (rcbEv : le) : Prop :=
    OpLib_Op_Coh (EV_Op olEv) (LE_payload rcbEv) ∧
    olEv.(EV_Orig) = (LE_origin rcbEv) ∧
    olEv.(EV_Time) = (LE_vc rcbEv).

  Definition loc_st_set_coh (h : gset (Event LogOp)) (s : gset le) : Prop :=
    (∀ p, p ∈ h -> ∃ q, q ∈ s ∧ loc_st_coh p q) ∧
    (∀ q, q ∈ s -> ∃ p, p ∈ h ∧ loc_st_coh p q).

  Lemma loc_st_coh_inj p p' q :
    loc_st_coh p q -> loc_st_coh p' q -> p = p'.
  Proof.
    intros Hpq Hp'q.
    destruct p, p'.
    unfold loc_st_coh in *.
    simpl in *.
    destruct Hpq as (Hop & Horig & Hvc).
    destruct Hp'q as (Hop' & Horig' & Hvc').
    subst.
    rewrite (OpLib_Op_Coh_Inj _ _ _ Hop Hop').
    done.
  Qed.

  Lemma loc_st_coh_vc p p' q q' :
    p.(EV_Time) = p'.(EV_Time) ->
    loc_st_coh p q ->
    loc_st_coh p' q' ->
    (LE_vc q) = (LE_vc q').
  Proof.
    intros Hvceq (_&_&<-) (_&_&<-).
    done.
  Qed.

  Lemma loc_st_coh_glob_st_coh p q :
    loc_st_coh p q <->
    glob_st_coh p (erasure q).
  Proof.
    split.
    - intros (?&?&?).
      rewrite /glob_st_coh.
      rewrite erasure_payload erasure_origin erasure_vc.
      done.
    - intros (?&?&?).
      rewrite /loc_st_coh.
      rewrite <- erasure_payload.
      rewrite <- erasure_origin.
      rewrite <- erasure_vc.
      done.
  Qed.

  (** * Resource definitions *)

  (* Global state *)
  Definition oplib_glob_st_inv (h : gset (Event LogOp)) : iProp Σ :=
    ∃ (s : gset ge),
      OwnGlobal s ∗
      own γ_glob ((1/3)%Qp, to_agree h) ∗
      ⌜glob_st_set_coh h s⌝ ∗
      ⌜events_total_order h⌝.

  Definition oplib_glob_st_user (h : gset (Event LogOp)) : iProp Σ :=
    own γ_glob ((2/3)%Qp, to_agree h).

  (* Global snapshots *)
  Definition oplib_glob_snap (h : gset (Event LogOp)) : iProp Σ :=
    ∃ (s s__sub : gset ge),
      OwnGlobalSnapshot s ∗
      (* We can't take s__sub = s because then we can't
         prove oplib_loc_snap_glob_snap_provenance *)
      ⌜s__sub ⊆ s⌝ ∗
      ⌜glob_st_set_coh h s__sub⌝.

  (* Local snapshots *)

  Definition own_orig (i : nat) (h : gset (Event LogOp)) : Prop :=
    ∀ e, e ∈ h -> e.(EV_Orig) = i.

  Definition foreign_orig (i : nat) (h : gset (Event LogOp)) : Prop :=
    ∀ e, e ∈ h -> ¬ (e.(EV_Orig) = i).

  Lemma orig_disjoint i h1 h2 :
    own_orig i h1 -> foreign_orig i h2 -> h1 ## h2.
    intros Hown Hfor.
    intros e Hin1%Hown Hin2%Hfor.
    apply Hin2. done.
  Qed.

  Lemma own_orig_union i h1 h2 : own_orig i h1 -> own_orig i h2 -> own_orig i (h1 ∪ h2).
  Proof.
    intros Hin1 Hin2 e [Hl | Hr]%elem_of_union; [apply Hin1 | apply Hin2]; done.
  Qed.

  Lemma foreign_orig_union i h1 h2 :
    foreign_orig i h1 -> foreign_orig i h2 -> foreign_orig i (h1 ∪ h2).
  Proof.
    intros Hin1 Hin2 e [Hl | Hr]%elem_of_union; [apply Hin1 | apply Hin2]; done.
  Qed.

  Definition oplib_loc_snap (γ_cc γ_inv : gname)
             (i : nat) (h__own h__for : gset (Event LogOp)) : iProp Σ :=
    ⌜own_orig i h__own⌝ ∗
    ⌜foreign_orig i h__for⌝ ∗
    own γ_cc (◯ (princ_ev (h__own ∪ h__for))) ∗
    own γ_inv inv_init.

  Definition oplib_loc_snap_wrap i h__own h__for : iProp Σ :=
    ∃ γcc γinv,
      ⌜γ_cc !! i = Some γcc⌝ ∗
      ⌜γ_inv !! i = Some γinv⌝ ∗
      oplib_loc_snap γcc γinv i h__own h__for.

  (* Local state *)

  Definition oplib_loc_st_user (γ_own γ_sub γ_cc γ_inv : gname)
             (i : nat) (h__own h__for : gset (Event LogOp)) : iProp Σ :=
    ⌜own_orig i h__own⌝ ∗
    ⌜foreign_orig i h__for⌝ ∗
    own γ_own ((1/3)%Qp, to_agree h__own) ∗
    own γ_sub ((2/3)%Qp, to_agree h__for) ∗
    (* We carry a copy of the corresponding snapshot so we can take
       snaps without opening invariants. *)
    oplib_loc_snap γ_cc γ_inv i h__own h__for ∗
    own γ_inv inv_init.

  Definition oplib_loc_st_user_wrap i h__own h__for : iProp Σ :=
    ∃ γown γsub γcc γinv,
      ⌜γ_own !! i = Some γown⌝ ∗
      ⌜γ_sub !! i = Some γsub⌝ ∗
      ⌜γ_cc !! i = Some γcc⌝ ∗
      ⌜γ_inv !! i = Some γinv⌝ ∗
      oplib_loc_st_user γown γsub γcc γinv i h__own h__for.

  Definition oplib_loc_st_lock (γ_own γ_for γ_inv : gname)
             (i : nat) (h__own h__for : gset (Event LogOp)) : iProp Σ :=
    ⌜own_orig i h__own⌝ ∗
    ⌜foreign_orig i h__for⌝ ∗
    own γ_own ((1/3)%Qp, to_agree h__own) ∗
    own γ_for ((1/2)%Qp, to_agree h__for) ∗
    own γ_inv inv_init.

  Definition oplib_loc_st_lock_wrap i h__own h__for : iProp Σ :=
    ∃ γown γfor γinv,
      ⌜γ_own !! i = Some γown⌝ ∗
      ⌜γ_for !! i = Some γfor⌝ ∗
      ⌜γ_inv !! i = Some γinv⌝ ∗
      oplib_loc_st_lock γown γfor γinv i h__own h__for.

  (** * Global Invariant *)

  Definition OwnLocalOpt γ i s : iProp Σ :=
    (own γ inv_uninit) ∨ (own γ inv_init ∗ OwnLocal i s).

  Lemma OwnLocalOpt_Init γ i s : OwnLocalOpt γ i s ⊢ own γ inv_init -∗ OwnLocal i s.
  Proof.
    iIntros "[Hl|[_ Hr]] Hown"; [|done].
    by iDestruct (inv_uninit_excl with "Hl Hown") as "?".
  Qed.

  (* If we see OwnLocalOpt in the context together with the right inv_init resource, then
     try to conclude that we have an OwnLocal. *)
  Ltac own_local_opt_init gname :=
    lazymatch goal with
    | [ |- context[environments.Esnoc _ ?IH1 (OwnLocalOpt gname _ _)] ] =>
        lazymatch goal with
          [ |- context[environments.Esnoc _ ?IH2 (own gname inv_init)] ] =>
            iDestruct (OwnLocalOpt_Init with IH1) as IH1;
            iDestruct (IH1 with IH2) as IH1
        end
    end.

  Definition oplib_loc_st_inv γown γfor γsub γcc γinv(i : nat)
             (h__own h__for h__sub: gset (Event LogOp)) (s : gset le) : iProp Σ :=
      ⌜loc_st_set_coh (h__own ∪ h__for) s⌝ ∗
      ⌜own_orig i h__own⌝ ∗
      ⌜foreign_orig i h__for⌝ ∗
      ⌜foreign_orig i h__sub⌝ ∗
      ⌜cc_subseteq (h__own ∪ h__sub) (h__own ∪ h__for)⌝ ∗
      OwnLocalOpt γinv i s ∗
      own γown ((1/3)%Qp, to_agree h__own) ∗
      own γfor ((1/2)%Qp, to_agree h__for) ∗
      own γsub ((1/3)%Qp, to_agree h__sub) ∗
      own γcc (● (princ_ev (h__own ∪ h__sub))).

  Definition oplib_loc_st_inv_wrap (i : nat)
             (h__own h__for h__sub : gset (Event LogOp)) : iProp Σ :=
    ∃ γown γfor γsub γcc γinv s,
      ⌜γ_own !! i = Some γown⌝ ∗
      ⌜γ_for !! i = Some γfor⌝ ∗
      ⌜γ_sub !! i = Some γsub⌝ ∗
      ⌜γ_cc !! i = Some γcc⌝ ∗
      ⌜γ_inv !! i = Some γinv⌝ ∗
        oplib_loc_st_inv γown γfor γsub γcc γinv i h__own h__for h__sub s.

  Definition oplib_loc_st_inv_prop : iProp Σ :=
    (∃ h, oplib_glob_st_inv h) ∗
    [∗ list] k ↦ _ ∈ CRDT_Addresses,
      ∃ h__own h__for h__sub, oplib_loc_st_inv_wrap k h__own h__for h__sub.

  Lemma γ_cc_lookup_lt (i : nat) γ :
    γ_cc !! i = Some γ -> (i < length CRDT_Addresses)%nat.
  Proof.
    intros Hlookup.
    rewrite -γ_cc_len.
    apply lookup_lt_is_Some.
    done.
  Qed.

  Lemma γ_cc_lookup i γ :
    γ_cc !! i = Some γ -> ∃ addr, CRDT_Addresses !! i = Some addr.
  Proof.
    intros Hlt%γ_cc_lookup_lt.
    apply list_lookup_lookup_total_lt in Hlt.
    eauto.
  Qed.

  Lemma oplib_loc_st_user_lt i s1 s2 :
    oplib_loc_st_user_wrap i s1 s2 ⊢ ⌜(i < length CRDT_Addresses)%nat⌝.
  Proof.
    iIntros "Huser".
    iDestruct "Huser" as (γ1 γ2 γ3 γ4) "(_&_&%Hcc&_)".
    iPureIntro.
    eapply γ_cc_lookup_lt; eauto.
  Qed.

  Lemma oplib_loc_st_lock_lt i s1 s2 :
    oplib_loc_st_lock_wrap i s1 s2 ⊢ ⌜(i < length CRDT_Addresses)%nat⌝.
  Proof.
    iIntros "Hlock".
    iDestruct "Hlock" as (γ1 γ2 γ3) "(%Hown&%&%&_)".
    iPureIntro.
    rewrite -γ_own_len.
    apply lookup_lt_is_Some.
    done.
  Qed.

  Definition inv_aux `{A : Type} `{!Inhabited A} (l : list A) (base : nat) : iProp Σ :=
    [∗ list] k ↦ _ ∈ l,
      ∃ h__own h__for h__sub, oplib_loc_st_inv_wrap (base + k) h__own h__for h__sub.

  Lemma big_sepL_base_0 `{A : Type} (l : list A) (Φ : nat -> A -> iProp Σ) :
    ([∗ list] i ↦ k ∈ l, Φ i k) ⊢ ([∗ list] i ↦ k ∈ l, Φ (0 + i)%nat k).
  Proof.
    iIntros "Hbig".
    iApply (big_sepL_impl with "Hbig"); auto.
  Qed.

  Lemma big_sepL_base_0' `{A : Type} (l : list A) (Φ : nat -> A -> iProp Σ) :
    ([∗ list] i ↦ k ∈ l, Φ (0 + i)%nat k) ⊢ ([∗ list] i ↦ k ∈ l, Φ i k).
  Proof.
    iIntros "Hbig".
    iApply (big_sepL_impl with "Hbig"); auto.
  Qed.

  Lemma oplib_inv_lookup_acc_aux `{A : Type} `{!Inhabited A} (l : list A) (base i : nat) :
    inv_aux l base ⊢
    ⌜(i < length l)%nat⌝ -∗
    ∃ h__own h__for h__sub,
      oplib_loc_st_inv_wrap (base + i) h__own h__for h__sub ∗
      ((∃ h__own' h__for' h__sub',
          oplib_loc_st_inv_wrap (base + i) h__own' h__for' h__sub') -∗ inv_aux l base).
  Proof.
    iIntros "Hinv %Hlen".
    apply list_lookup_lookup_total_lt in Hlen.
    rewrite /oplib_loc_st_inv_prop.
    iPoseProof (big_sepL_lookup_acc _ _ _ _ Hlen with "Hinv") as "[Hres1 Hres2]".
    iDestruct "Hres1" as (h__own h__for h__forsub) "Hwrap".
    iExists h__own, h__for, h__forsub.
    iFrame.
  Qed.

  Lemma oplib_inv_lookup_acc' (i : nat) :
    oplib_loc_st_inv_prop ⊢
    ⌜(i < length CRDT_Addresses)%nat⌝ -∗
    ∃ h__own h__for h__sub hglob,
      oplib_loc_st_inv_wrap  i h__own h__for h__sub ∗
      oplib_glob_st_inv hglob ∗
      ((∃ h__own' h__for' h__sub' hglob',
           oplib_loc_st_inv_wrap i h__own' h__for' h__sub' ∗
           oplib_glob_st_inv hglob') -∗ oplib_loc_st_inv_prop).
  Proof.
    iIntros "[Hglob Hprop] #Hlen".
    rewrite /oplib_loc_st_inv_prop.
    iDestruct (big_sepL_base_0 with "Hprop") as "Hprop".
    iDestruct (oplib_inv_lookup_acc_aux with "Hprop Hlen") as (hown hfor hsub) "[Hwrap Hprop]".
    iDestruct "Hglob" as (hglob) "Hglob".
    iExists hown, hfor, hsub, hglob.
    iFrame.
    iIntros "Hpre".
    iDestruct "Hpre" as (hown' hfor' hsub' hglob') "[Hinv Hglob]".
    iSplitL "Hglob"; [eauto |].
    simpl.
    iDestruct ("Hprop" with "[Hinv]") as "Hprop"; [eauto |].
    done.
  Qed.

  Lemma oplib_inv_lookup_acc (i : nat) :
    oplib_loc_st_inv_prop ⊢
    ⌜(i < length CRDT_Addresses)%nat⌝ -∗
    ∃ h__own h__for h__sub,
      oplib_loc_st_inv_wrap  i h__own h__for h__sub ∗
      (oplib_loc_st_inv_wrap i h__own h__for h__sub -∗ oplib_loc_st_inv_prop).
  Proof.
    iIntros "Hprop #Hlen".
    iDestruct (oplib_inv_lookup_acc' with "Hprop Hlen") as (hown hfor hsub hglob) "[H1 [H2 H3]]".
    iExists hown, hfor, hsub.
    iFrame.
    iIntros "Hwrap".
    iApply "H3".
    eauto with iFrame.
  Qed.

  Lemma list_breakup2 `{A : Type} (i : nat) (l : list A) :
    (i < length l)%nat ->
    ∃ l1 l2,
      (length l1 = i + 1)%nat ∧
      l = l1 ++ l2.
  Proof.
    induction i as [ | i'].
    - intros Hlen.
      assert (∃ x y, l = x :: y) as (x & y & Hcons).
      { destruct l as [ | x y]; [ | eauto].
        simpl in *; lia. }
      exists [x], y.
      auto with lia.
    - intros Hlt.
      assert (i' < length l)%nat as Hlt' by lia.
      apply IHi' in Hlt' as (l1 & l2 & Hlen_l1 & Happ).
      assert (length l2 > 0)%nat.
      { assert (length l2 = length l - length l1)%nat as ->; [ | lia].
        rewrite Happ app_length.
        lia. }
      assert (∃ x y, l2 = x :: y) as (x & y & Hcons).
      { destruct l2 as [ | x y]; [ | eauto].
       simpl in *; lia. }
      exists (l1 ++ [x]), y.
      split.
      + rewrite app_length.
        simpl.
        rewrite Hlen_l1.
        lia.
      + rewrite Happ Hcons.
        rewrite -app_assoc.
        done.
  Qed.

  Lemma oplib_inv_lookup_acc2_lt (i j : nat) :
    (i < length CRDT_Addresses)%nat ->
    (j < length CRDT_Addresses)%nat ->
    (i < j)%nat ->
    oplib_loc_st_inv_prop ⊢
    ∃ h__own1 h__own2 h__for1 h__for2 h__sub1 h__sub2,
      oplib_loc_st_inv_wrap i h__own1 h__for1 h__sub1 ∗
      oplib_loc_st_inv_wrap j h__own2 h__for2 h__sub2 ∗
      (oplib_loc_st_inv_wrap i h__own1 h__for1 h__sub1 -∗
       oplib_loc_st_inv_wrap j h__own2 h__for2 h__sub2 -∗
       oplib_loc_st_inv_prop).
  Proof.
    iIntros (Hi Hj Hne) "[Hglob Hinv]".
    rewrite /oplib_loc_st_inv_prop.
    pose proof (list_breakup2 i CRDT_Addresses Hi) as (l1 & l2 & Hlen & Happ).
    assert ((i < length l1)%nat) as Hlt1 by lia.
    assert ((length l1 + (j - length l1) = j)%nat) as Heq by lia.
    rewrite Happ app_length in Hj.
    assert (j - length l1 < length l2)%nat as Hlt2 by lia.
    rewrite Happ.
    iDestruct (big_sepL_app with "Hinv") as "[Hl1 Hl2]".
    iDestruct (big_sepL_base_0 with "Hl1") as "Hl1".
    iDestruct (oplib_inv_lookup_acc_aux with "Hl1 [//]") as
      (hown1 hfor1 hsub1) "[Hwrap1 Hacc1]".
    iDestruct (oplib_inv_lookup_acc_aux with "Hl2 [//]") as
      (hown2 hfor2 hsub2) "[Hwrap2 Hacc2]".
    rewrite Heq; simpl.
    iExists hown1, hown2, hfor1, hfor2, hsub1, hsub2.
    iFrame.
    iIntros "Hinv1 Hinv2".
    iDestruct ("Hacc1" with "[Hinv1]") as "Hacc1"; [eauto |].
    iDestruct ("Hacc2" with "[Hinv2]") as "Hacc2"; [eauto |].
    rewrite /inv_aux.
    iDestruct (big_sepL_base_0' _
              (λ n _, (∃ hown hfor hsub,
                          oplib_loc_st_inv_wrap (0 + n) hown hfor hsub)%I)
                with "Hacc1") as "Hacc1".
    iDestruct (big_sepL_app with "[$Hacc1 $Hacc2]") as "Hres".
    iFrame.
  Qed.

  Lemma oplib_inv_lookup_acc2 (i j : nat) :
    (i < length CRDT_Addresses)%nat ->
    (j < length CRDT_Addresses)%nat ->
    not (i = j)%nat ->
    oplib_loc_st_inv_prop ⊢
    ∃ h__own1 h__own2 h__for1 h__for2 h__sub1 h__sub2,
      oplib_loc_st_inv_wrap i h__own1 h__for1 h__sub1 ∗
      oplib_loc_st_inv_wrap j h__own2 h__for2 h__sub2 ∗
      (oplib_loc_st_inv_wrap i h__own1 h__for1 h__sub1 -∗
       oplib_loc_st_inv_wrap j h__own2 h__for2 h__sub2 -∗
       oplib_loc_st_inv_prop).
  Proof.
    iIntros (Hi Hj Hne) "Hinv".
    destruct (decide (i < j)%nat) as [Hl | Hr].
    - iDestruct (oplib_inv_lookup_acc2_lt i j with "Hinv") as "Hres"; auto.
    - assert ((j < i)%nat) as Hlt by lia.
      iDestruct (oplib_inv_lookup_acc2_lt j i with "Hinv") as "Hres";
        [done | done | done |].
      iDestruct "Hres" as (hown1 hown2 hfor1 hfor2 hsub1 hsub2)
                            "(Hj & Hi & Hacc)".
      iExists hown2, hown1, hfor2, hfor1, hsub2, hsub1.
      iFrame.
      iIntros "H2 H1".
      iApply ("Hacc" with "H1 H2").
  Qed.

  Lemma oplib_inv_lookup_acc_γcc i γ :
    oplib_loc_st_inv_prop ⊢
    ⌜γ_cc !! i = Some γ⌝ -∗
    ∃ h__own h__for h__sub,
      oplib_loc_st_inv_wrap i h__own h__for h__sub ∗
      (oplib_loc_st_inv_wrap i h__own h__for h__sub -∗ oplib_loc_st_inv_prop).
  Proof.
    iIntros "Hinv %Hlookup".
    assert ((i < length CRDT_Addresses)%nat) as ?.
    { eapply γ_cc_lookup_lt.
      done. }
    iApply (oplib_inv_lookup_acc with "Hinv").
    iPureIntro. done.
  Qed.

  (* Our global invariant consists of two invariants: the RCB's invariant,
     and Oplib's own invariants for tracking local state and snapshots.
     The namespaces for both are disjoint and included in ↑CRDT_InvName. *)
  Definition oplib_inv : iProp Σ :=
    GlobalInv ∗
    inv OpLib_InvName oplib_loc_st_inv_prop.

  Instance oplib_inv_persistent : Persistent oplib_inv.
  Proof. apply _. Qed.

  (** * Laws about global state *)

  Lemma oplib_glob_st_excl h h' :
    oplib_glob_st_user h ⊢ oplib_glob_st_user h' -∗ False.
  Proof.
    iIntros "Hglob Hglob'".
    rewrite /oplib_glob_st_user.
    iDestruct (own_op with "[$Hglob $Hglob']") as "Hres".
    rewrite -pair_op.
    rewrite frac_op.
    iDestruct (own_valid with "Hres") as "%Hvalid".
    exfalso.
    apply pair_valid in Hvalid as [Hvalid _].
    simpl in Hvalid.
    apply (iffLR (frac_valid _)) in Hvalid.
    done.
  Qed.

  (* This is not visible outside the section, but is here to check that the class instance
     can be found. *)
  Lemma oplib_glob_st_timeless h : Timeless (oplib_glob_st_user h).
  Proof. apply _. Qed.

  Lemma oplib_glob_snap_pers h : Persistent (oplib_glob_snap h).
  Proof. apply _. Qed.

  Lemma oplib_glob_snap_timeless h : Timeless (oplib_glob_snap h).
  Proof. apply _. Qed.

  Lemma pair_agree γ (f1 f2 : Qp) (h1 h2 : gset (Event (LogOp))) :
    own γ (f1, to_agree h1) ⊢
    own γ (f2, to_agree h2) -∗
    ⌜h1 = h2⌝.
  Proof.
    iIntros "Hown1 Hown2".
    iDestruct (own_valid_2 with "Hown1 Hown2") as "%Hvalid".
    iPureIntro.
    apply pair_valid in Hvalid as [_ Hvalid].
    apply to_agree_op_valid_L.
    done.
  Qed.

  Lemma oplib_glob_agree h :
    oplib_glob_st_user h ⊢
    (∃ h', oplib_glob_st_inv h') -∗
              oplib_glob_st_user h ∗
              oplib_glob_st_inv h.
  Proof.
    iIntros "Hown1 Hown2".
    iDestruct "Hown2" as (h') "Hown2".
    iDestruct "Hown2" as (s) "(Hglob & Hown2 & %)".
    iDestruct (pair_agree with "Hown1 Hown2") as %->.
    eauto with iFrame.
  Qed.

  Lemma pair_update γ (f1 f2 : Qp) h h' :
    (f1 + f2 = 1)%Qp ->
    own γ (f1, to_agree h) ⊢
    own γ (f2, to_agree h) ==∗
      own γ (f1, to_agree h') ∗
      own γ (f2, to_agree h').
  Proof.
    iIntros (Hsum) "Hown1 Hown2".
    rewrite -own_op.
    iApply (own_update_2 with "Hown1 Hown2").
    rewrite -pair_op.
    rewrite frac_op.
    assert (Exclusive ((f1 + f2)%Qp)) as ?.
    { rewrite Hsum.
      apply frac_full_exclusive. }
    apply cmra_update_exclusive.
    apply pair_valid. split; simpl.
    - rewrite frac_op.
      rewrite Hsum.
      done.
    - apply to_agree_op_valid; done.
  Qed.

  Lemma oplib_glob_st_take_snap E h :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_glob_st_user h ={E}=∗ oplib_glob_st_user h ∗ oplib_glob_snap h.
  Proof.
    iIntros (Hsub) "[#Hrcbinv #Hinv] Hglob".
    iInv OpLib_InvName as "> [Hglobinv Hprop]" "Hclose".
    iDestruct (oplib_glob_agree with "Hglob Hglobinv") as "[Hglob Hglobinv]".
    rewrite /oplib_glob_st_user.
    rewrite /oplib_glob_st_inv.
    iDestruct "Hglobinv" as (s) "(Hownglob&Hown1&%Hcoh&%Htotal)".
    iDestruct (User_Snapshot with "Hownglob") as "[Hownglob Hownsnap]".
    iMod ("Hclose" with "[Hownglob Hown1 Hprop]") as "_".
    { iModIntro.
      rewrite /oplib_loc_st_inv_prop.
      iFrame.
      iExists _.
      iFrame.
      eauto with iFrame.
    }
    iModIntro. iFrame.
    rewrite /oplib_glob_snap.
    eauto with iFrame.
  Qed.

  Lemma oplib_glob_snap_union h h' :
    oplib_glob_snap h ⊢ oplib_glob_snap h' -∗ oplib_glob_snap (h ∪ h').
  Proof.
    iIntros "Hsnap Hsnap'".
    iDestruct "Hsnap" as (s ssub) "(#Hsnap & %Hsub & %Hcoh)".
    iDestruct "Hsnap'" as (s' ssub') "(#Hsnap' & %Hsub' & %Hcoh')".
    pose proof (glob_st_set_coh_union _ _ _ _ Hcoh Hcoh') as Hcoh_union.
    iPoseProof (OwnGlobalSnapshot_union with "Hsnap Hsnap'") as "Hownunion".
    iExists _, (ssub ∪ ssub').
    iFrame "Hownunion".
    eauto with set_solver.
  Qed.

  Lemma oplib_glob_snap_included E h h' :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_glob_snap h -∗ oplib_glob_st_user h' ={E}=∗ ⌜h ⊆ h'⌝ ∗ oplib_glob_st_user h'.
  Proof.
    iIntros (HE) "[#Hrcbinv #Hinv] #Hsnap Hglob".
    iDestruct "Hsnap" as (s ssub) "(#Hownsnap & %Hsub & %Hcoh)".
    iInv OpLib_InvName as "> [Hglobinv Hprop]" "Hclose".
    iDestruct (oplib_glob_agree with "Hglob Hglobinv") as "[Hglob Hglobinv]".
    iDestruct "Hglobinv" as (s') "(Hownglob & Hglobinv & %Hcoh' & %Htotal')".
    iMod (OwnGlobalSnapshot_included with "[] Hownglob Hownsnap") as
      "[Hownglob %Hincl]"; try (auto || done).
    iMod ("Hclose" with "[Hownglob Hglobinv Hprop]") as "_".
    { iModIntro.
      iFrame. iExists h'.
      iFrame. eauto with iFrame. }
    iModIntro.
    iFrame. iPureIntro.
    eapply glob_st_set_coh_subseteq; eauto with set_solver.
  Qed.

  Lemma oplib_glob_snap_ext E h h' :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_glob_snap h -∗ oplib_glob_snap h' ={E}=∗
    ⌜∀ e e', e ∈ h -> e' ∈ h' -> e.(EV_Time) = e'.(EV_Time) -> e = e'⌝.
  Proof.
    iIntros (Hin) "[#Hinv _] #Hsnap #Hsnap'".
    iDestruct "Hsnap" as (s ssub) "(#Hownsnap & %Hsub & %Hcoh & %Htotal)".
    iDestruct "Hsnap'" as (s' ssub') "(#Hownsnap' & %Hsub' & %Hcoh')".
    iMod ((Snapshot_ext _ _ E) with "Hinv Hownsnap Hownsnap'") as "%Hext"; [auto |].
    iModIntro. iPureIntro.
    intros e e' Hein Hein' Hvceq.
    apply Hcoh in Hein as [q [Hins Hecoh]].
    apply Hcoh' in Hein' as [q' [Hins' Hecoh']].
    assert ((GE_vc q) = (GE_vc q')) as Hqq'.
    { destruct Hecoh as (_ & _ & <-).
      destruct Hecoh' as (_ & _ & <-).
      done. }
    assert (q ∈ s) as Hs by set_solver.
    assert (q' ∈ s') as Hs' by set_solver.
    pose proof (Hext _ _ Hs Hs' Hqq') as ->.
    eapply glob_st_coh_inj; eauto.
  Qed.

  Lemma events_total_order_sub (h h' : gset (Event LogOp)) :
    h ⊆ h' -> events_total_order h' -> events_total_order h.
  Proof.
    intros Hsub Htotal' e e' Hin Hin' Hne Horig.
    apply Htotal'; auto with set_solver.
  Qed.

  Lemma oplib_glob_snap_total E h :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢ oplib_glob_snap h ={E}=∗ ⌜events_total_order h⌝.
  Proof.
    iIntros (Hin) "[#Hgi #Hinv] #Hsnap".
    iDestruct "Hsnap" as (s ssub) "(#Hownsnap & %Hsub & %Hcoh)".
    iInv OpLib_InvName as "> [Hglobinv Hprop]" "Hclose".
    iDestruct "Hglobinv" as (h' s') "(Hownglob & Hglob & %Hcoh' & %Htotal)".
    iMod (OwnGlobalSnapshot_included with "Hgi Hownglob Hownsnap") as "[Hownglob %Hsub']"; [auto|].
    iMod ("Hclose" with "[Hglob Hownglob Hprop]") as "_".
    { iModIntro.
      iSplitL "Hownglob Hglob"; [|iFrame].
      iExists h', s'. eauto with iFrame. }
    iModIntro; iPureIntro.
    apply (events_total_order_sub h h'); [|done].
    intros x [q [Hqin Hqcoh]]%Hcoh.
    assert (q ∈ s') as [p [Hpin Hpcoh]]%Hcoh'; [set_solver|].
    assert (x = p) as ->; [|done].
    apply (glob_st_coh_inj _ _ q); done.
  Qed.

  (** * Laws about local state only *)

  Ltac rewrite_lookup := repeat (
    match goal with
    | [ H1 : _ !! ?i = Some ?v1, H2 : _ !! ?i = Some ?v2 |- _ ] =>
          rewrite H1 in H2; inversion H2
    end); subst.

  Instance oplib_loc_st_timeless i s1 s2 : Timeless (oplib_loc_st_user_wrap i s1 s2).
  Proof. apply _. Qed.

  Lemma oplib_loc_st_excl i s1 s2 s1' s2' :
    oplib_loc_st_user_wrap i s1 s2 ⊢
    oplib_loc_st_user_wrap i s1' s2' -∗
    False.
  Proof.
    iIntros "Hloc1 Hloc2".
    iDestruct "Hloc1" as (? ? ? ?) "(?&%&?&?&?&?&?&Hloc1&?&?)".
    iDestruct "Hloc2" as (? ? ? ?) "(?&%&?&?&?&?&?&Hloc2&?&?)".
    rewrite_lookup.
    iDestruct (own_valid_2 with "Hloc1 Hloc2") as "%Hv".
    exfalso.
    apply pair_valid in Hv as [Hv _].
    simpl in Hv.
    apply (iffLR (frac_valid _)) in Hv.
    rewrite frac_op in Hv.
    by compute in Hv.
  Qed.

  Instance oplib_loc_snap_timeless i s1 s2 : Timeless (oplib_loc_snap_wrap i s1 s2).
  Proof. apply _. Qed.

  Instance oplib_loc_snap_pers i s1 s2 : Persistent (oplib_loc_snap_wrap i s1 s2).
  Proof. apply _. Qed.

  Lemma oplib_loc_st_own_orig i s1 s2 :
    oplib_loc_st_user_wrap i s1 s2 ⊢ ⌜∀ e, e ∈ s1 -> e.(EV_Orig) = i⌝.
  Proof.
    iIntros "Hwrap".
    iDestruct "Hwrap" as (γown γsub γcc γinv) "(_&_&_&%Horig&?&Hwrap)".
    done.
  Qed.

  Lemma oplib_loc_st_foreign_orig i s1 s2 :
    oplib_loc_st_user_wrap i s1 s2 ⊢ ⌜∀ e, e ∈ s2 -> ¬ (e.(EV_Orig) = i)⌝.
  Proof.
    iIntros "Hwrap".
    iDestruct "Hwrap" as (γown γsub γcc γinv) "(_&_&_&_&_&%Horig&_)".
    done.
  Qed.

  Lemma oplib_loc_st_lock_orig i s1 s2 :
    oplib_loc_st_lock_wrap i s1 s2 ⊢ ⌜own_orig i s1 ∧ foreign_orig i s2⌝.
  Proof.
    iIntros "Hwrap".
    iDestruct "Hwrap" as (γown γfor γinv) "(_&_&_&%Hown&%Hfor&_)".
    done.
  Qed.

  Lemma oplib_loc_snap_own_orig i s1 s2 :
    oplib_loc_snap_wrap i s1 s2 ⊢ ⌜∀ e, e ∈ s1 -> e.(EV_Orig) = i⌝.
  Proof.
    iIntros "Hwrap".
    iDestruct "Hwrap" as (γcc γinv) "(_&_&%Horig&Hwrap&?)".
    done.
  Qed.

  Lemma oplib_loc_snap_foreign_orig i s1 s2 :
    oplib_loc_snap_wrap i s1 s2 ⊢ ⌜∀ e, e ∈ s2 -> ¬ (e.(EV_Orig) = i)⌝.
  Proof.
    iIntros "Hwrap".
    iDestruct "Hwrap" as (γcc γinv) "(_&_&_&%Horig&Hwrap&?)".
    done.
  Qed.

  Lemma oplib_loc_st_take_snap i h1 h2 :
    oplib_loc_st_user_wrap i h1 h2 ⊢ oplib_loc_st_user_wrap i h1 h2 ∗ oplib_loc_snap_wrap i h1 h2.
  Proof.
    iIntros "Hloc".
    iDestruct "Hloc" as (γ1 γ2 γ3 γ4) "(% & % & % & % & Hloc)".
    iDestruct "Hloc" as "(% & % & Hown & Hfor & #Hsnap & #Hinit)".
    iSplitL "Hown Hfor".
    - iExists γ1, γ2, γ3, γ4.
      rewrite /oplib_loc_st_user.
      repeat (iSplitL ""; [done |]).
      iDestruct "Hsnap" as "(?&?&?&?)".
      iFrame. iFrame "#".
    - iExists γ3, γ4.
      auto.
  Qed.

  Lemma princ_ev_own_both γ h h' :
    own γ (● princ_ev h) -∗
    own γ (◯ princ_ev h') -∗
    ⌜cc_subseteq h' h⌝.
  Proof.
    iIntros "Hauth #Hfrag".
    iAssert (own γ ((● princ_ev h) ⋅ (◯ princ_ev h'))) with "[Hauth]" as "Hown".
    { rewrite own_op. auto. }
    iPoseProof (own_valid with "Hown") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid as [Hlt _].
    iPureIntro.
    apply principal_included. done.
  Qed.

  Lemma oplib_cc_snap_union h h1 h2 γ :
    own γ (● princ_ev h) ⊢
    own γ (◯ princ_ev h1) -∗
    own γ (◯ princ_ev h2) ==∗
    own γ (● princ_ev h) ∗ own γ (◯ princ_ev (h1 ∪ h2)).
  Proof.
    iIntros "Hauth #Hfrag1 #Hfrag2".
    iPoseProof (princ_ev_own_both with "Hauth Hfrag1") as "%Hsubset1".
    iPoseProof (princ_ev_own_both with "Hauth Hfrag2") as "%Hsubset2".
    assert (cc_subseteq (h1 ∪ h2) h) as Hunion.
    { apply cc_subseteq_union; done. }
    iMod (own_update _ _ (● (princ_ev h) ⋅ ◯ (princ_ev (h1 ∪ h2))) with "Hauth") as "Hres".
    { eapply monotone_update; done. }
    iModIntro.
    by iApply own_op.
  Qed.

  Lemma oplib_loc_snap_union (E : coPset) i (h1 h2 h1' h2' : gset (Event LogOp)) :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_loc_snap_wrap i h1 h2 -∗
    oplib_loc_snap_wrap i h1' h2' ={E}=∗
    oplib_loc_snap_wrap i (h1 ∪ h1') (h2 ∪ h2').
  Proof.
    iIntros (Hin) "[_ #Hinv] Hsnap Hsnap'".
    iDestruct "Hsnap" as (γcc γinv Hγcc Hγinv) "#Hsnap".
    iDestruct "Hsnap'" as (γcc' γinv' Hγcc' Hγinv') "#Hsnap'".
    rewrite_lookup.
    iExists γcc', γinv'.
    rewrite /oplib_loc_snap.
    iDestruct "Hsnap" as "(% & % & #Hfrag1 & #Hinvst)".
    iDestruct "Hsnap'" as "(% & % & #Hfrag2 & #Hinvst')".
    assert (own_orig i (h1 ∪ h1')) as ? by (apply own_orig_union; done).
    assert (foreign_orig i (h2 ∪ h2')) as ? by (apply foreign_orig_union; done).
    iAssert (|={ E }=> own γcc' (◯ princ_ev (h1 ∪ h1' ∪ (h2 ∪ h2'))))%I as "> #Hmono".
    { iInv OpLib_InvName as "> Hprop".
      iPoseProof (oplib_inv_lookup_acc_γcc i γcc' with "Hprop []") as "Hlookup"; [done |].
      iDestruct "Hlookup" as (h__own h__for h__forsub) "[H1 H2]".
      iDestruct "H1" as (? ? ? γcc ? ?) "(%&%&%&%&%&H1)".
      rewrite_lookup.
      iDestruct "H1" as "(?&?&?&?&?&?&?&?&?&Hauth)".
      iMod (oplib_cc_snap_union with "Hauth Hfrag1 Hfrag2") as "[Hauth Hfrag]".
      assert (h1 ∪ h2 ∪ (h1' ∪ h2') = h1 ∪ h1' ∪ (h2 ∪ h2')) as ->; [set_solver |].
      iFrame.
      iModIntro.
      iSplitR ""; [iNext | by iModIntro].
      iApply "H2".
      rewrite /oplib_loc_st_inv_wrap.
      eauto 15 with iFrame. }
    iModIntro.
    iFrame "#".
    by iPureIntro.
  Qed.

  Lemma oplib_loc_snap_loc_state_included_cc E i h1 h2 h1' h2' :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_loc_snap_wrap i h1 h2 -∗
    oplib_loc_st_user_wrap i h1' h2' ={E}=∗
      ⌜cc_subseteq (h1 ∪ h2) (h1' ∪ h2')⌝ ∗
      oplib_loc_st_user_wrap i h1' h2'.
  Proof.
    iIntros (Hin) "[_ #Hinv] #Hsnap Hloc".
    iInv OpLib_InvName as "> Hprop" "Hclose".
    rewrite /oplib_loc_snap_wrap /oplib_loc_snap.
    iDestruct "Hsnap" as (γcc γinv) "(%&%&%&%&#Hfrag&#Hinvst)".
    rewrite /oplib_loc_st_user_wrap.
    iDestruct "Hloc" as (γown γsub γcc' γinv') "(%&%&%&%&Hloc)".
    rewrite /oplib_loc_st_user.
    iDestruct "Hloc" as "(%&%&Hown&Hsub&#Hsnap&#Hinvst')".
    rewrite_lookup.
    iDestruct (oplib_inv_lookup_acc_γcc with "Hprop [//]") as
      (h__own h__for h__sub) "[Hloc_inv Hacc]".
    iDestruct "Hloc_inv" as (γown'' γfor'' γsub'' γcc'' γinv'' s) "(%&%&%&%&%&Hloc_inv)".
    rewrite_lookup.
    iDestruct "Hloc_inv" as "(%&%&%&%&%&HS&Hown'&Hfor&Hsub'&Hauth)".
    iDestruct (pair_agree with "Hown Hown'") as %->.
    iDestruct (pair_agree with "Hsub Hsub'") as %->.
    iDestruct (princ_ev_own_both with "Hauth Hfrag") as %Hsubseteq.
    iDestruct ("Hacc" with "[HS Hown Hfor Hsub' Hauth]") as "Hacc".
    { iExists _, _, _, _, _, _.
      rewrite /oplib_loc_st_inv.
      iFrame. iPureIntro.
      eauto 10. }
    iMod ("Hclose" with "[$Hacc]") as "_".
    iModIntro.
    iSplitL ""; [by iPureIntro|].
    iExists _, _, _, _.
    iFrame. iFrame "Hsnap".
    eauto 10.
  Qed.

  Lemma elem_of_subseteq' (X Y : gset (Event LogOp)) x :
    X ⊆ Y -> x ∈ X -> x ∈ Y.
  Proof.
    intros ? ?.
    set_solver.
  Qed.

  Lemma subseteq_union_mono_r (X Y Z : gset (Event LogOp)) :
    Y ⊆ Z -> X ∪ Y ⊆ X ∪ Z.
  Proof. set_solver. Qed.

  Lemma oplib_loc_snap_ext E i i' s1 s2 s1' s2' :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_loc_snap_wrap i s1 s2 -∗
    oplib_loc_snap_wrap i' s1' s2' ={E}=∗
    ⌜∀ e e', e ∈ s1 ∪ s2 -> e' ∈ s1' ∪ s2' -> e.(EV_Time) = e'.(EV_Time) -> e = e'⌝.
  Proof.
    iIntros (Hin) "[#Hrcb #Hinv] #Hsnap1 #Hsnap2".
    iInv OpLib_InvName as "> Hprop" "Hclose".
    rewrite /oplib_loc_snap_wrap /oplib_loc_snap.
    iDestruct "Hsnap1" as (γcc1 γinv1) "(%Hl1&%&%&%&#Hfrag1&#Hinvst1)".
    iDestruct "Hsnap2" as (γcc2 γinv2) "(%Hl2&%&%&%&#Hfrag2&#Hinvst2)".
    destruct (decide (i = i')) as [-> | Hne].
    - (* same node id *)
      iDestruct (oplib_inv_lookup_acc_γcc with "Hprop []") as
        (h__own h__for h__sub) "[Hloc_inv Hacc]".
      { iPureIntro.
        eapply Hl1. }
      rewrite_lookup.
      iDestruct "Hloc_inv" as (γown γfor γsub γcc γinv s) "(%&%&%&%&%&Hloc_inv)".
      rewrite_lookup.
      iDestruct "Hloc_inv" as "(%coh&%&%&%&%Hsub&HS&Hown&Hfor&Hsub&Hauth)".
      iDestruct (princ_ev_own_both with "Hauth Hfrag1") as %[Hsubseteq1 _].
      iDestruct (princ_ev_own_both with "Hauth Hfrag2") as %[Hsubseteq2 _].
      rewrite_lookup.
      own_local_opt_init γinv.
      iMod (OwnLocal_local_ext' with "Hrcb HS") as "[HS %ext]".
      { pose proof rcb_invname_diff_subseteq.
        set_solver. }
      iDestruct ("Hacc" with "[HS Hown Hfor Hsub Hauth]") as "Hacc".
      { iExists γown, γfor, γsub, γcc, γinv, s.
        rewrite /oplib_loc_st_inv.
        iFrame. iFrame "#".
        eauto with iFrame. }
      iMod ("Hclose" with "[Hacc]") as "_"; [done |].
      iModIntro.
      iPureIntro.
      intros e e' Hein He'in Hvc.
      destruct Hsub as [Hsub _].
      (* set_solver solves a bunch of the steps below, but it takes way too long
         so we do them manually so the proof compiles more efficiently *)
      assert (h__own ∪ h__sub ⊆ h__own ∪ h__for) as Hsubs.
      { clear Hsubseteq1 Hsubseteq2 Hein He'in.
        set_solver. }
      assert (e ∈ h__own ∪ h__for) as Hein2.
      { apply (iffLR (elem_of_subseteq (h__own ∪ h__sub) (h__own ∪ h__for)) Hsubs).
        apply (iffLR (elem_of_subseteq (s1 ∪ s2) (h__own ∪ h__sub)) Hsubseteq1).
        done. }
      assert (e' ∈ h__own ∪ h__for) as He'in2.
      { apply (iffLR (elem_of_subseteq (h__own ∪ h__sub) (h__own ∪ h__for)) Hsubs).
        apply (iffLR (elem_of_subseteq (s1' ∪ s2') (h__own ∪ h__sub)) Hsubseteq2).
        done. }
      apply coh in Hein2.
      apply coh in He'in2.
      destruct Hein2 as [q1 [Hin1 Hcoh1]].
      destruct He'in2 as [q2 [Hin2 Hcoh2]].
      assert ((LE_vc q1) = (LE_vc q2)) as Hvceq.
      { apply (loc_st_coh_vc e e' q1 q2); done. }
      pose proof (ext q1 q2 Hin1 Hin2 Hvceq) as Hqeq.
      subst.
      eapply loc_st_coh_inj; done.
    - (* different node id *)
      iDestruct (oplib_inv_lookup_acc2 with "Hprop") as
        (ho1 ho2 hf1 hf2 m1 m2) "(Hinv1 & Hinv2 & Hacc)".
      + eapply γ_cc_lookup_lt.
        eapply Hl1.
      + eapply γ_cc_lookup_lt.
        eapply Hl2.
      + done.
      + iDestruct "Hinv1" as (γown' γfor' γsub' γcc' γinv' s') "(%&%&%&%&%&Hinv1)".
        rewrite_lookup.
        iDestruct "Hinv1" as "(%coh1&%&%&%&%Hsub1&HS1&Hown1&Hfor1&Hsub1&Hauth1)".
        iDestruct "Hinv2" as (γown'' γfor'' γsub'' γcc'' γinv'' s'') "(%&%&%&%&%&Hinv2)".
        rewrite_lookup.
        iDestruct "Hinv2" as "(%coh2&%&%&%&%Hsub2&HS2&Hown2&Hfor2&Hsub2&Hauth2)".
        own_local_opt_init γinv'.
        own_local_opt_init γinv''.
        iMod (OwnLocal_ext' with "Hrcb HS1 HS2") as "(HS1 & HS2 & %Hext)"; [auto |].
        iDestruct (princ_ev_own_both with "Hauth1 Hfrag1") as %[Hsubseteq1 _].
        iDestruct (princ_ev_own_both with "Hauth2 Hfrag2") as %[Hsubseteq2 _].
        iDestruct ("Hacc" with "[Hown1 Hfor1 Hsub1 Hauth1 HS1] [Hown2 Hfor2 Hsub2 Hauth2 HS2]") as "Hprop".
        * iExists _, _, _, _, γinv', _.
          rewrite /oplib_loc_st_inv.
          iFrame. iFrame "#".
          eauto with iFrame.
        * iExists _, _, _, _, _, _.
          rewrite /oplib_loc_st_inv.
          iFrame. iFrame "#".
          eauto with iFrame.
        * iMod ("Hclose" with "[Hprop]") as "_".
          { iModIntro. iFrame. }
          iModIntro.
          iPureIntro.
          intros e e' Hein Hein' Hvceq.
          (* again, we need to manually run some of the steps below, because
             otherwise set_solver is too slow *)
          assert (e ∈ ho1 ∪ hf1) as Hein1.
          { destruct Hsub1 as [Hsub1 _ ].
            clear Hein' Hsubseteq2 Hsub2.
            apply (elem_of_subseteq' _ _ e Hsub1).
            apply (elem_of_subseteq' _ _ e Hsubseteq1).
            done. }
          apply coh1 in Hein1 as [q1 [Hq1in (Hop1&Horig1&Hvc1)]].
          assert (e' ∈ ho2 ∪ hf2) as Hein2.
          { destruct Hsub2 as [Hsub2 _].
            apply (elem_of_subseteq' _ _ e' Hsub2).
            apply (elem_of_subseteq' _ _ e' Hsubseteq2).
            done. }
          apply coh2 in Hein2 as [q2 [Hq2in (Hop2&Horig2&Hvc2)]].
          assert ((LE_vc q1) = (LE_vc q2)) as Hvceq'.
          { rewrite -Hvc1 -Hvc2.
            done. }
          pose proof (Hext q1 q2 Hq1in Hq2in Hvceq') as [Hpayload Horig].
          assert (EV_Op e = EV_Op e') as Heqop.
          { eapply OpLib_Op_Coh_Inj.
            + eapply Hop1.
            + rewrite Hpayload.
              eapply Hop2. }
          assert (EV_Time e = EV_Time e') as Heqvc; [auto |].
          assert (EV_Orig e = EV_Orig e') as Heqorig.
          { rewrite Horig1 Horig2 Horig. done. }
          destruct e, e'; simpl in *.
          rewrite Heqop Heqvc Heqorig.
          done.
  Qed.

  (** * Laws that connect local and global state *)

  (* TODO: take advantage of improved rcb spec *)
  Lemma oplib_loc_snap_glob_snap_provenance E i s1 s2 e :
    ↑CRDT_InvName ⊆ E ->
    e ∈ s1 ∪ s2 ->
    oplib_inv ⊢
    oplib_loc_snap_wrap i s1 s2 ={E}=∗ ∃ h, oplib_glob_snap h ∗ ⌜e ∈ h⌝.
  Proof.
    iIntros (Hname Hin) "[#Hrcbinv #Hinv] #Hwrap".
    iDestruct "Hwrap" as (γ γinv Hi Hinv) "(%Horig & %Hfor & #Hfrag & Hinvst)".
    iInv OpLib_InvName as "> Hprop" "Hclose".
    iDestruct (oplib_inv_lookup_acc with "Hprop []") as "Hres".
    { apply γ_cc_lookup_lt in Hi. done. }
    iDestruct "Hres" as (hown hfor hsub) "[Hinvwrap Hacc]".
    rewrite /oplib_loc_st_inv_wrap.
    iDestruct "Hinvwrap" as (γown γfor γsub γcc γinv' s)
                              "(%&%&%&%&%&%Hcoh&%&%&%&%Hsub&Hloc&?&?&?&Hauth)".
    rewrite_lookup.
    iDestruct (princ_ev_own_both with "Hauth Hfrag") as "%Hsub'".
    assert (e ∈ hown ∪ hfor) as [q [Hqin Hqcoh]]%Hcoh.
    { assert (e ∈ hown ∪ hsub) as ?.
      { destruct Hsub' as [Hsub' _].
        set_solver. }
      destruct Hsub as [Hsub _].
      set_solver. }
    own_local_opt_init γinv'.
    iMod (OwnLocal_provenance _ _ with "Hrcbinv Hloc") as "[Hloc Hprov]"; [auto |].
    iDestruct "Hprov" as (h) "[#Hsnap %Herase]".
    iDestruct ("Hacc" with "[-Hclose]") as "Hacc".
    { iExists _, _, _, _, _, _.
      iFrame. iFrame "#".
      eauto with iFrame. }
    iMod ("Hclose" with "Hacc") as "_".
    iModIntro.
    iExists {[ e ]}.
    iSplitL ""; [| iPureIntro; set_solver].
    iExists h, {[ erasure q ]}.
    iFrame "#"; iPureIntro.
    split; [set_solver|].
    apply glob_st_set_coh_singleton, loc_st_coh_glob_st_coh; done.
  Qed.

  Lemma oplib_loc_inv_subset_glob_internal E i hown hfor hsub hglob :
    ↑RCB_InvName ⊆ E ->
    GlobalInv ⊢
    oplib_loc_st_inv_wrap i hown hfor hsub -∗
    oplib_loc_st_lock_wrap i hown hfor -∗
    oplib_glob_st_inv hglob ={E}=∗
                                oplib_loc_st_inv_wrap i hown hfor hsub ∗
                                oplib_loc_st_lock_wrap i hown hfor ∗
                                oplib_glob_st_inv hglob ∗
                                ⌜hown ∪ hfor ⊆ hglob⌝.
  Proof.
    iIntros (Hin) "#Hrcbinv Hinv Hlock Hglob".
    iDestruct "Hinv" as (γown γfor γsub γcc γinv s) "(%&%&%&%&%&Hinv)".
    iDestruct "Hinv" as "(%Hcoh&%&%&%&%&Hloc&Howni&Hfori&Hsubi&Hcci)".
    iDestruct "Hlock" as (γown' γfor' γinv') "(%&%&%&%&%&Hownl&Hforl&#?)".
    rewrite_lookup.
    own_local_opt_init γinv'.
    iDestruct "Hglob" as (G) "(Hglob&?&%Hglobcoh&%)".
    iMod (OwnLocal_provenance _ _ with "Hrcbinv Hloc") as "[Hloc Hprov]"; [auto |].
    iDestruct "Hprov" as (h) "[#Hsnap %Herase]".
    iMod (OwnGlobalSnapshot_included with "Hrcbinv Hglob Hsnap") as "[Hglob %HG]"; [done|].
    assert (hown ∪ hfor ⊆ hglob) as Hsub.
    { intros x Hxin.
      apply Hcoh in Hxin as [q [Hqin%Herase Hqcoh]].
      assert (erasure q ∈ G) as HqG; [set_solver|].
      apply Hglobcoh in HqG as [p [Hpin Hpcoh%loc_st_coh_glob_st_coh]].
      assert (x = p) as ->; [|done].
      eapply loc_st_coh_inj; eauto. }
    iModIntro.
    iSplitL "Howni Hfori Hsubi Hcci Hloc".
    { rewrite /oplib_loc_st_inv_wrap.
      iExists γown', γfor', γsub, γcc, γinv', s.
      rewrite /oplib_loc_st_inv.
      iFrame.
      repeat (iSplitL ""; [done|]).
      iRight.
      auto with iFrame. }
    iSplitL "Hownl Hforl".
    { iExists γown', γfor', γinv'.
      rewrite /oplib_loc_st_lock.
      repeat (iSplitL ""; [done|]).
      eauto with iFrame. }
    iSplitR "".
    { rewrite /oplib_glob_st_inv.
      iExists G.
      auto with iFrame. }
    done.
  Qed.

  Lemma oplib_loc_st_glob_snap_provenance E i s1 s2 h :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_loc_st_user_wrap i s1 s2 -∗
    oplib_glob_snap h ={E}=∗
    oplib_loc_st_user_wrap i s1 s2 ∗ ⌜∀ e, e ∈ h -> e.(EV_Orig) = i -> e ∈ s1⌝.
  Proof.
    iIntros (Hinv) "[Hinv Hrcbinv] Hloc #Hglobsnap".
    iInv OpLib_InvName as "> Hprop" "Hclose".
    iDestruct "Hloc" as (γown γsub γcc γinv) "(%&%&%&%&%&%&Hown&Hsub&#Hsnap&#Hinvst)".
    iDestruct (oplib_inv_lookup_acc with "Hprop []") as "Hres".
    { iPureIntro; eapply γ_cc_lookup_lt. eauto. }
    iDestruct "Hres" as (hown hfor hsub) "[Hinvwrap Hacc]".
    iDestruct "Hinvwrap" as (γown' γfor' γsub' γcc' γinv' s)
                              "(%&%&%&%&%&%Hcoh&%&%Hfor&%&%Hsub&Hloc&Hown'&Hfor'&Hsub'&Hauth)".
    rewrite_lookup.
    iDestruct "Hglobsnap" as (s__super s__sub) "(#Hgsnap & %Hgsub & %Hgcoh)".
    own_local_opt_init γinv'.
    iMod (OwnGlobalSnapshot_provenance' with "Hinv Hgsnap Hloc") as "[Hloc %Hprov]";
      [auto |].
    iDestruct (pair_agree with "Hown Hown'") as %->.
    iDestruct ("Hacc" with "[Hloc Hown' Hfor' Hsub' Hauth]") as "Hacc".
    { rewrite /oplib_loc_st_inv_wrap.
      rewrite /oplib_loc_st_inv.
      iExists γown', γfor', γsub', γcc', γinv'.
      iFrame. iFrame "#".
      eauto with iFrame. }
    iMod ("Hclose" with "Hacc") as "_".
    iModIntro.
    iSplitR "".
    - iExists _, _, _.
      eauto 10 with iFrame.
    - iPureIntro.
      intros e Hin Heorig.
      apply Hgcoh in Hin.
      destruct Hin as [q [Hqsub Hqcoh]].
      assert (q ∈ s__super) as Hqsup by set_solver.
      apply Hprov in Hqsup; last first.
      { apply glob_st_coh_orig in Hqcoh as <-.
        done. }
      destruct Hqsup as [r [Hrins Hrerase]].
      apply Hcoh in Hrins.
      destruct Hrins as (p & Hpin & Hpcoh).
      assert (p ∈ hown) as Hpown.
      { apply elem_of_union in Hpin as [Hl | Hr]; [done |].
        exfalso.
        apply Hfor in Hr.
        apply Hr.
        destruct Hpcoh as (_ & -> & _).
        rewrite <- erasure_origin.
        rewrite Hrerase.
        apply glob_st_coh_orig in Hqcoh.
        subst; done. }
      apply loc_st_coh_glob_st_coh in Hpcoh.
      rewrite Hrerase in Hpcoh.
      assert (e = p) as ->; [ | done].
      eapply glob_st_coh_inj; eauto.
  Qed.

  Lemma oplib_loc_state_glob_snap_causality E i s1 s2 h :
    ↑CRDT_InvName ⊆ E ->
    oplib_inv ⊢
    oplib_loc_st_user_wrap i s1 s2 -∗
    oplib_glob_snap h ={E}=∗
      oplib_loc_st_user_wrap i s1 s2 ∗
      ⌜∀ a e, a ∈ h → e ∈ s1 ∪ s2 → a <_t e → a ∈ s1 ∪ s2⌝.
  Proof.
    iIntros (Hinv) "[Hinv Hrcbinv] Hloc #Hglobsnap".
    iInv OpLib_InvName as "> Hprop" "Hclose".
    iDestruct "Hloc" as (γown γsub γcc γinv) "(%&%&%&%&%&%&Hown&Hsub&#Hsnap&#Hinvst)".
    iDestruct (oplib_inv_lookup_acc with "Hprop []") as "Hres".
    { iPureIntro; eapply γ_cc_lookup_lt. eauto. }
    iDestruct "Hres" as (hown hfor hsub) "[Hinvwrap Hacc]".
    iDestruct "Hinvwrap" as (γown' γfor' γsub' γcc' γinv' s)
                              "(%&%&%&%&%&%Hcoh&%Hown&%Hfor&%&%Hsub&Hloc&Hown'&Hfor'&Hsub'&Hauth)".
    rewrite_lookup.
    own_local_opt_init γinv'.
    iDestruct "Hglobsnap" as (ssup ssub) "(#Hglobsnap&%Hsubset&%Hglobcoh)".
    iMod (Causality' with "Hinv Hloc Hglobsnap") as "[Hloc %Hcaus]"; [auto|].
    iDestruct (pair_agree with "Hown Hown'") as %->.
    iDestruct (pair_agree with "Hsub Hsub'") as %->.
    iDestruct ("Hacc" with "[Hloc Hown' Hfor' Hsub' Hauth]") as "Hacc".
    { rewrite /oplib_loc_st_inv_wrap.
      rewrite /oplib_loc_st_inv.
      iExists γown', γfor', γsub', γcc', γinv', _.
      iFrame. iFrame "#".
      eauto with iFrame. }
    iMod ("Hclose" with "Hacc") as "_".
    iModIntro.
    iSplitR "".
    - iExists _, _, _.
      eauto 10 with iFrame.
    - iPureIntro.
      intros a e [q [Hqin Hqcoh]]%Hglobcoh Hein Hle.
      assert (q ∈ ssup) as Hqin' by set_solver.
      destruct Hsub as [Hsub Hcc].
      assert (e ∈ hown ∪ hfor) as Hein' by set_solver.
      apply Hcoh in Hein'.
      destruct Hein' as [q' [Hq'in Hq'coh]].
      assert (time.vector_clock_lt (GE_vc q) (LE_vc q')) as Hlt.
      { destruct Hqcoh as (Hop&Horig&<-).
        destruct Hq'coh as (Hop'&Horig'&<-).
        done. }
      pose proof (Hcaus q q' Hqin' Hq'in Hlt) as [e' [He'in He'erase]].
      apply Hcoh in He'in.
      destruct He'in as [p [Hpin Hpcoh]].
      assert (p = a) as ->.
      { apply loc_st_coh_glob_st_coh in Hpcoh.
        rewrite He'erase in Hpcoh.
        eapply glob_st_coh_inj; eauto. }
      apply TM_lt_TM_le in Hle.
      apply (Hcc a e); eauto with set_solver.
  Qed.

  Lemma oplib_loc_snap_EV_Orig E i s1 s2 :
   ↑CRDT_InvName ⊆ E
   → oplib_inv -∗
     oplib_loc_snap_wrap i s1 s2 ={E}=∗
     ⌜∀ e : Event LogOp, e ∈ s1 ∪ s2 → (EV_Orig e < length CRDT_Addresses)%Z⌝.
  Proof.
    iIntros (Hin) "[#Hrcb #Hinv] #Hsnap1".
    iInv OpLib_InvName as "> Hprop" "Hclose".
    rewrite /oplib_loc_snap_wrap /oplib_loc_snap.
    iDestruct "Hsnap1"
      as (γcc1 γinv1) "(%Hl1&%Hl2&%Hl3&%Hl4&#Hfrag1&#Hinvst1)".
    (*
    iPureIntro.
    intros e [He|He]%elem_of_union.
    - apply Hl3 in He as ->.
      assert (i < length CRDT_Addresses).
      { by eapply γ_cc_lookup_lt. }
      by apply Nat2Z.inj_lt.
    - apply Hl4 in He.
      assert (i < length CRDT_Addresses).
      { by eapply γ_cc_lookup_lt. }
      by apply Nat2Z.inj_lt. *)
  Admitted.

  Global Instance oplib_res : CRDT_Res_Mixin Mdl Σ LogOp := {
    GlobInv := oplib_inv;
    GlobInv_persistent := oplib_inv_persistent;
    GlobState := oplib_glob_st_user;
    GlobState_Exclusive := oplib_glob_st_excl;
    GlobState_Timeless := oplib_glob_st_timeless;
    GlobSnap := oplib_glob_snap;
    GlobSnap_Timeless := oplib_glob_snap_timeless;
    GlobSnap_Persistent := oplib_glob_snap_pers;
    LocState := oplib_loc_st_user_wrap;
    LocState_Timeless := oplib_loc_st_timeless;
    LocState_Exclusive := oplib_loc_st_excl;
    LocSnap := oplib_loc_snap_wrap;
    LocSnap_Timeless := oplib_loc_snap_timeless;
    LocSnap_Persistent := oplib_loc_snap_pers;
    GlobState_TakeSnap := oplib_glob_st_take_snap;
    GlobSnap_Union := oplib_glob_snap_union;
    GlobSnap_GlobState_Included := oplib_glob_snap_included;
    GlobSnap_Ext := oplib_glob_snap_ext;
    GlobSnap_TotalOrder := oplib_glob_snap_total;
    LocState_OwnOrig := oplib_loc_st_own_orig;
    LocState_ForeignOrig := oplib_loc_st_foreign_orig;
    LocSnap_OwnOrig := oplib_loc_snap_own_orig;
    LocSnap_ForeignOrig := oplib_loc_snap_foreign_orig;
    LocState_TakeSnap := oplib_loc_st_take_snap;
    LocSnap_Union := oplib_loc_snap_union;
    LocSnap_LocState_Included_CC := oplib_loc_snap_loc_state_included_cc;
    LocSnap_Ext := oplib_loc_snap_ext;
    LocSnap_EV_Orig := oplib_loc_snap_EV_Orig;
    LocSnap_GlobSnap_Provenance := oplib_loc_snap_glob_snap_provenance;
    LocState_GlobSnap_Provenance := oplib_loc_st_glob_snap_provenance;
    LocState_GlobSnap_Causality := oplib_loc_state_glob_snap_causality
  }.

  (** * Updating resources *)

  Lemma loc_st_user_inv_agree i γown γfor γsub γcc γinv hown hfor hsub s hown' hsub' :
    oplib_loc_st_inv γown γfor γsub γcc γinv i hown hfor hsub s ⊢
    oplib_loc_st_user γown γsub γcc γinv i hown' hsub' -∗
    ⌜hown = hown' ∧ hsub = hsub'⌝.
  Proof.
    iIntros "Hinv Huser".
    iDestruct "Hinv" as "(_&_&_&_&_&_&Hown&_&Hsub&_)".
    iDestruct "Huser" as "(_&_&Hown'&Hsub'&_)".
    iDestruct (pair_agree with "Hown Hown'") as "%".
    iDestruct (pair_agree with "Hsub Hsub'") as "%".
    done.
  Qed.

  Lemma loc_st_user_inv_wrap_agree i hown hfor hsub hown' hsub' :
    oplib_loc_st_inv_wrap i hown hfor hsub ⊢
    oplib_loc_st_user_wrap i hown' hsub' -∗
    ⌜hown = hown' ∧ hsub = hsub'⌝.
  Proof.
    iIntros "Hinv Huser".
    iDestruct "Hinv" as (? ? ? ? ? ?) "(%&%&%&%&%&Hinv)".
    iDestruct "Huser" as (? ? ? ?) "(%&%&%&%&Huser)".
    rewrite_lookup.
    iApply (loc_st_user_inv_agree with "Hinv Huser").
  Qed.

  Lemma loc_st_lock_inv_agree i γown γfor γsub γcc γinv hown hfor hsub s hown' hfor' :
    oplib_loc_st_inv γown γfor γsub γcc γinv i hown hfor hsub s ⊢
    oplib_loc_st_lock γown γfor γinv i hown' hfor' -∗
    ⌜hown = hown' ∧ hfor = hfor'⌝.
  Proof.
    iIntros "Hinv Hlock".
    iDestruct "Hinv" as "(_&_&_&_&_&_&Hown&Hfor&_&_)".
    iDestruct "Hlock" as "(_&_&Hown'&Hfor'&_)".
    iDestruct (pair_agree with "Hown Hown'") as "%".
    iDestruct (pair_agree with "Hfor Hfor'") as "%".
    done.
  Qed.

  Lemma loc_st_lock_inv_wrap_agree i hown hfor hsub hown' hfor' :
    oplib_loc_st_inv_wrap i hown hfor hsub ⊢
    oplib_loc_st_lock_wrap i hown' hfor' -∗
    ⌜hown = hown' ∧ hfor = hfor'⌝.
  Proof.
    iIntros "Hinv Hlock".
    iDestruct "Hinv" as (? ? ? ? ? ?) "(%&%&%&%&%&Hinv)".
    iDestruct "Hlock" as (? ? ?) "(%&%&%&Hlock)".
    rewrite_lookup.
    iApply (loc_st_lock_inv_agree with "Hinv Hlock").
  Qed.

  Lemma loc_st_user_inv_sub_update γown γfor γsub γcc γinv i hown hfor hsub s :
    oplib_loc_st_inv γown γfor γsub γcc γinv i hown hfor hsub s ⊢
    oplib_loc_st_user γown γsub γcc γinv i hown hsub ==∗
      oplib_loc_st_inv γown γfor γsub γcc γinv i hown hfor hfor s ∗
      oplib_loc_st_user γown γsub γcc γinv i hown hfor.
  Proof.
    iIntros "Hinv Huser".
    iDestruct "Hinv" as "(%&%&%&%&%&Hloc&Hown&Hfor&Hsub&Hprinc)".
    iDestruct "Huser" as "(%&%&Hown'&Hsub'&#Hsnap&#Hinvst)".
    iAssert (|==> own γsub ((1/3)%Qp, to_agree hfor) ∗
                  own γsub ((2/3)%Qp, to_agree hfor))%I with "[Hsub Hsub']" as
      "> [Hsub Hsub']".
    { rewrite -own_op.
      iApply (own_update_2 with "Hsub Hsub'").
      rewrite -pair_op.
      rewrite frac_op.
      assert (1 / 3 + 2 / 3 = 1)%Qp as ->.
      { compute_done. }
      apply cmra_update_exclusive.
      apply pair_valid; split; simpl.
      - apply frac_valid.
        compute; done.
      - rewrite to_agree_op_valid.
        done.
    }
    iAssert (|==> own γcc (● princ_ev (hown ∪ hfor)) ∗
                  own γcc (◯ princ_ev (hown ∪ hfor)))%I with "[Hprinc]" as
      "> [Hprinc #Hfrag]".
    { rewrite -own_op.
      iApply (own_update with "Hprinc").
      apply monotone_update; [assumption | apply PreOrder_Reflexive]. }
    iModIntro.
    iSplitL "Hloc Hown Hfor Hprinc Hsub".
    - rewrite /oplib_loc_st_inv.
      iFrame. eauto.
    - iFrame. iFrame "#".
      eauto.
  Qed.

  Lemma loc_st_user_inv_sub_wrap_update i hown hfor hsub :
    oplib_loc_st_inv_wrap i hown hfor hsub ⊢
    oplib_loc_st_user_wrap i hown hsub ==∗
      oplib_loc_st_inv_wrap i hown hfor hfor ∗
      oplib_loc_st_user_wrap i hown hfor.
  Proof.
    iIntros "Hinv Huser".
    iDestruct "Hinv" as (? ? ? ? ? ?) "(%&%&%&%&%&Hinv)".
    iDestruct "Huser" as (? ? ? ?) "(%&%&%&%&Huser)".
    rewrite_lookup.
    iMod (loc_st_user_inv_sub_update with "Hinv Huser") as "[Hinv Huser]".
    iModIntro.
    iSplitL "Hinv".
    - iExists _, _, _, _.
      eauto with iFrame.
    - iExists _, _, _.
      eauto with iFrame.
  Qed.

  Lemma loc_st_inv_subseteq i hown hfor hsub :
    oplib_loc_st_inv_wrap i hown hfor hsub ⊢ ⌜hsub ⊆ hfor⌝.
  Proof.
    iIntros "Hinv".
    iDestruct "Hinv" as (? ? ? ? ? ?) "(%&%&%&%&%&Hinv)".
    iDestruct "Hinv" as "(%&%Horigown&%&%Horigsub&%Hsub&_&_&_&H&_)".
    iPureIntro.
    destruct Hsub as [Hsub _].
    intros x Hin.
    assert (x ∈ hown ∪ hfor) as [Hl | Hr]%elem_of_union; [set_solver | | done].
    apply Horigsub in Hin.
    apply Horigown in Hl.
    exfalso.
    apply Hin. done.
  Qed.

  (* Extending the local state *)

  Definition to_event (op : LogOp) (msg : le) :=
    Build_Event LogOp op (LE_origin msg) (LE_vc msg).

  Lemma to_event_coh op msg : OpLib_Op_Coh op (LE_payload msg) -> loc_st_coh (to_event op msg) msg.
  Proof.
    intros Hopcoh.
    rewrite /to_event.
    repeat split; auto.
  Qed.

  Lemma loc_st_set_coh_union s ls e m :
    loc_st_set_coh s ls -> loc_st_coh e m -> loc_st_set_coh (s ∪ {[ e ]}) (ls ∪ {[m]}).
  Proof.
    intros Hset Helem.
    split.
    - intros p [Hl | ->%elem_of_singleton]%elem_of_union.
      + apply Hset in Hl.
        destruct Hl as [q [? ? ]].
        exists q; auto with set_solver.
      + exists m; auto with set_solver.
    - intros q [Hl | ->%elem_of_singleton]%elem_of_union.
      + apply Hset in Hl.
        destruct Hl as [p [? ?]].
        exists p; auto with set_solver.
      + exists e; auto with set_solver.
  Qed.

  Definition lstate_ext (ls : lstate) :=
    ∀ m m', m ∈ ls -> m' ∈ ls -> (LE_vc m) = (LE_vc m') -> m = m'.

  Definition gstate_ext (ls : gstate) :=
    ∀ m m', m ∈ ls -> m' ∈ ls -> (GE_vc m) = (GE_vc m') -> m = m'.

  Lemma loc_st_coh_vc' e m m' : loc_st_coh e m -> loc_st_coh e m' -> (LE_vc m) = (LE_vc m').
  Proof.
    eapply loc_st_coh_vc; eauto.
  Qed.

  Lemma lstate_events_ext s ls : loc_st_set_coh s ls -> lstate_ext ls -> events_ext s.
  Proof.
    intros Hcoh Hext.
    intros e e' Hein Hein' Hvceq.
    apply Hcoh in Hein.
    apply Hcoh in Hein'.
    destruct Hein as [q [Hqin Hqcoh]].
    destruct Hein' as [q' [Hqin' Hqcoh']].
    assert ((LE_vc q) = (LE_vc q')) as ?.
    { destruct Hqcoh as (_&_&<-).
      destruct Hqcoh' as (_&_&<-).
      done. }
    assert (q = q') as ->.
    { apply Hext; auto. }
    eapply loc_st_coh_inj; eauto.
  Qed.

  Lemma gstate_events_ext s ls : glob_st_set_coh s ls -> gstate_ext ls -> events_ext s.
  Proof.
    intros Hcoh Hext.
    intros e e' Hein Hein' Hvceq.
    apply Hcoh in Hein.
    apply Hcoh in Hein'.
    destruct Hein as [q [Hqin Hqcoh]].
    destruct Hein' as [q' [Hqin' Hqcoh']].
    assert ((GE_vc q) = (GE_vc q')) as ?.
    { destruct Hqcoh as (_&_&<-).
      destruct Hqcoh' as (_&_&<-).
      done. }
    assert (q = q') as ->.
    { apply Hext; auto. }
    eapply glob_st_coh_inj; eauto.
  Qed.

  Lemma loc_st_set_coh_not_elem s ls e m :
    loc_st_set_coh s ls -> loc_st_coh e m -> lstate_ext (ls ∪ {[ m ]}) -> m ∉ ls -> e ∉ s.
  Proof.
    intros Hset Hcoh Hext Hnotin Hcontra.
    apply Hnotin.
    apply Hset in Hcontra.
    destruct Hcontra as [q [Hin Hcoh']].
    pose proof (loc_st_coh_vc' _ _ _ Hcoh Hcoh') as Hvceq.
    assert (m = q) as ->.
    { apply Hext; auto with set_solver. }
    done.
  Qed.

  Lemma glob_st_coh_vc e m m' :
    glob_st_coh e m -> glob_st_coh e m' -> (GE_vc m) = (GE_vc m').
  Proof.
    intros (_&_&<-) (_&_&<-).
    done.
  Qed.

  Lemma glob_st_set_coh_not_elem s ls e m :
    glob_st_set_coh s ls -> glob_st_coh e m -> gstate_ext (ls ∪ {[ m ]}) -> m ∉ ls -> e ∉ s.
  Proof.
    intros Hset Hcoh Hext Hnotin Hcontra.
    apply Hnotin.
    apply Hset in Hcontra.
    destruct Hcontra as [q [Hin Hcoh']].
    pose proof (glob_st_coh_vc _ _ _ Hcoh Hcoh') as Hvceq.
    assert (m = q) as ->.
    { apply Hext; auto with set_solver. }
    done.
  Qed.

  Lemma coh_vc p q : loc_st_coh p q -> (EV_Time p) = (LE_vc q).
  Proof. intros (?&?&?); auto. Qed.

  Lemma loc_st_coh_maximum s ls e m :
    loc_st_set_coh s ls ->
    loc_st_coh e m ->
    lstate_ext ls ->
    e ∈ s ->
    m ∈ ls ->
    compute_maximum LE_vc ls = Some m ->
    Maximum s = Some e.
  Proof.
    intros Hsetcoh Hcoh Hext Hein Hmin Hmaxm.
    pose proof (lstate_events_ext _ _ Hsetcoh Hext) as Hext'.
    apply (Maximum_correct s Hext').
    split; [done |].
    intros t Htin Htne.
    apply Hsetcoh in Htin.
    destruct Htin as [q [Hqin Hqcoh]].
    apply compute_maximum_correct in Hmaxm; last first.
    { apply Hext. }
    destruct Hmaxm as [_ Hmaxm].
    apply Hmaxm in Hqin; last first.
    { intros ->.
      apply Htne.
      eapply loc_st_coh_inj; eauto. }
    simpl.
    rewrite /time /Event_Timed.
    apply coh_vc in Hcoh as ->.
    apply coh_vc in Hqcoh as ->.
    done.
  Qed.

  Lemma loc_st_coh_maximal s ls e m :
    loc_st_set_coh s ls ->
    loc_st_coh e m ->
    e ∈ s ->
    m ∈ ls ->
    m ∈ compute_maximals LE_vc ls ->
    e ∈ Maximals s.
  Proof.
    intros Hsetcoh Hcoh Hein Hmin Hmaxm.
    apply (Maximals_correct s).
    split; [done |].
    intros t Htin Htlt.
    apply Hsetcoh in Htin.
    destruct Htin as [q [Hqin Hqcoh]].
    apply compute_maximals_correct in Hmaxm; last first.
    destruct Hmaxm as [_ Hmaxm].
    apply Hmaxm in Hqin; last first.
    apply Hqin.
    assert (LE_vc m = time e) as ->.
    { rewrite /time.
      rewrite /Event_Timed.
      destruct Hcoh as (?&?&->).
      reflexivity. }
    assert (LE_vc q = time t) as ->.
    { rewrite /time.
      rewrite /Event_Timed.
      destruct Hqcoh as (?&?&->).
      reflexivity. }
    done.
  Qed.

  Lemma glob_st_coh_maximal s ls e m :
    glob_st_set_coh s ls ->
    glob_st_coh e m ->
    e ∈ s ->
    m ∈ ls ->
    m ∈ compute_maximals GE_vc ls ->
    e ∈ Maximals s.
  Proof.
    intros Hsetcoh Hcoh Hein Hmin Hmaxm.
    apply (Maximals_correct s).
    split; [done |].
    intros t Htin Htlt.
    apply Hsetcoh in Htin.
    destruct Htin as [q [Hqin Hqcoh]].
    apply compute_maximals_correct in Hmaxm; last first.
    destruct Hmaxm as [_ Hmaxm].
    apply Hmaxm in Hqin; last first.
    apply Hqin.
    assert (GE_vc m = time e) as ->.
    { rewrite /time /Event_Timed.
      destruct Hcoh as (?&?&->).
      reflexivity. }
    assert (GE_vc q = time t) as ->.
    { rewrite /time /Event_Timed.
      destruct Hqcoh as (?&?&->).
      reflexivity. }
    done.
  Qed.

  Lemma oplib_loc_st_inv_wrap_pure i hown hfor hsub :
    oplib_loc_st_inv_wrap i hown hfor hsub ⊢
      ⌜own_orig i hown ∧ foreign_orig i hfor ∧ foreign_orig i hsub ∧ cc_subseteq (hown ∪ hsub) (hown ∪ hfor)⌝.
  Proof.
    iIntros "Hinv".
    iDestruct "Hinv" as (? ? ? ? ? ?) "(%&%&%&%&%&Hinv)".
    iDestruct "Hinv" as "(%&%&%&%&%&_)".
    done.
  Qed.

  Lemma own_orig_singleton i e :
    e.(EV_Orig) = i -> own_orig i {[ e ]}.
  Proof.
    intros Heq q ->%elem_of_singleton.
    done.
  Qed.

  Lemma foreign_orig_singleton i e :
    e.(EV_Orig) ≠ i -> foreign_orig i {[ e ]}.
  Proof.
    intros Hneq q ->%elem_of_singleton.
    done.
  Qed.


  Lemma cc_subseteq_maximal (s1 s2 : gset (Event LogOp)) e :
    cc_subseteq s1 s2 -> e ∈ Maximals (s2 ∪ {[ e ]}) -> events_ext (s2 ∪ {[e]}) -> cc_subseteq s1 (s2 ∪ {[ e ]}).
  Proof.
    intros [Hsub Hcc] Hmax Hext.
    split; [set_solver | ].
    intros e1 e2 Hin1 Hin2 Hlt Hin'.
    apply elem_of_union in Hin1 as [Hl | ->%elem_of_singleton].
    - eapply (Hcc e1 e2); eauto.
    - apply TM_le_eq_or_lt in Hlt as [Hlt | Heq].
      + assert (e = e2) as ->; [|done].
        apply Hext; auto with set_solver.
      + exfalso.
        apply Maximals_correct in Hmax.
        apply Hmax in Hin2.
        apply Hin2.
        done.
  Qed.

  Hint Resolve own_orig_singleton : core.
  Hint Resolve loc_st_coh_glob_st_coh : core.

  Lemma  oplib_loc_st_lock_wrap_inv_st i hown hfor :
    oplib_loc_st_lock_wrap i hown hfor ⊢
      ∃ γ, oplib_loc_st_lock_wrap i hown hfor ∗
           ⌜γ_inv !! i = Some γ⌝ ∗
           own γ inv_init.
  Proof.
    iIntros "Hlock".
    iDestruct "Hlock" as (γown γfor γinv) "(%&%&%&%&%&Hown&Hfor&#Hinvst)".
    iExists γinv.
    iFrame "#".
    iSplitR "";[ | done].
    iExists _, _, _.
    rewrite /oplib_loc_st_lock.
    iFrame. iFrame "#".
    eauto.
  Qed.

  Lemma update_own E i hglob hown hfor hsub :
    ↑RCB_InvName ⊆ E ->
    hown ∪ hfor ⊆ hglob ->
    GlobalInv ⊢
    oplib_glob_st_user hglob -∗
    oplib_glob_st_inv hglob -∗
    oplib_loc_st_user_wrap i hown hsub -∗
    oplib_loc_st_lock_wrap i hown hfor -∗
    oplib_loc_st_inv_wrap i hown hfor hsub -∗
    (∃ h s,
        OwnGlobal h ∗
        OwnLocal i s ∗
        ⌜loc_st_set_coh (hown ∪ hfor) s⌝ ∗
        (∀ a op,
              ⌜OpLib_Op_Coh op (LE_payload a)⌝ ∗
              ⌜(LE_origin a) = i⌝ ∗
              ⌜a ∉ s⌝ ∗
              ⌜erasure a ∉ h⌝ ∗
              ⌜erasure a ∈ compute_maximals GE_vc (h ∪ {[ erasure a ]})⌝ ∗
              ⌜compute_maximum LE_vc (s ∪ {[ a ]}) = Some a⌝ ∗
              ⌜lstate_ext (s ∪ {[ a ]})⌝ ∗
              ⌜gstate_ext (h ∪ {[erasure a]})⌝ ∗
              OwnGlobal (h ∪ {[ erasure a ]}) ∗
              OwnLocal i (s ∪ {[ a ]}) ={E}=∗
              ∃ (e : Event LogOp),
                ⌜loc_st_coh e a⌝ ∗
                 ⌜e ∉ hglob⌝ ∗
                 ⌜e ∉ hown⌝ ∗
                 ⌜Maximum (hown ∪ {[e]} ∪ hfor) = Some e⌝ ∗
                 ⌜e ∈ Maximals (hglob ∪ {[ e ]})⌝ ∗
                 ⌜events_total_order (hown ∪ {[e]} ∪ hfor)⌝ ∗
                 oplib_glob_st_inv (hglob ∪ {[ e ]}) ∗
                 oplib_glob_st_user (hglob ∪ {[ e ]}) ∗
                 oplib_loc_st_user_wrap i (hown ∪ {[e]}) hfor ∗
                 oplib_loc_st_lock_wrap i (hown ∪ {[e]}) hfor ∗
                 oplib_loc_st_inv_wrap i (hown ∪ {[e]}) hfor hfor)).
  Proof.
    iIntros (Hinvin Hlocglob) "#Hrcbinv Hglobu Hglobi Huser Hlock Hinv".
    rewrite /oplib_loc_st_user_wrap /oplib_loc_st_user.
    rewrite /oplib_loc_st_lock_wrap /oplib_loc_st_lock.
    rewrite /oplib_loc_st_inv_wrap /oplib_loc_st_inv.
    iDestruct "Hglobi" as (s) "(Hglob & Hglobi & %Hglobcoh & %Htotal)".
    iDestruct "Hinv" as (γown γfor γsub γcc γinv s') "(%&%&%&%&%&%Hcoh&%Hownorig&%Hfor1&%Hfor2&%Hsub&Hloc&Hown&Hfor1&Hfor2&Hcc)".
    iExists s, s'.
    iFrame "Hglob".
    iDestruct (oplib_loc_st_lock_wrap_inv_st with "Hlock") as (γinv') "(Hlock&%&#Hinvinit)".
    rewrite_lookup.
    own_local_opt_init γinv'.
    iFrame "Hloc".
    iSplitL ""; [by iPureIntro|].
    iIntros (a op) "(%Hncoh&%Hnorig&%Hnotin&%Herasenot&%Hmaximal&%Hmaximum&%Hlext&%Hgext&Hglob&Hloc)".
    iExists (to_event op a).
    iDestruct "Huser" as (γown0 γsub0 γcc0 γinv0) "(%&%&%&%&%&%Hufor&Huown&Husub&#Husnap&#Hinvinit')".
    iDestruct "Hlock" as (γown1 γfor1 γinv1) "(%&%&%&%Hlorig&%Hlfor&Hlown&Hlfor&#Hinvinit'')".
    rewrite_lookup.
    iDestruct (User_Snapshot with "Hglob") as "[Hglob #Hglobsnap]".
    iMod (OwnGlobalSnapshot_provenance' with "Hrcbinv Hglobsnap Hloc") as "[Hloc %Hprov]"; [done|].
    set hown' := hown ∪ {[ to_event op a ]}.
    iAssert (|==> (own γown1 ((1 / 3)%Qp, to_agree hown')) ∗
                  (own γown1 ((1 / 3)%Qp
                               , to_agree hown')) ∗
                  (own γown1 ((1 / 3)%Qp, to_agree hown')))%I with "[Huown Hlown Hown]" as "> (Huown & Hlown & Hiown)".
    { do 2 rewrite -own_op.
      assert ((1/3 + 1/3 + 1/3)%Qp = 1%Qp) as Heq.
      { compute_done. }
      iApply (own_update_3 with "Huown Hlown Hown").
      do 2 rewrite -pair_op.
      simpl.
      do 3 rewrite frac_op.
      rewrite Heq.
      apply cmra_update_exclusive.
      apply pair_valid; split.
      - apply frac_valid.
        assert ((1/3 + (1/3 + 1/3))%Qp = 1%Qp) as ->.
        { compute_done. }
        done.
      - do 2 rewrite agree_idemp.
        done.
    }
    iAssert (|==> (own γsub0 ((2 / 3)%Qp, to_agree hfor)) ∗
                  (own γsub0 ((1 / 3)%Qp, to_agree hfor)))%I with "[Husub Hfor2]" as "> [Husub Hfor2]".
    { rewrite -own_op.
      iApply (own_update_2 with "Husub Hfor2").
      do 2 rewrite -pair_op.
      rewrite frac_op.
      assert ((2/3 + 1/3)%Qp = 1%Qp) as ->; [compute_done |].
      apply cmra_update_exclusive.
      apply pair_valid; split.
      - apply frac_valid. done.
      - apply to_agree_op_valid. done. }
    iAssert (|==> (own γcc0 (● princ_ev (hown' ∪ hfor))) ∗
                  (own γcc0 (◯ princ_ev (hown' ∪ hfor))))%I with "[Hcc]" as "> [Hcc #Hsnap]".
    { rewrite -own_op.
      iApply (own_update with "Hcc").
      apply monotone_update; [ | apply reflexivity].
      assert (hown' ∪ hfor = (hown ∪ hfor) ∪ {[ to_event op a ]}) as ->.
      { set_solver. }
      apply cc_subseteq_maximal; [done | |]; last first.
      { eapply lstate_events_ext.
        - eapply loc_st_set_coh_union; [done |].
          eapply to_event_coh; done.
        - done. }
      eapply loc_st_coh_maximal.
      - eapply loc_st_set_coh_union; eauto using to_event_coh.
      - eapply to_event_coh; done.
      - set_solver.
      - set_solver.
      - apply compute_maximals_correct.
        apply (compute_maximum_correct _ _ Hlext) in Hmaximum.
        assert (@maximal _ _ _ _ LE_vc a (s' ∪ {[a]})) as Hres.
        { apply is_maximum_maximal.
          done. }
        apply Hres.
    }
    rewrite /oplib_glob_st_user.
    iDestruct (pair_update _ _ _ _ (hglob ∪ {[ to_event op a ]}) with "Hglobu Hglobi") as "> [Hglobu Hglobi]".
    { compute_done. }
    iModIntro.
    assert (loc_st_coh (to_event op a) a) as Hacoh.
    { rewrite /loc_st_coh.
      simpl.
      auto. }
    iSplitL ""; [done |].
    iSplitL "".
    { iPureIntro.
      eapply glob_st_set_coh_not_elem; eauto.
      apply loc_st_coh_glob_st_coh; done. }
    iSplitL "".
    { iPureIntro.
      assert (to_event op a ∉ (hown ∪ hfor)) as ?; [ | set_solver].
      eapply loc_st_set_coh_not_elem; eauto. }
    assert (loc_st_set_coh (hown' ∪ hfor) (s' ∪ {[a]})) as Hsetcoh.
    {  assert (hown' ∪ hfor = hown ∪ hfor ∪ {[ to_event op a ]}) as ->.
        { subst hown'.
          set_solver. }
        eapply loc_st_set_coh_union; eauto. }
    iSplitL "".
    { iPureIntro.
      eapply loc_st_coh_maximum; eauto.
      - subst hown'.
        set_solver.
      - set_solver. }
    iSplitL "".
    { iPureIntro.
      assert (glob_st_set_coh (hglob ∪ {[to_event op a]}) (s ∪ {[erasure a]})) as Hglobcoh'.
      { apply glob_st_set_coh_union; auto.
        apply glob_st_set_coh_singleton.
        apply loc_st_coh_glob_st_coh.
        done. }
      eapply glob_st_coh_maximal; auto.
      - eapply Hglobcoh'.
      - assert (glob_st_coh (to_event op a) (erasure a)) as ?.
        { apply loc_st_coh_glob_st_coh. done. }
        eassumption.
      - set_solver.
      - set_solver.
      - auto. }
    assert (events_total_order (hglob ∪ {[to_event op a]})) as Htotal'.
    { intros e e' [Hel | ->%elem_of_singleton]%elem_of_union [Hel' | ->%elem_of_singleton]%elem_of_union Hne Horigeg.
        + by apply Htotal.
        + left.
          eapply loc_st_coh_maximum in Hmaximum; eauto; [ | set_solver | set_solver].
          eapply lstate_events_ext in Hlext; eauto.
          apply Maximum_correct in Hmaximum; [|done].
          apply Hglobcoh in Hel as [q [Hqin Hqcoh]].
          assert (q ∈ s ∪ {[erasure a]}) as Hqin'; [set_solver|].
          apply Hprov in Hqin' as [e' [[He'in | ->%elem_of_singleton]%elem_of_union <-]].
          * apply Hmaximum; [|done].
            apply Hcoh in He'in as [p [Hpin Hpcoh]].
            assert (e = p) as ->; [ | set_solver].
            eapply loc_st_coh_inj; eauto.
            apply loc_st_coh_glob_st_coh in Hqcoh.
            done.
          * exfalso.
            apply Hne.
            eapply glob_st_coh_inj; [eauto |].
            apply to_event_coh in Hncoh.
            apply loc_st_coh_glob_st_coh.
            done.
          * assert (GE_origin q = EV_Orig e) as ->.
            { destruct Hqcoh as (?&?&?).
              done. }
            assert (LE_origin a = EV_Orig (to_event op a)); [done|].
            done.
        + right.
          eapply loc_st_coh_maximum in Hmaximum; eauto; [ | set_solver | set_solver].
          eapply lstate_events_ext in Hlext; eauto.
          apply Maximum_correct in Hmaximum; [|done].
          apply Hglobcoh in Hel' as [q [Hqin Hqcoh]].
          assert (q ∈ s ∪ {[erasure a]}) as Hqin'; [set_solver|].
          apply Hprov in Hqin' as [e [[Hein | ->%elem_of_singleton]%elem_of_union <-]].
          * apply Hmaximum; [|done].
            apply Hcoh in Hein as [p [Hpin Hpcoh]].
            assert (e' = p) as ->; [ | set_solver].
            eapply loc_st_coh_inj; eauto.
            apply loc_st_coh_glob_st_coh in Hqcoh.
            done.
          * exfalso.
            apply Hne.
            eapply glob_st_coh_inj; [ | eauto].
            apply to_event_coh in Hncoh.
            apply loc_st_coh_glob_st_coh.
            done.
          * assert (GE_origin q = EV_Orig e') as ->.
            { destruct Hqcoh as (?&?&?).
              done. }
            assert (LE_origin a = EV_Orig (to_event op a)); [done|].
            done.
        + exfalso.
          by apply Hne. }
    iSplitL "".
    { iPureIntro.
      assert (hown' ∪ hfor ⊆ hglob ∪ {[to_event op a]}) as ?.
      { set_solver. }
      eapply events_total_order_sub; done. }
    iSplitL "Hglob Hglobi".
    { iExists (s ∪ {[erasure a]}).
      iFrame.
      iPureIntro.
      split; [|done].
      eapply glob_st_set_coh_union; eauto.
      eapply glob_st_set_coh_singleton.
      eapply loc_st_coh_glob_st_coh; done.
    }
    assert (own_orig (LE_origin a) hown') as Hown'orig.
    { subst hown'.
      apply own_orig_union; auto. }
    iSplitL "Hglobu"; [iFrame |].
    iSplitL "Huown Husub".
    { iExists _, _, _, _.
      iAssert (oplib_loc_snap γcc0 γinv1 (LE_origin a) hown' hfor) as "#Hsnap2".
      { rewrite /oplib_loc_snap.
        iFrame "#".
        iPureIntro.
        auto. }
      iFrame.
      iFrame "#".
      iPureIntro.
      auto 10. }
    iSplitL "Hlown Hlfor".
    { iExists _, _, _.
      iFrame.
      auto 10. }
    iExists γown1, γfor1, γsub0, γcc0, γinv1, (s' ∪ {[ a ]}).
    iFrame.
    iFrame "#". iFrame "Hloc".
    iPureIntro.
    repeat (split; auto).
    apply reflexivity.
  Qed.

  Lemma update_foreign i hown hfor hsub :
    oplib_loc_st_lock_wrap i hown hfor ⊢
    oplib_loc_st_inv_wrap i hown hfor hsub -∗
    (∃ s,
        OwnLocal i s ∗
        ⌜loc_st_set_coh (hown ∪ hfor) s⌝ ∗
        ((∀ a op,
                ⌜a ∉ s⌝ ∗
                 ⌜a ∈ compute_maximals LE_vc (s ∪ {[a]})⌝ ∗
                ⌜(LE_origin a) ≠ i⌝ ∗
                ⌜OpLib_Op_Coh op (LE_payload a)⌝ ∗
                ⌜lstate_ext (s ∪ {[ a ]})⌝ ∗
                OwnLocal i (s ∪ {[ a ]}) ==∗
                ∃ e,
                  ⌜loc_st_coh e a⌝ ∗
                  ⌜e ∉ hfor⌝ ∗
                  ⌜e ∈ Maximals (hown ∪ hfor ∪ {[e]})⌝ ∗
                  oplib_loc_st_lock_wrap i hown (hfor ∪ {[e]}) ∗
                  oplib_loc_st_inv_wrap i hown (hfor ∪ {[e]}) hsub)
          ∧
          (OwnLocal i s -∗
           oplib_loc_st_lock_wrap i hown hfor ∗
           oplib_loc_st_inv_wrap i hown hfor hsub))).
  Proof.
    iIntros "Hlockwrap Hinvwrap".
    iDestruct "Hinvwrap" as (γown γfor γsub γcc γinv s') "(%&%&%&%&%&%Hcoh&%Hownorig&%Hfor1&%Hfor2&%Hsub&Hloc&Hown&Hfor1&Hfor2&Hcc)".
    iDestruct "Hlockwrap" as (γown1 γfor1 γinv1) "(%&%&%&%Hlorig&%Hlfor&Hlown&Hlfor&#Hinvst)".
    rewrite_lookup.
    own_local_opt_init γinv1.
    iExists s'.
    iFrame "Hloc".
    iSplitL ""; [by iPureIntro|].
    iSplit.
    - iIntros (a op) "(%Hnotin&%Hamax&%Haorig&%Hopcoh&%Hstext&Hloc)".
      iMod (pair_update _ _ _ _ (hfor ∪ {[(to_event op a)]}) with "Hlfor Hfor1") as
        "[Hlfor Hfor1]".
      { compute_done. }
      iModIntro.
      iExists (to_event op a).
      rewrite /oplib_loc_st_lock_wrap.
      iSplitL "".
      { iPureIntro.
        apply to_event_coh. done. }
      iSplitL "".
      { iPureIntro.
        intros contra.
        (* use extensionality *)
        apply Hnotin.
        assert (to_event op a ∈ hown ∪ hfor) as Hin by set_solver.
        apply Hcoh in Hin.
        destruct Hin as [q [Hqin Hqcoh]].
        assert (a = q) as ->; [ | done].
        apply Hstext; [set_solver|set_solver|].
        apply to_event_coh in Hopcoh.
        destruct Hqcoh as [? [? <-]].
        destruct Hopcoh as [? [? <-]].
        done.
      }
      iSplitL ""; [iPureIntro|].
      { eapply loc_st_coh_maximal.
        - assert (loc_st_set_coh (hown ∪ hfor ∪ {[to_event op a]}) (s' ∪ {[a]})); last done.
          split.
          + intros p [Hl|Hr]%elem_of_union.
            * apply Hcoh in Hl.
              destruct Hl as [? [? ?]].
              exists x.
              auto with set_solver.
            * exists a.
              split; [set_solver|].
              apply elem_of_singleton in Hr as ->.
              apply to_event_coh.
              done.
          + intros q [Hl|Hr]%elem_of_union.
            * apply Hcoh in Hl.
              destruct Hl as [? [? ?]].
              exists x.
              auto with set_solver.
            * exists (to_event op a).
              split; [set_solver|].
              apply elem_of_singleton in Hr as ->.
              apply to_event_coh.
              done.
        - eapply to_event_coh; done.
        - set_solver.
        - set_solver.
        - apply compute_maximals_correct.
          split; [set_solver|].
          apply compute_maximals_correct in Hamax as [_ Hamax].
          done. }
      iSplitL "Hlown Hlfor".
      + iExists _, _, _.
        rewrite /oplib_loc_st_lock.
        iFrame. iFrame "#".
        iPureIntro.
        repeat split; auto.
        apply foreign_orig_union; [done |].
        apply foreign_orig_singleton.
        intros contra.
        apply Haorig.
        rewrite <- contra.
        simpl. done.
      + rewrite /oplib_loc_st_inv_wrap /oplib_loc_st_inv.
        iExists _, _, _, _, _, _.
        iFrame. iFrame "#". iFrame "Hloc".
        assert (hown ∪ (hfor ∪ {[to_event op a]}) = (hown ∪ hfor) ∪ {[to_event op a]}) as ->.
        { set_solver. }
        iPureIntro.
        assert (loc_st_set_coh (hown ∪ hfor ∪ {[to_event op a]}) (s' ∪ {[a]})) as Hsetcoh.
        { apply loc_st_set_coh_union; [done|].
          apply to_event_coh.
          done. }
        repeat split; eauto.
        * apply Hsetcoh.
        * apply Hsetcoh.
        * intros x [Hl| -> %elem_of_singleton]%elem_of_union.
          ** apply Hfor1. done.
          ** intros contra.
             apply Haorig.
             rewrite <- contra.
             apply to_event_coh in Hopcoh as [? [-> ?]].
             done.
        * assert (hown ∪ hsub ⊆ hown ∪ hfor) as ?.
          { destruct Hsub as [? ?].
            done. }
          set_solver.
        * destruct Hsub as [? Hsubs].
          intros e e' [Hl | -> %elem_of_singleton]%elem_of_union He'in Hle He'in2.
          ** apply (Hsubs e e'); try (done || set_solver).
          ** apply TM_le_eq_or_lt in Hle as [Heq | Hlt].
             *** assert (to_event op a = e') as ->; [ | done].
                 eapply lstate_events_ext in Hstext; eauto.
                 apply Hstext; [set_solver | set_solver | done].
             *** exfalso.
                 assert (a ∈ s' ∪ {[a]}) as Hain; [set_solver|].
                 assert (to_event op a ∈ hown ∪ hfor ∪ {[to_event op a]}) as Hevin; [set_solver|].
                 apply to_event_coh in Hopcoh.
                 pose proof (loc_st_coh_maximal _ _ _ _ Hsetcoh Hopcoh Hevin Hain Hamax) as Hmax'.
                 apply Maximals_correct in Hmax' as [_ Hmax'].
                 apply (Hmax' e'); [ | done].
                 set_solver.
    - iIntros "Hloc".
      iSplitL "Hlown Hlfor".
      + rewrite /oplib_loc_st_lock_wrap /oplib_loc_st_lock.
        iExists _, _, _.
        eauto 15 with iFrame.
      + iExists _, _, _, _, _, _.
        rewrite /oplib_loc_st_inv.
        iFrame. iFrame "#". iFrame "Hloc".
        iPureIntro.
        repeat split; auto.
        * apply Hcoh.
        * apply Hcoh.
        * destruct Hsub as [? ?].
          done.
        * destruct Hsub as [? ?].
          done.
  Qed.

End Resources.
