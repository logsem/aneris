From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang notation network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def.
From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Σ}.

  (** socket_interp_coh *)
  Lemma socket_interp_coh_init ips A M σ f :
    dom (gset _) M = A →
    dom (gset _) (state_ports_in_use σ) = ips →
    (∀ ip, ip ∈ ips → state_ports_in_use σ !! ip = Some ∅) →
    (∀ a, a ∈ A → ip_of_address a ∈ ips) →
    ([∗ set] a ∈ A, a ⤇ f a)%I -∗
    fixed A -∗
    saved_si_auth M -∗
    socket_interp_coh (state_ports_in_use σ).
  Proof.
    iIntros (Hdmsi Hipdom Hpiiu Hfixdom) "? ? ?".
    rewrite /socket_interp_coh. iExists _; iFrame.
    iExists _; iFrame; iFrame "#".
    rewrite -!Hdmsi.
    iSplit; [iApply (big_sepS_mono with "[$]"); auto|].
    iSplit; [iPureIntro; set_solver|].
    iPureIntro. intros b Hbips. split; auto.
    intros [Hb | [Hb HP]]; [done|].
    simplify_eq.
    specialize (Hpiiu _ Hbips).
    specialize (HP _ Hpiiu). done.
  Qed.

  Lemma socket_interp_coh_fixed_valid a A ips :
    a ∈ A →
    socket_interp_coh ips -∗ fixed A -∗ ∃ φ, a ⤇ φ.
  Proof.
    iIntros (HaA) "Hscoh #HA".
    iDestruct "Hscoh" as (si A') "(HA' & Hsiauth & Hsis & % & H)".
    iDestruct "H" as %Hdom.
    iDestruct (fixed_agree with "HA HA'") as %->.
    iDestruct (big_sepS_elem_of with "Hsis") as "$".
    erewrite Hdom; eauto.
  Qed.

  Lemma socket_interp_coh_socketbind_static ps P a A:
    a ∈ A →
    P !! ip_of_address a = Some ps →
    port_of_address a ∉ ps →
    fixed A -∗
    socket_interp_coh P -∗
    socket_interp_coh (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P).
  Proof.
    iIntros (???) "HA". rewrite /socket_interp_coh.
    iDestruct 1 as (si A') "(HA' & Hsiauth & Hsis & %Hf & %Hdms)".
    iDestruct (fixed_agree with "HA HA'") as %->.
    iExists _,_. iFrame. iPureIntro. split.
    { intros ??. rewrite dom_insert elem_of_union; right. by apply Hf. }
    intros b. rewrite dom_insert elem_of_union. intros Hb.
    rewrite Hdms; last first.
    { destruct (decide (a = b)); subst; first by apply Hf.
      destruct Hb as [->%elem_of_singleton_1|]; [|done]. by apply Hf. }
    split; intros [|[Hnb Hdm]]; auto.
    { right. split; [done|].
      destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      - intros P'. rewrite Heq lookup_insert. intros; simplify_eq.
        apply elem_of_union_r, Hdm. rewrite -Heq //.
      - intros P'. rewrite lookup_insert_ne //. apply Hdm. }
    destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
    { right. split; [done|]. intros P'.
      rewrite Heq lookup_insert in Hdm.
      specialize (Hdm ({[port_of_address a]} ∪ _) eq_refl).
      apply elem_of_union in Hdm. destruct Hdm as [Hdm%elem_of_singleton_1 | Hdm].
      - destruct a, b; simpl in *. by subst.
      - rewrite -Heq. by intros; simplify_eq. }
    right. split; [done|].
    rewrite lookup_insert_ne in Hdm; done.
  Qed.

  Lemma socket_interp_coh_socketbind_dynamic ps P a A φ :
    a ∉ A →
    P !! ip_of_address a = Some ps →
    port_of_address a ∉ ps →
    fixed A -∗
    socket_interp_coh P ==∗
    socket_interp_coh (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P) ∗
    a ⤇ φ.
  Proof.
    iIntros (? Hpa Hps) "#HA". rewrite /socket_interp_coh.
    iDestruct 1 as (si A') "(HA' & Hsiauth & Hsis & %Hf & %Hdms)".
    iDestruct (fixed_agree with "HA HA'") as %<-.
    assert (si !! a = None).
    { destruct (si !! a) eqn:Heq; last done.
      destruct (Hdms a) as [[|[Hfx HP]] _]; try done.
      - by eapply elem_of_dom_2.
      - rewrite elem_of_dom. eauto.
      - by apply HP in Hpa. }
    iMod (socket_interp_alloc a φ with "Hsiauth")
      as (?) "[Hsiauth #Hφ]"; [done|].
    iFrame "Hφ". iModIntro. iExists _, _; iFrame.
    iSplitL "Hsis".
    { rewrite dom_insert_L big_sepS_insert;
        last rewrite not_elem_of_dom //.
      iFrame. iExists _. iFrame "Hφ". }
    iSplit.
    { iPureIntro. intros b Hb.
      destruct (decide (a = b)); subst; first done.
      apply dom_insert, elem_of_union. by auto. }
    iPureIntro. intros b Hbdom.
    rewrite dom_insert elem_of_union elem_of_singleton Hdms; last first.
    { destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      - destruct Heq. by eapply elem_of_dom_2.
      - apply dom_insert, elem_of_union in Hbdom. set_solver. }
    split.
    - intros [Hb | Hdom]; subst.
      + right. split; [done|]. rewrite lookup_insert.
        intros; simplify_eq. by apply elem_of_union_l, elem_of_singleton.
      + destruct Hdom as [? | [Hb HP]]; first by left.
        right. split; first done.
        destruct (decide (ip_of_address a = ip_of_address b)) as [Heq |Hneq].
        * destruct Heq. rewrite lookup_insert. intros; simplify_eq.
          apply elem_of_union_r, HP; eauto.
        * by rewrite lookup_insert_ne.
    - intros [Hb | [Hb Hdom]]; first by auto.
      destruct (decide (a = b)) as [Heq | Hneq]; first by auto.
      right; right. split; first done.
      destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      + intros ps'.
        rewrite Heq in Hdom.
        rewrite lookup_insert in Hdom.
        specialize (Hdom ({[port_of_address a]} ∪ ps) eq_refl).
        apply elem_of_union in Hdom. destruct Hdom as [Hdom | Hport].
        * apply elem_of_singleton_1 in Hdom.
          destruct a,b; simpl in *; simplify_eq.
        * intros. destruct Heq; simplify_eq; eauto.
      + intros. apply Hdom. rewrite lookup_insert_ne //.
  Qed.

End state_interpretation.
