From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def.
From aneris.algebra Require Import disj_gsets.
From iris.algebra Require Import auth.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Lemma set_choose_forall_L
        (sag : socket_address_group) (sags : gset socket_address_group) :
    (∀ sag, sag ∈ sags → sag ≠ ∅) → sag ∈ sags →
    ∃ sa, sa ∈ sag.
  Proof. intros Hall Hin. specialize (Hall sag Hin). by apply set_choose_L. Qed.

  (* socket_interp_coh *)
  Lemma socket_interp_coh_init C :
    socket_address_group_ctx C -∗
    unfixed_groups_auth C -∗
    saved_si_auth ∅ -∗
    socket_interp_coh.
  Proof.
    iIntros "Hsags Hunfixed Hsis".
    iExists _, _. iFrame. iSplit; [done|].
    rewrite difference_diag_L.
    iExists _.
    iFrame. iSplit; [by iPureIntro; set_solver|done].
  Qed.

  (* (* socket_interp_coh *) *)
  (* Lemma socket_interp_coh_init ips C A M σ f : *)
  (*   dom M = A → *)
  (*   dom (state_ports_in_use σ) = ips → *)
  (*   A ⊆ C → *)
  (*   (∀ ip, ip ∈ ips → state_ports_in_use σ !! ip = Some ∅) → *)
  (*   (∀ sag sa, sag ∈ A → sa ∈ sag → ip_of_address sa ∈ ips) → *)
  (*   set_Forall is_singleton (C ∖ A) → *)
  (*   ([∗ set] sag ∈ A, sag ⤇* f sag)%I -∗ *)
  (*   socket_address_group_ctx C -∗ *)
  (*   unfixed_groups A -∗ *)
  (*   saved_si_auth M -∗ *)
  (*   socket_interp_coh (state_ports_in_use σ). *)
  (* Proof. *)
  (*   iIntros (<- <- HAle Hpiiu Hfixdom Hsingleton) "? Hctx ? ?". *)
  (*   rewrite /socket_interp_coh. *)
  (*   iDestruct (socket_address_group_ctx_valid with "Hctx") as %[_ Hne]. *)
  (*   iExists _, _, _; iFrame. *)
  (*   iSplit. *)
  (*   { iExists _. iFrame. iSplit; [ eauto | ]. *)
  (*     iApply (big_sepS_mono with "[$]"); auto. } *)
  (*   iSplit; [done|]. iSplit; [done|]. *)
  (*   iPureIntro. intros sag. split; auto. *)
  (*   intros [Hb | [Hb [Hdisj HP]]]; [done|]. *)
  (*   destruct HP as (sa & ps & Hsain & Hlookup & Hpsin). *)
  (*   assert (ip_of_address sa ∈ dom (state_ports_in_use σ)) as Hdom. *)
  (*   { apply elem_of_dom. eexists _. apply Hlookup. } *)
  (*   specialize (Hpiiu (ip_of_address sa) Hdom). *)
  (*   rewrite Hlookup in Hpiiu. *)
  (*   assert (ps = ∅) by naive_solver; subst. done. *)
  (* Qed. *)

  (* Lemma socket_interp_coh_fixed_valid sag A ips : *)
  (*   sag ∈ A → *)
  (*   socket_interp_coh ips -∗ fixed_groups A -∗ ∃ φ, sag ⤇* φ. *)
  (* Proof. *)
  (*   iIntros (HaA) "Hscoh #HA". *)
  (*   iDestruct "Hscoh" as (sags sis A') "(Hctx & HA' & Hsiauth & %Hle & %Hsingle & %Hdom)". *)
  (*   iDestruct (fixed_agree with "HA HA'") as %<-. *)
  (*   iDestruct (socket_address_group_ctx_valid with "Hctx") as %[_ Hin]. *)
  (*   assert (sag ∈ sags) as Hasags by set_solver. *)
  (*   pose proof (set_choose_forall_L _ _ Hin Hasags) as [sa Hsa]. *)
  (*   iDestruct ("Hsiauth") as (sis') "(Hsiauth & <- & Hsis)". *)
  (*   iDestruct (big_sepS_elem_of with "Hsis") as "$". *)
  (*   erewrite Hdom; eauto. *)
  (* Qed. *)

  (* Lemma unfixed_update_dealloc' A B : *)
  (*   ⊢ unfixed_groups_auth A ∗ unfixed_groups B ==∗ *)
  (*     unfixed_groups_auth (A ∖ B). *)
  (* Proof. Admitted. *)


  Lemma socket_address_group_own_subseteq `{anerisG Mdl}
        (sags sags' : gset socket_address_group) :
    sags' ⊆ sags →
    socket_address_groups_own sags -∗
    socket_address_groups_own sags'.
  Proof.
    iIntros (Hle) "Hsags".
    rewrite /socket_address_groups_own.
    apply subseteq_disjoint_union_L in Hle.
    destruct Hle as [Z [-> Hdisj]].
    setoid_rewrite <-disj_gsets_op_union.
    iDestruct "Hsags" as "[H1 H2]".
    iFrame.
  Qed.

  Lemma set_lemma `{Countable A} (X Y Z : gset A) :
    Z ⊆ Y → Y ⊆ X → X ∖ Y ∪ Z = X ∖ (Y ∖ Z).
  Proof. Admitted.

  Lemma socket_interp_coh_allocate sag φ :
    socket_interp_coh -∗
    unfixed_groups {[sag]} ==∗
    sag ⤇* φ ∗ socket_interp_coh.
  Proof.
    iIntros "Hinterp Hsag".
    iDestruct "Hinterp" as (sags A Hle) "(Hsags & Hunfixed & Hsis)".
    iAssert (⌜sag ∈ A⌝)%I as %Hin.
    { iDestruct (own_valid_2 with "Hunfixed Hsag") as %Hvalid.
      rewrite auth_both_valid_discrete in Hvalid.
      destruct Hvalid as [Hincluded Hvalid].
      rewrite gset_disj_included in Hincluded.
      iPureIntro. set_solver. }    
    iAssert (socket_address_group_own sag) as "#Hsag'".
    { rewrite /socket_address_group_own.
      iApply (socket_address_group_own_subseteq sags); [set_solver|].
      by iApply socket_address_groups_ctx_own. }    
    iMod (unfixed_update_dealloc with "[$Hunfixed $Hsag]") as "Hunfixed".
    iDestruct "Hsis" as (sis) "(Hsaved & %Hdom & Hsis)".
    iMod (socket_interp_alloc with "Hsag' Hsaved")
      as (γsi) "[Hsaved #Hsi]".
    { apply not_elem_of_dom. set_solver. }
    iModIntro. iFrame "#∗".
    iExists sags, (A ∖ {[sag]}).
    iSplit; [iPureIntro; set_solver|].
    iFrame. iExists _. iSplit; [done|].    
    iSplit; [iPureIntro|].
    { rewrite dom_insert_L.
      rewrite Hdom. rewrite -set_lemma; [set_solver|set_solver|done]. }
    rewrite -set_lemma; [|set_solver|done].
    iApply big_sepS_union; [set_solver|].
    iFrame. iApply big_sepS_singleton.
    iExists _. iFrame "#".
  Qed.

  (* Lemma socket_interp_coh_socketbind_static ps P sa sag A : *)
  (*   sa ∈ sag → *)
  (*   sag ∈ A → *)
  (*   P !! ip_of_address sa = Some ps → *)
  (*   port_of_address sa ∉ ps → *)
  (*   fixed_groups A -∗ *)
  (*   socket_interp_coh P -∗ *)
  (*   socket_interp_coh (<[ip_of_address sa:={[port_of_address sa]} ∪ ps]> P). *)
  (* Proof. *)
  (*   iIntros (?? Hpsin ?) "HA". rewrite /socket_interp_coh. *)
  (*   iDestruct 1 as (sags sis A') "(Hown & HA' & Hsiauth & %Hle & %Hsingle & %Hdms)". *)
  (*   iDestruct (fixed_agree with "HA HA'") as %<-. *)
  (*   iDestruct (socket_address_group_ctx_valid with "Hown") as %[Hdisj Hne]. *)
  (*   pose proof (socket_interp_coh_le _ _ _ Hdms) as Hle'. *)
  (*   pose proof (all_disjoint_subseteq _ _ Hle Hdisj) as HdisjA. *)
  (*   iExists _,_,_. iFrame. iPureIntro. *)
  (*   split; [done|]. split; [done|]. *)
  (*   intros sag'. rewrite Hdms. *)
  (*   split; intros [|(Hnin & Helems & sa' & ps' & Hin & HPlookup & Hpsin')]; auto. *)
  (*   { right. split; [done|]. split; [done|]. *)
  (*     destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq|]. *)
  (*     - eexists _, _. split; [done|]. rewrite Heq lookup_insert. split; [done|]. *)
  (*       rewrite -Heq Hpsin in HPlookup. *)
  (*       assert (ps = ps') by naive_solver; subst. *)
  (*       by apply elem_of_union_r. *)
  (*     - eexists _, _. by rewrite lookup_insert_ne //. } *)
  (*   destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq|]. *)
  (*   { rewrite Heq lookup_insert in HPlookup. *)
  (*     assert ({[port_of_address sa]} ∪ ps = ps') as <- by naive_solver. *)
  (*     apply elem_of_union in Hpsin'. *)
  (*     destruct Hpsin' as [Hdm%elem_of_singleton_1 | Hdm]. *)
  (*     - destruct sa, sa'; simpl in *. simplify_eq. *)
  (*       assert ((SocketAddressInet address0 port) ∈ *)
  (*               ({[SocketAddressInet address0 port]}:gset _)) *)
  (*         as Hin by set_solver. *)
  (*       assert (all_disjoint ({[{[SocketAddressInet address0 port]}]} ∪ A)). *)
  (*       { apply (all_disjoint_union {[{[SocketAddressInet address0 port]}]} A). *)
  (*         split. *)
  (*         { by apply all_disjoint_singleton. } *)
  (*         split. *)
  (*         { eapply all_disjoint_subseteq. done. done. } *)
  (*         done. } *)
  (*       assert (sag = {[SocketAddressInet address0 port]}). *)
  (*       { eapply (elem_of_all_disjoint_eq _ _ _ _); set_solver. } *)
  (*       naive_solver. *)
  (*     - right. split; [done|]. split; [done|]. eexists _, _. split; [done|]. *)
  (*       split; [by rewrite -Heq|]. *)
  (*       done. } *)
  (*   right. split; [done|]. split; [done|]. *)
  (*   eexists _, _. split; [done|]. *)
  (*   rewrite lookup_insert_ne in HPlookup; done. *)
  (* Qed. *)

  (* Lemma socket_interp_coh_socketbind_dynamic ps P sa A φ : *)
  (*   sa ∉ ⋃ₛ A → *)
  (*   P !! ip_of_address sa = Some ps → *)
  (*   port_of_address sa ∉ ps → *)
  (*   fixed_groups A -∗ *)
  (*   socket_interp_coh P ==∗ *)
  (*   socket_interp_coh (<[ip_of_address sa:={[port_of_address sa]} ∪ ps]> P) ∗ *)
  (*   sa ⤇1 φ. *)
  (* Proof. *)
  (*   iIntros (? Hpa Hps) "#HA". rewrite /socket_interp_coh. *)
  (*   iDestruct 1 as (sags sis A') "(Hctx & HA' & Hsiauth & %Hle & %Hsingle & %Hdms)". *)
  (*   iDestruct ("Hsiauth") as (sis') "(Hsiauth & <- & #Hsis)". *)
  (*   iDestruct (fixed_agree with "HA HA'") as %<-. *)
  (*   iDestruct (socket_address_group_ctx_valid with "Hctx") as %[Hdisj Hne]. *)
  (*   pose proof (socket_interp_coh_le _ _ _ Hdms) as Hle'. *)
  (*   pose proof (all_disjoint_subseteq _ _ Hle Hdisj) as Hdisj_sis. *)
  (*   pose proof (all_disjoint_subseteq _ _ Hle' Hdisj_sis) as HdisjA. *)
  (*   assert (sis' !! {[sa]} = None). *)
  (*   { destruct (sis' !! {[sa]}) eqn:Heq; last done. *)
  (*     destruct (Hdms {[sa]}) as [[Hin |] _]; [ by eapply elem_of_dom_2 | | ]. *)
  (*     - assert (sa ∈ ({[sa]}:socket_address_group)) as Hin' by set_solver. *)
  (*       pose proof (elem_of_union_set_mono _ _ _ Hin Hin') as Hin''. *)
  (*       contradiction. *)
  (*     - by set_solver. } *)
  (*   iDestruct (socket_address_group_ctx_valid with "Hctx") as %[_ Hall]. *)
  (*   iMod (socket_address_group_ctx_update _ {[{[sa]}]} with "Hctx") as "[Hctx Hown]". *)
  (*   { apply all_disjoint_singleton. } *)
  (*   { destruct (decide ({[sa]} ∈ sags)). *)
  (*     { by apply have_disj_elems_elem_of. } *)
  (*     apply have_disj_elems_singleton. *)
  (*     intros x Hx. *)
  (*     right. *)
  (*     assert (sa ∉ ⋃ₛ sags). *)
  (*     { assert ({[sa]} ∉ sags ∖ A). *)
  (*       { apply not_elem_of_difference. left. done. } *)
  (*       eapply not_elem_of_union_set_difference; [done|]. *)
  (*       intros Hsa. apply H1. *)
  (*       by apply elem_of_union_set_singletons. } *)
  (*     pose proof (set_choose_forall_L x _ Hall Hx) as [x' Hxin]. *)
  (*     pose proof (elem_of_union_set_mono _ _ _ Hx Hxin) as Hx'. *)
  (*     symmetry. *)
  (*     intros x'' Hx1 Hx2. *)
  (*     assert (x'' = sa) by set_solver; simplify_eq. *)
  (*     pose proof (elem_of_union_set_mono _ _ _ Hx Hx1). *)
  (*     set_solver. } *)
  (*   { apply set_Forall_singleton. rewrite /is_ne. set_solver. } *)
  (*   iMod (socket_interp_alloc {[sa]} φ sis' with "Hown Hsiauth") *)
  (*     as (?) "[Hsiauth #Hφ]"; [done|]. *)
  (*   iFrame "Hφ". iModIntro. *)
  (*   iExists _, _, _; iFrame. *)
  (*   iSplitL "Hsis Hsiauth". *)
  (*   { iExists _. *)
  (*     iFrame. *)
  (*     rewrite dom_insert_L. *)
  (*     iSplit; [done|]. *)
  (*     rewrite big_sepS_insert; last rewrite not_elem_of_dom //. *)
  (*     iFrame "#". *)
  (*     iExists _. iFrame "Hφ". } *)
  (*   iSplit; [iPureIntro;set_solver|]. *)
  (*   iSplit. *)
  (*   { iPureIntro. *)
  (*     assert ({[sa]} ∉ A). *)
  (*     { by apply not_elem_of_union_set_singleton. } *)
  (*     assert (({[{[sa]}]} ∪ sags) ∖ A = {[{[sa]}]} ∪ (sags ∖ A)) as Heq. *)
  (*     { set_solver. } *)
  (*     rewrite Heq. *)
  (*     apply set_Forall_union; [|done]. *)
  (*     apply set_Forall_singleton. rewrite /is_singleton. by eauto. } *)
  (*   iIntros (sag). *)
  (*   iPureIntro. *)
  (*   rewrite elem_of_union elem_of_singleton Hdms. *)
  (*   split. *)
  (*   - intros [->| Hdom]. *)
  (*     + right. *)
  (*       split; [ by apply not_elem_of_union_set_singleton |]. *)
  (*       pose proof (all_disjoint_have_disj_elems_singleton A sa HdisjA H). *)
  (*       split; [done|]. *)
  (*       eexists _, _. *)
  (*       split; [done|]. rewrite lookup_insert. split; [done|]. *)
  (*       by apply elem_of_union_l, elem_of_singleton. *)
  (*     + destruct Hdom as [? | (Hnin & Helems & sa' & ps' & -> & HPlookup & Hpsin')]; *)
  (*         [by left|]. *)
  (*       right. split; [done|]. *)
  (*       destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq |Hneq]. *)
  (*       * split; [done|]. eexists _, _. split; [done|]. *)
  (*         destruct Heq. rewrite lookup_insert. intros; simplify_eq. *)
  (*         split; [done|]. by apply elem_of_union_r. *)
  (*       * split; [done|]. eexists _, _. by rewrite lookup_insert_ne. *)
  (*   - intros [Hin | (Hnin & Helems & sa' & ps' & -> & HPlookup & Hpsin')]; [by auto|]. *)
  (*     destruct (decide (sa = sa')) as [Heq | Hneq]; [ by left; f_equiv | ]. *)
  (*     right; right. split; [done|]. *)
  (*     destruct (decide (ip_of_address sa = ip_of_address sa')) as [Heq|]. *)
  (*     + split; [done|]. eexists _, _. *)
  (*       rewrite Heq lookup_insert in HPlookup. split; [done|]. *)
  (*       rewrite -Heq. split; [eauto|]. *)
  (*       assert ({[port_of_address sa]} ∪ ps = ps') by naive_solver; subst. *)
  (*       apply elem_of_union in Hpsin'. destruct Hpsin' as [Hpsin' | Hport]. *)
  (*       * apply elem_of_singleton_1 in Hpsin'. *)
  (*         destruct sa,sa'; simpl in *; simplify_eq. *)
  (*       * intros. destruct Heq; simplify_eq; eauto. *)
  (*     + split; [done|]. intros. eexists _, _. by rewrite lookup_insert_ne in HPlookup. *)
  (* Qed. *)

End state_interpretation.
