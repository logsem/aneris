From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth ofe.
From iris.base_logic Require Export own gen_heap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris.program_logic Require Import weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Export
     helpers lang notation tactics network resources_lemmas.
From stdpp Require Import fin_maps gmap.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : aneris_to_val _ = Some _ |- _ => apply to_base_aneris_val in H
  | H : ground_lang.head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1);
     inversion H; subst; clear H
  | H: socket_step _ ?e _ _ _ _ _ _ _ |- _ =>
    try (is_var e; fail 1);
     inversion H; subst; clear H
  end.

Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Section lifting.
  Context `{distG Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : aneris_val → iProp Σ.
  Implicit Types efs : list aneris_expr.
  Implicit Types σ : state.

  Local Transparent IsNode.


  (** Weakest Precondition rules for Network-aware steps *)

  Lemma wp_start ip ports k E e Φ :
    ip ≠ "system" →
    ▷ FreeIP ip ∗
    ▷ Φ (mkVal "system" #()) ∗
    ▷ (IsNode ip -∗ FreePorts ip ports -∗ WP (mkExpr ip e) @ k; ⊤ {{ _, True }}) ⊢
    WP (mkExpr "system" (Start (LitString ip) e)) @ k; E {{ Φ }}.
  Proof.
    iIntros (Hneq) "(>Hfip & HΦ & Hwp)".
    iApply (wp_lift_head_step with "[-]"); first auto.
    iIntros (σ1 κ κs f) "Hσ".
    iMod (fupd_intro_mask _ ∅ True%I with "[]") as "Hmk"; first set_solver; auto.
    iDestruct "Hσ" as (x [Hdh Hds]) "(Hsi & HownS & Hlsi & HFP & HCoh)".
    iDestruct "HFP" as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iDestruct (is_FreeIP with "HfCtx Hfip") as %Hip.
    iMod (Use_FreeIP with "HfCtx Hfip") as "HfCtx".
    iMod (FreePorts_alloc _ ip ports with "HpCtx") as "[HpCtx Hports]"; first set_solver.
    iModIntro; iSplit; first iPureIntro.
    { do 4 eexists. apply AssignNewIpStepS; eauto; set_solver. }
    iNext. iIntros (e2 σ2 efs Hrd). iMod "Hmk" as "_".
    iDestruct (network_coherence_later with "HCoh") as "HCoh".
    inversion Hrd; last inversion SocketStep; subst; try inversion BaseStep.
    iMod (own_alloc (A:=authR (gen_heapUR loc ground_lang.val))  (● to_gen_heap ∅)) as (γh) "Hheap".
    { apply/auth_auth_valid. exact: to_gen_heap_valid. }
    iMod (own_alloc (A:=authR (gen_metaUR loc))  (● to_gen_meta ∅)) as (γhm) "Hheapm".
    { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
    iMod (own_alloc (A:=authR (gen_heapUR socket_handle (socket * message_soup * message_soup)))
                    (● to_gen_heap ∅)) as (γs) "Hsocket".
    { apply/auth_auth_valid. exact: to_gen_heap_valid. }
    iMod (own_alloc (A:=authR (gen_metaUR socket_handle)) (● to_gen_meta ∅)) as (γsm) "Hsocketm".
    { rewrite auth_auth_valid. exact: to_gen_meta_valid. }
    set (γn := {| heap_name := γh; heap_meta_name := γhm; socket_name := γs; socket_meta_name := γsm |} : node_gnamesO).
    iMod (own_update (A:=authR (gmapUR ip_address (agreeR node_gnamesO))) _
                     (● (to_agree <$> x))
                     (● (to_agree <$> (<[ip:=γn]> x)) ⋅ (◯ {[ ip := to_agree γn ]} : auth system_state_mapUR))
            with "HownS") as "[HownS #Hγl]".
    { rewrite fmap_insert. apply auth_update_alloc.
      apply (alloc_singleton_local_update _ _ (to_agree γn)); last done.
        by rewrite -(not_elem_of_dom (D:=gset ip_address)) dom_fmap_L Hdh not_elem_of_dom. }
    iSplitR "HΦ Hwp Hports".
    - iExists (<[ip:=γn]> x). iFrame. iSplitR.
      { iPureIntro. rewrite /gnames_coherence !dom_insert_L -Hdh -Hds /= //. }
      assert (x !! ip = None).
      { by rewrite -(not_elem_of_dom (D:=gset ip_address)) Hdh not_elem_of_dom. }
      rewrite big_sepM_insert; auto. rewrite -{1}(delete_notin x ip); auto.
      iDestruct (map_local_state_i_update_heaps with "Hlsi") as "Hlsi".
      iDestruct (map_local_state_i_update_sockets with "Hlsi") as "Hlsi".
      rewrite /= delete_notin; auto. iFrame.
      iSplitL "Hheap Hheapm Hsocket Hsocketm".
      + iExists _,_.
        rewrite !lookup_insert mapsto_node_eq /mapsto_node_def /= //.
        iFrame; iFrame "#". iModIntro. do 2 (iSplit; first done).
        iSplitL "Hheapm". { iExists _; by iFrame. }
        iSplitL; last done. iExists _; by iFrame.
      + iModIntro. iSplitR "HCoh". by iApply (FiuPiu_new_ip with "[$HfCtx] [$HpCtx]").
        rewrite /network_coherence.
        iDestruct "HCoh" as "[H Hmsg]". iDestruct "H" as %Hnet. iSplit.
        * iPureIntro. unfold network_sockets_coherence in *.
          iIntros (ip' ? Hst). destruct (decide (ip' = ip)).
          subst. apply lookup_insert_rev in Hst. subst. split; done.
          eapply Hnet; by rewrite lookup_insert_ne in Hst.
        * by iApply network_messages_coherence_new_ip.
    - iSplitL "HΦ". iApply wp_value; rewrite /IntoVal /=; eauto; done. iModIntro.
      simpl. iSplitL; last done. iApply ("Hwp" with "[]"); last by iFrame.
      rewrite /IsNode mapsto_node_eq /mapsto_node_def; iFrame "#"; iFrame; eauto.
  Qed.

  Lemma wp_new_socket n s E v1 v2 v3 :
  {{{ ▷ IsNode n }}}
    (mkExpr n (NewSocket (Val $ LitV $ LitAddressFamily v1)
                 (Val $ LitV $ LitSocketType v2)
                 (Val $ LitV $ LitProtocol v3))) @ s; E
  {{{ h, RET (mkVal n (LitV (LitSocket h)));
      h s↦[n]{1/2} ({| sfamily := v1;
                     stype := v2;
                     sprotocol := v3;
                     saddress := None |}, ∅, ∅) }}}.
Proof.
  iIntros (Φ) ">Hn HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n') "H !>"; simpl in *.
  iDestruct "H" as (m Hlcoh) "(Hsicoh & Hmaps & HlocS & Hrest)".
  rewrite /IsNode. iDestruct "Hn" as (γ's) "Hn".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hnins].
  iDestruct (node_local_state with "[HlocS]") as "(Hs & HlocS) ";
    first done; iFrame.
  iSplitR.
  { iPureIntro; do 4 eexists; apply SocketStepS with (S := S) ; try auto; subst.
    apply newsocket_fresh; by eauto. }
  iIntros (v2' σ2 efs Hstep); inv_head_step.
  set (socket := {| sfamily := v1; stype := v2; sprotocol := v3;
                    saddress := None |}).
  destruct γ's as [γh γs]; iSplitR; auto; iFrame.
  iDestruct "Hs" as (h' S'' Hh Hs) "(#Hn' & Hheap & Hsockets & Hzs)";
    simplify_eq; simpl. iModIntro.
  iMod ((gen_heap_alloc S handle (socket, ∅, ∅)) with "[Hsockets]")
    as "(Hsockets & Hs & _)"; auto.
  iAssert (handle s↦[n]{1} (socket, ∅, ∅)) with "[Hs Hn']" as "Hs".
  { iExists _. iFrame "#". iFrame. }
  iDestruct (fractional_half with "Hs") as "[Hs Hs']"; try done.
  iDestruct (map_local_state_i_update_sockets with "HlocS") as "HlocS".
  iModIntro. iSplitR "HΦ Hs"; iFrame.
  + iExists m. iFrame.
    iDestruct (big_sepM_insert with "[Hs' Hzs Hn]") as "Hzs"; eauto with iFrame.
    iDestruct (node_local_state_rev with "[Hheap Hzs Hsockets] HlocS")
      as "HX"; first done; simpl.
    { iExists h',(<[handle:=_]> S).
      simpl in *. iFrame. iSplit; try done.
      iFrame "#". iPureIntro.
      by rewrite lookup_insert. }
    iFrame.
    rewrite /gnames_coherence (dom_insert_Some (D:=gset ip_address) _ _ S) /= //.
    iDestruct "Hrest" as "(HFP & Hmsg)".
    iFrame. iSplit; first done. iSplitL "HFP".
    iDestruct "HFP" as (Fiu Piu) "((% & % & % & %) & HFP)".
    iExists Fiu, Piu. simpl. iFrame. iPureIntro.
    repeat split; try eauto with set_solver. set_solver.
    destruct (decide (ip = n)); subst; first by set_solver.
    rewrite lookup_insert_ne; set_solver.
    iApply (network_coherence_insert_new with "[Hmsg]"); try done.
    iDestruct "Hmsg" as "[? Hmsg]".
    iDestruct (network_messages_sepM_later with "Hmsg") as "Hmsg".
    by iFrame.
  + by iApply "HΦ".
Qed.


Lemma wp_socketbind_static s A E sh skt a:
  let ip := ip_of_address a in
  saddress skt = None →
  a ∈ A →
  {{{ Fixed A ∗
      ▷ FreePorts ip {[(port_of_address a)]} ∗
      ▷ sh s↦[ip]{1/2} (skt, ∅, ∅)
  }}}
    (mkExpr ip (SocketBind (Val $ LitV $ LitSocket sh)
                   (Val $ LitV $ LitSocketAddress a))) @ s; E
  {{{ RET (mkVal ip  #0);
      sh s↦[ip]{1/2} (skt <| saddress := Some a |>, ∅, ∅) ∗
      ∃ φ, a ⤇ φ }}}.
Proof.
  (* Introducing and unfolding hypotheses. *)
  iIntros (ip Hnone HaA Φ) "(#Hf & >HfpsA & >HshHalf1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto. iIntros (σ1 κ κs κn) "Hσ".
  iDestruct "Hσ" as (m HLocStateCoh)
       "(HsiCoh & Hgnames & HlocStatesInterp & HipsCoh & HmsCoh)".
  iDestruct "HipsCoh" as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HFip HPiu]".
  iMod (FreePorts_dealloc with "HPiu HfpsA")
    as (ports [Hports Hportsa%elem_of_subseteq_singleton]) "HPiu".
  iDestruct "HshHalf1" as ([γh γs]) "(#Hn & HshHalf1)".
  iDestruct (node_in_map with "Hn Hgnames") as %Hgnames.
  iDestruct (node_in_state_sockets _ _ _ _ Hgnames with "HlocStatesInterp") as %[Sn HSn].
  iDestruct (node_local_state with "[HlocStatesInterp]")
    as "(Hn_state_interp & HlocStatesInterp) "; [done | iFrame|].
  iDestruct "Hn_state_interp" as (hn Sn' Hhn Hsn) "(_ & HhCtx & HsCtx & Hshs)".
  rewrite Hsn in HSn Hhn;  simplify_eq; simpl.
  iDestruct (find_fixed_socket_interp with "Hf HsiCoh") as "#Haφ"; eauto.
  iDestruct (@gen_heap_valid with "HsCtx HshHalf1") as %Hlookup;
  iModIntro. iSplit.
  - destruct (HPiu _ _ Hports) as [Q [Ha Hdisj]];
    iPureIntro; do 4 eexists; eapply SocketStepS; eauto;
      eapply (SocketBindSucS ip sh a ∅ ∅ skt Sn (state_ports_in_use σ1) _); try eauto.
  - iIntros (e2 σ2 efs Hstep); inv_head_step. iModIntro.
    set (skt' := skt <| saddress ::= constructor (Some a) |>).
    iDestruct (mapsto_s_update (skt, ∅, ∅) (skt',  ∅, ∅) _ _ _ _ _ Hlookup
                 with "[$Hn $HshHalf1 $HsCtx $Hshs]")  as ">(HsCtx & Hshs & HshHalf2)".
    iModIntro. iSplit; first done. iSplitR "HΦ HshHalf2";
       last iApply "HΦ"; iFrame; iFrame "#".
    iExists m.
    iDestruct (map_local_state_i_update_sockets _ _ (<[sh:=(skt', ∅, ∅)]> Sn)
                   with "HlocStatesInterp") as "HlocStatesInterp".
    iDestruct (socket_interp_coherence_insert with "[] [HsiCoh]") as "HsiCoh"; eauto.
    iDestruct (node_local_state_rev with "[HhCtx Hshs HsCtx] HlocStatesInterp")
      as "HlocStatesInterp"; first done; simpl.
    { iExists hn, (<[sh:=_]> Sn). simpl in *. iFrame. iSplit; try done.
      iFrame "#". iPureIntro. by rewrite lookup_insert. }
    iFrame "Hgnames HsiCoh HlocStatesInterp". iSplit.
    { rewrite /gnames_coherence (dom_insert_Some (D:=gset ip_address) _ _ Sn) /= //. }
    iSplitR "HmsCoh".
    { iExists _, _; iFrame. iPureIntro; repeat split.
      - assert (ip_of_address a ∈ dom (gset _) Piu). { rewrite elem_of_dom; eauto. }
        rewrite dom_insert. set_solver.
      - intros ip0 Hip0. ddeq ip0 ip; last by eauto.
        exfalso; revert Hip0; eapply elem_of_disjoint; eauto; apply elem_of_dom; eauto.
      - set_solver.
      - ddeq ip0 ip; set_solver.
      - intros ip0 ?. ddeq ip0 (ip_of_address a).
        destruct (HPiu _ _ Hports) as [Q [Ha HQ]].
        rewrite H4 in Ha; simplify_eq /=. eexists. split; first done. set_solver. }
    iDestruct "HmsCoh" as "[HnetCoh HsentCoh]".
    iAssert (network_coherence  (state_sockets σ1) (state_ms σ1) (state_ports_in_use σ1))
      with "[HnetCoh HsentCoh]" as "HmsgCoh".
    { iFrame. rewrite /network_messages_coherence.
      iApply (big_sepS_mono with "HsentCoh"). iIntros (??) "[ H | H ]". iLeft.
      iDestruct "H" as (x0) "(H1 & H2)". iExists x0. iFrame. eauto with iFrame. }
    iDestruct (network_coherence_insert_bind with "HmsgCoh") as "H4"; eauto.
    Qed.

(* Lemma wp_socketbind_static_2 k A E sh s a : *)
(*   let ip := ip_of_address a in *)
(*   saddress s = None → *)
(*   a ∈ A → *)
(*   {{{ Fixed A ∗ *)
(*       ▷ FreePorts (ip_of_address a) {[(port_of_address a)]} ∗ *)
(*       ▷ sh s↦[ip]{1/2} (s, ∅, ∅) *)
(*   }}} *)
(*     (mkExpr ip (SocketBind (Val $ LitV $ LitSocket sh) *)
(*                    (Val $ LitV $ LitSocketAddress a))) @ k; E *)
(*   {{{ RET (mkVal ip #0); *)
(*       sh s↦[ip]{1/2} (s <| saddress := Some a |>, ∅, ∅) }}}. *)
(*   Proof. *)
(*     iIntros (? ? ? ?) "(#HA & Hports & Hsock) HΦ". *)
(*     iApply (wp_socketbind_static with "[$HA Hports $Hsock]"); try auto. *)
(*     iNext. iDestruct 1 as "(HM & Hψ)". *)
(*     iDestruct "Hψ" as (Ψ) "#HΨ". iApply "HΦ". iFrame. *)
(*   Qed. *)


  Lemma wp_socketbind_dynamic s A E sh k a φ :
    let ip := ip_of_address a in
    saddress s = None →
    a ∉ A →
  {{{ ▷ Fixed A ∗
      ▷ FreePorts (ip_of_address a) {[port_of_address a]} ∗
      ▷ sh s↦[ip]{1/2} (s, ∅, ∅) }}}
    (mkExpr ip (SocketBind (Val $ LitV $ LitSocket sh)
                   (Val $ LitV $ LitSocketAddress a))) @ k; E
  {{{ RET (mkVal ip #0);
      sh s↦[ip]{1/2} (s <| saddress := Some a |>, ∅, ∅) ∗ a ⤇ φ
    }}}.
  Proof.
    (* Introducing and unfolding hypotheses. *)
    iIntros (ip Hnone HaA Φ) "(#>Hf & >HfpsA & >HshHalf1) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto. iIntros (σ1 κ κs κn) "Hσ".
  iDestruct "Hσ" as (m HLocStateCoh)
       "(HsiCoh & Hgnames & HlocStatesInterp & HipsCoh & HmsCoh)".
  iDestruct "HipsCoh" as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HFip HPiu]".
  iMod (FreePorts_dealloc with "HPiu HfpsA")
    as (ports [Hports Hportsa%elem_of_subseteq_singleton]) "HPiu".
  iDestruct "HshHalf1" as ([γh γs]) "(#Hn & HshHalf1)".
  iDestruct (node_in_map with "Hn Hgnames") as %Hgnames.
  iDestruct (node_in_state_sockets _ _ _ _ Hgnames with "HlocStatesInterp") as %[Sn HSn].
  iDestruct (node_local_state with "[HlocStatesInterp]")
    as "(Hn_state_interp & HlocStatesInterp) "; [done | iFrame|].
  iDestruct "Hn_state_interp" as (hn Sn' Hhn Hsn) "(_ & HhCtx & HsCtx & Hshs)".
  rewrite Hsn in HSn Hhn;  simplify_eq; simpl.
   iDestruct (@gen_heap_valid with "HsCtx HshHalf1") as %Hlookup; iModIntro; iSplit.
    - destruct (HPiu _ _ Hports) as [Q [Ha Hdisj]];
        iPureIntro; do 4 eexists; eapply SocketStepS; eauto;
          eapply (SocketBindSucS ip sh a ∅ ∅ s Sn (state_ports_in_use σ1) _); try eauto.
    - iIntros (e2 σ2 efs Hstep); inv_head_step. iModIntro.
      set (skt' := s <| saddress ::= constructor (Some a) |>).
      iDestruct (mapsto_s_update (s, ∅, ∅) (skt',  ∅, ∅) _ _ _ _ _ Hlookup
                   with "[$Hn $HshHalf1 $HsCtx $Hshs]")  as ">(HsCtx & Hshs & HshHalf2)".
      iDestruct "HsiCoh" as (si fx Hfxsub Hdms) "(#Hfix & Hsi & #Hall)".
      iDestruct (ownF_agree with "Hf Hfix") as %?; subst.
      iMod (saved_pred_alloc φ) as (γsi) "#Hsipred".
      assert (Hnotin': si !! a = None).
      { destruct (si !! a) eqn:Heq; last done.
        destruct (Hdms a) as [[|[Hfx HP]] _]; try done.
        - by eapply elem_of_dom_2.
        - rewrite elem_of_dom. eauto.
        - match goal with
          | H: state_ports_in_use σ1 !! ip_of_address a = Some _ |- _ =>
              by apply HP in H
          end. }
      iMod (own_update _ _ (● <[a:=(to_agree γsi)]>si ⋅ ◯ {[ a:=(to_agree γsi)]})
              with "Hsi") as "[Hsi #Hsip]".
      { apply auth_update_alloc. by apply (alloc_singleton_local_update si). }
      iModIntro. iSplit; first done.
      iSplitR "HΦ HshHalf2"; last iApply "HΦ"; iFrame; iFrame "#".
      iExists m.
      iDestruct (map_local_state_i_update_sockets _ _ (<[sh:=(skt', ∅, ∅)]> Sn)
                   with "HlocStatesInterp") as "HlocStatesInterp".
      iDestruct (node_local_state_rev with "[HhCtx Hshs HsCtx] HlocStatesInterp")
        as "HlocStatesInterp"; first done; simpl.
      { iExists hn, (<[sh:=_]> Sn). simpl in *. iFrame. iSplit; try done.
        iFrame "#". iPureIntro. by rewrite lookup_insert. }
      iFrame "Hgnames HlocStatesInterp". iSplit.
      { rewrite /gnames_coherence (dom_insert_Some (D:=gset ip_address) _ _ Sn) /= //. }
      iSplitR "HmsCoh HFip HPiu".
      { rewrite /socket_interp_coherence.
        iExists (<[a:=(to_agree γsi)]>si), _; iFrame. iFrame "#".
        iSplit.
        { iPureIntro. intros b Hb.
          destruct (decide (a = b)); subst; first done.
          apply dom_insert, elem_of_union. by auto. }
        iSplitR.
        { iPureIntro. intros b Hbdom.
          rewrite dom_insert elem_of_union elem_of_singleton Hdms; last first.
          { ddeq (ip_of_address b) (ip_of_address a).
            - rewrite e. by eapply elem_of_dom_2.
            - rewrite /IPs in Hbdom. apply dom_insert, elem_of_union in Hbdom.
              set_solver. }
          split.
          - intros [Hb | Hdom]; subst.
            + right. split; first done. rewrite lookup_insert.
              intros; simplify_eq. by apply elem_of_union_l, elem_of_singleton.
            + destruct Hdom as [? | [Hb HP]]; first by left.
              right. split; first done.
              destruct (decide (ip_of_address a = ip_of_address b)) as [Heq |Hneq].
              * rewrite Heq lookup_insert. intros; simplify_eq.
                apply elem_of_union_r. apply HP. by rewrite -Heq.
              * by rewrite lookup_insert_ne.
          - intros [Hb | [Hb Hdom]]; first by auto.
            destruct (decide (a = b)) as [Heq | Hneq]; first by auto.
            right; right. split; first done.
            destruct (decide (ip_of_address a = ip_of_address b)) as [Heq' |Hneq'].
            + intros P.
              rewrite Heq' in Hdom.
              rewrite lookup_insert in Hdom.
              match goal with
              | _: port_of_address a ∉ ?P |- _ =>
                specialize (Hdom ({[port_of_address a]} ∪ P) eq_refl)
              end.
              apply elem_of_union in Hdom. destruct Hdom as [Hdom | Hport].
              * apply elem_of_singleton_1 in Hdom. destruct a,b; simpl in *; simplify_eq.
              * intros.
                match goal with
                | HP: state_ports_in_use σ1 !! ip_of_address b = Some P |- _ =>
                  rewrite -Heq' in HP; by simplify_eq
                end.
            + intros. apply Hdom. rewrite lookup_insert_ne; done. }
      -  rewrite dom_insert_L big_sepS_insert.
        iFrame; iFrame "#". iExists _, _; iFrame "#".
        { by rewrite not_elem_of_dom. } }
    iSplitR "HmsCoh".
    { iExists _, _; iFrame.
       iPureIntro; repeat split; try eauto.
          - assert (ip_of_address a ∈ dom (gset _) Piu).
            { rewrite elem_of_dom; eauto. }
            rewrite dom_insert. set_solver.
          - intros ip0 Hip0.
            destruct (decide (ip0 = ip_of_address a)); subst.
            + exfalso; revert Hip0. eapply elem_of_disjoint; eauto.
              apply elem_of_dom; eauto.
            + rewrite lookup_insert_ne //; by apply HFip.
          - set_solver.
          - simpl. rewrite !lookup_insert_ne //. set_solver.
            set_solver.
          - intros ip0 Q. destruct (decide (ip0 = ip_of_address a)); subst.
            + rewrite lookup_insert => ?; simplify_eq.
              destruct (HPiu _ _ Hports) as [Q [Ha HQ]].
              match goal with
                Ha : state_ports_in_use σ1 !! ip_of_address a = Some _,
                Hb : state_ports_in_use σ1 !! ip_of_address a = Some _ |- _ =>
                rewrite Ha in Hb; simplify_eq
              end.
              exists ({[port_of_address a]} ∪ Q).
              rewrite lookup_insert; split; first done.
              set_solver.
            + rewrite !lookup_insert_ne //. apply HPiu. }
    iDestruct "HmsCoh" as "[HnetCoh HsentCoh]".
    iAssert (network_coherence  (state_sockets σ1) (state_ms σ1) (state_ports_in_use σ1))
      with "[HnetCoh HsentCoh]" as "HmsgCoh".
    { iFrame. rewrite /network_messages_coherence.
      iApply (big_sepS_mono with "HsentCoh"). iIntros (??) "[ H | H ]". iLeft.
      iDestruct "H" as (x0) "(H1 & H2)". iExists x0. iFrame. eauto with iFrame. }
    iDestruct (network_coherence_insert_bind with "HmsgCoh") as "H4"; eauto.
    iExists γsi. iFrame "#".
  Qed.

  Lemma wp_send φ m sh a f k E s R T:
    let ip := ip_of_address f in
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_protocol := sprotocol s;
          m_body := m;
        |} in
    {{{ ▷ sh s↦[ip]{1/2} (s, R, T) ∗ a ⤇ φ ∗ φ msg }}}
      (mkExpr ip (SendTo (Val $ LitV $ LitSocket sh) #m #a)) @ k; E
    {{{ RET (mkVal ip (#(String.length m)));
        sh s↦[ip]{1/2} (s, R, {[ msg ]} ∪ T)
    }}}.
  Proof.
    iIntros (ip Hsome Hmsg Φ) "(>Hsocket & #Hsip & Hsipred) HΦ"; simpl.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 κ κs n') "Hσ !>".
    iDestruct "Hσ" as (γmap Hncoh)
                        "(Hsi & Hmaps & HlocS & HFip & Hnetcoh & Hms)".
    iDestruct "Hsocket" as ([γh γs]) "(Hn & Hs)".
    iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hnins].
    iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS)";
      first done; iFrame.
    iDestruct "Hloc"
      as (h' S' Hheaps Hsockets) "(Hn' & Hheap & Hsockets & Hshs)".
    rewrite Hsockets in Hnins; simplify_eq; simpl.
    iDestruct (@gen_heap_valid with "Hsockets Hs") as %Hv.
    iSplitR.
    { iPureIntro; do 4 eexists; eapply SocketStepS; eauto.
      apply SendToBoundS; try done. }
    iIntros (e2 σ2 efs Hstep); inv_head_step. iModIntro.
    set (msg := {| m_sender := f; m_destination := a;
                   m_protocol := sprotocol s; m_body := m |}).
    iDestruct (mapsto_s_update (s, R, T) (s, R, {[ msg ]} ∪ T) _ _ _ _ _ Hv
                 with "[$Hn $Hs $Hsockets $Hshs]")  as ">(Hsockets & Hshs & Hsh')".
    iModIntro. iSplit; first done. iSplitR "HΦ Hsh'"; last by iApply "HΦ".
    iExists γmap. iFrame. iSplitR.
    { rewrite /gnames_coherence (dom_insert_Some (D:=gset ip_address) _ _ S) /= //. }
    iDestruct (map_local_state_i_update_sockets _ _ (<[sh:=(s, R, {[msg]} ∪ T)]> S)
                 with "HlocS") as "HlocS".
      iSplitL "Hn' Hheap Hsockets HlocS Hshs"; auto.
      + iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets Hshs] HlocS")
         as "HlocS"; first done; simpl.
        * iExists h', (<[sh:=_]> S). iFrame. iSplit; try done.
          iPureIntro. simpl. by rewrite lookup_insert.
        * iFrame.
      +  iAssert (network_coherence (state_sockets σ1) (state_ms σ1) (state_ports_in_use σ1))
          with "[Hnetcoh Hms]" as "HnetCoh".
         { iFrame. rewrite /network_messages_coherence.
          iApply (big_sepS_mono with "Hms"). iIntros (??) "[ H | H ]". iLeft.
          iDestruct "H" as (x0) "(H1 & H2)". iExists x0. iFrame. eauto with iFrame. }
         iSplitL "HFip".
         *  iDestruct "HFip" as (Fiu Piu) "((% & % & % & %) & HFP)".
            iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto. set_solver.
            ddeq ip0 ip; set_solver.
         * iDestruct (network_coherence_insert_sent with "[Hsip] [Hsipred] [HnetCoh]") as "H"; eauto.
Qed.

  Lemma wp_send_duplicate m sh a f k E s R T:
    let ip := ip_of_address f in
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_protocol := sprotocol s;
          m_body := m;
        |} in
    msg ∈ T →
    {{{ ▷ sh s↦[ip]{1/2} (s, R, T) }}}
      (mkExpr ip (SendTo (Val $ LitV $ LitSocket sh) #m #a)) @ k; E
    {{{ RET (mkVal ip #(String.length m));
        sh s↦[ip]{1/2} (s, R, T)
    }}}.
   Proof.
    iIntros (ip Hsome msg Hmsg Φ) ">Hsocket HΦ"; simpl.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 κ κs n') "Hσ !>".
    iDestruct "Hσ" as (γmap Hncoh)
                        "(Hsi & Hmaps & HlocS & Hips & Hnetcoh & Hms)".
    iDestruct "Hsocket" as ([γh γs]) "(Hn & Hs)".
    iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hnins].
    iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS)";
      first done; iFrame.
    iDestruct "Hloc"
      as (h' S' Hheaps Hsockets) "(Hn' & Hheap & Hsockets & Hshs)".
    rewrite Hsockets in Hnins; simplify_eq; simpl.
    iDestruct (@gen_heap_valid with "Hsockets Hs") as %Hv.
    iSplitR.
    { iPureIntro; do 4 eexists; eapply SocketStepS; eauto.
      apply SendToBoundS; try done. }
    iIntros (e2 σ2 efs Hstep); inv_head_step. iModIntro.
    iDestruct (big_sepM_delete _ S with "Hshs") as "[HshHalf2 Hshs]"; first done.
    iAssert (sh s↦[ip]{1/2} (s, R, T)) with "[Hs Hn]" as "HshHalf1".
    { iExists _. iFrame "#". iFrame. }
     iCombine "HshHalf1" "HshHalf2" as "Hsh".
    iDestruct "Hsh" as ([??]) "(#Hn & Hsh)".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %Heq.
    simplify_eq /=. iClear "Hn'".
    iMod (gen_heap_update _ sh (s, R, T) (s, R, {[ msg ]} ∪ T) with "Hsockets Hsh")
      as "(Hsockets & Hsh)".
     iDestruct (fractional_half with "Hsh") as "[Hsh Hsh']"; try done.
     iModIntro. iSplit; first done. iSplitR "HΦ Hsh".
    - iExists γmap. iFrame. iSplitR.
      { rewrite /gnames_coherence.
        rewrite (dom_insert_Some (D:=gset ip_address) _ _ S) /= //. }
      iDestruct (map_local_state_i_update_sockets _ _ (<[sh:=(s, R, {[msg]} ∪ T)]> S)
                   with "HlocS") as "HlocS".
      iAssert (sh s↦[ip]{1/2} (s, R, {[msg]} ∪ T)) with "[Hsh']" as "Hsh'".
      { iExists _; iFrame "#"; iFrame. }
        iDestruct (big_sepM_insert  with "[Hsh' $Hshs Hn]") as "Hshs"; try done.
      apply lookup_delete.
      iSplitL "Hn Hheap Hsockets HlocS Hshs"; auto.
      + iDestruct (node_local_state_rev with "[Hn Hheap Hsockets Hshs] HlocS")
         as "HlocS"; first done; simpl.
        * iExists h', (<[sh:=_]> S). iFrame. iSplit; try done.
          iFrame "#". iSplit.
          ** iPureIntro. simpl. rewrite lookup_insert. done.
          ** rewrite insert_delete. iFrame.
        * iFrame.
      + iDestruct "Hnetcoh" as %HnetCoh.
        iAssert (⌜network_sockets_coherence (state_sockets σ1) (state_ms σ1)
                  (state_ports_in_use σ1)⌝)%I as "HnetCoh2"; first done.
        iAssert (network_coherence
                   (state_sockets σ1) (state_ms σ1) (state_ports_in_use σ1))
          with "[HnetCoh2 Hms]" as "HnetCoh".
        { iFrame "#".
          rewrite /network_messages_coherence.
      iApply (big_sepS_mono with "Hms"). iIntros (??) "[ H | H ]". iLeft.
      iDestruct "H" as (x0) "(H1 & H2)". iExists x0. iFrame. eauto with iFrame. }
    iSplitL "Hips".
        * iDestruct "Hips" as (Fiu Piu) "((% & % & % & %) & HFP)".
            iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto. set_solver.
            ddeq ip0 ip; set_solver.
        *  assert (T = {[msg]} ∪ T) by set_solver. rewrite -H0.
           assert (state_ms σ1 = {[msg]} ∪ (state_ms σ1)).
           destruct (HnetCoh ip S) as (HBpCoh & HshCoh & HsmCoh & HsaCoh); first done.
           specialize (HsmCoh sh s R T f Hv Hsome) as [Hm1 Hm2]. set_solver.
           rewrite -H1. rewrite insert_id. iFrame. rewrite insert_id; done.
    - iApply "HΦ".
      iAssert (sh s↦[ip]{1/2} (s, R, {[msg]} ∪ T)) with "[Hsh Hn]" as "HshHalf1".
      { iExists _. iFrame "#". iFrame. }
      assert (T = {[msg]} ∪ T) as <- by set_solver. iFrame.
   Qed.

   Lemma wp_receive_from_gen (Ψo : option (socket_interp Σ)) k a E h s R T :
    let ip := ip_of_address a in
    saddress s = Some a →
    {{{ ▷ h s↦[ip]{1/2} (s, R, T) ∗ match Ψo with Some Ψ => a ⤇ Ψ | _ => True end }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ h s↦[ip]{1/2} (s, R, T)) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h s↦[ip]{1/2} (s, {[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
            ⌜msg ∈ R⌝ ∗ h s↦[ip]{1/2} (s, R, T))))
    }}}.
   Proof.
    iIntros (ip Hla Φ) "[>Hh #HΨ] HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1 κ κs n) "Hσ !>".
    iDestruct "Hσ" as (γmap HγmapCoh) "(Hsi & HownS & HlocS & HipsCtx & HnetCoh & HsiCoh)".
    iDestruct "Hh" as ([γh γs]) "(#Hn & Hs)".
    iDestruct (node_in_map with "Hn HownS") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[Sn HSn].
    iDestruct (node_local_state with "[$HlocS]") as "(Hloc & HlocS) "; first done.
    iDestruct "Hloc" as (hp ? Hheap ?) "(_ & HhCtx & HsCtx & Hsockets)". simplify_eq /=.
    iDestruct (@gen_heap_valid with "HsCtx Hs") as %HSnh. iSplitR.
    { by iPureIntro; do 4 eexists; eapply SocketStepS; eauto; eapply ReceiveFromNoneS. }
    iIntros (v2' σ2 efs Hstep); inv_head_step; iSplitR; auto; subst; last first.
    - iNext.
      iModIntro. iSplitR "HΦ Hs Hn".
      + iExists γmap. iFrame. iSplitR.
        { rewrite /gnames_coherence (dom_insert_Some (D:=gset ip_address) _ _ S') /= //. }
        iDestruct (map_local_state_i_update_sockets _ _ S' with "HlocS") as "HlocS".
        iSplitL "Hn HhCtx HsCtx HlocS Hsockets"; auto.
        -- iDestruct (node_local_state_rev with "[Hn HhCtx HsCtx Hsockets] HlocS")
          as "HlocS"; first done; simpl; last by iFrame.
           iExists _, S'. iFrame. iSplit; try done. iFrame "#".
          iPureIntro. simpl. by rewrite lookup_insert.
        -- iAssert (network_coherence (state_sockets σ1) (state_ms σ1) (state_ports_in_use σ1))
           with "[HnetCoh HsiCoh]" as "HnetCoh".
           { iFrame. rewrite /network_messages_coherence.
           iApply (big_sepS_mono with "HsiCoh"). iIntros (??) "[ H | H ]". iLeft.
           iDestruct "H" as (x0) "(H1 & H2)". iExists x0. iFrame. eauto with iFrame. }
           iSplitL "HipsCtx".
           ---  iDestruct "HipsCtx" as (Fiu Piu) "((% & % & % & %) & HFP)".
                iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto. set_solver.
                ddeq ip0 ip; set_solver.
           --- assert (<[ip:=S']> (state_sockets σ1) = (state_sockets σ1)) as ->. by apply insert_id. done.
      + iApply "HΦ". iFrame. iLeft.
        iAssert (h s↦[ip]{1/2} (s, R, T)) with "[Hs Hn]" as "HshHalf1".
        { iExists _. iFrame "#". iFrame. } by iFrame.
    - rewrite /messages_to_receive_at in H3.
      apply elem_of_filter in H3 as (Heq & Hin).
      (* iDestruct "HnetCoh" as (HipsCoh HsktsCoh) "HsiCoh". *)
       destruct (decide (m ∈ R)).
       + iNext.
         iModIntro.
         assert ({[m]} ∪ R = R) as -> by set_solver.
         assert (<[h:=(s, R, T)]> Sn = Sn) as ->. by apply insert_id.
         assert (<[ip:=Sn]> (state_sockets σ1) = (state_sockets σ1)) as ->. by apply insert_id.
         iSplitR "HΦ Hs Hn".
         * iExists γmap. iFrame. iSplitR; first by rewrite /gnames_coherence.
           iDestruct (map_local_state_i_update_sockets _ _ _ with "HlocS") as "HlocS".
           iSplitL "Hn HhCtx HsCtx HlocS Hsockets"; auto.
           instantiate (1 := Sn).
           assert (<[ip:=Sn]> (state_sockets σ1) = (state_sockets σ1)) as ->. by apply insert_id.
           -- iDestruct (node_local_state_rev with "[Hn HhCtx HsCtx Hsockets] HlocS")
               as "HlocS"; first done; simpl. iExists _, _. iFrame. iSplit; try done. iFrame "#".
              iPureIntro. simpl. done.  iFrame.
           -- iFrame. rewrite /network_messages_coherence.
                iApply (big_sepS_mono with "HsiCoh"). iIntros (??) "[ H | H ]". iLeft.
                iDestruct "H" as (x0) "(H1 & H2)". iExists x0. iFrame. eauto with iFrame.
         * iApply "HΦ". iFrame. iRight.
          iAssert (h s↦[ip]{1/2} (s, R, T)) with "[Hs Hn]" as "HshHalf1".
          { iExists _. iFrame "#". iFrame. }
          iExists m. do 2 (iSplit; first done). iRight. by iFrame.
       +  iPoseProof (big_sepS_delete _ _ m with "HsiCoh") as
             "[[ Hmsi | Hrd ] HsiCoh]"; first done.
         (* case: fresh message *)
          * iDestruct "Hmsi" as (Ψ) "[#Hψ Hm]".
            iAssert (▷ match Ψo with
                       Some Ψ => Ψ m
                     | _ => ∃ φ, m_destination m ⤇ φ ∗ φ m
                     end)%I with "[Hm]" as "Hm".
            { destruct Ψo as [ψ|]; last by eauto.
              rewrite Heq.
              iDestruct (si_pred_agree _ _ _ m with "HΨ Hψ") as "Hsiagree".
              iNext.
              iRewrite "Hsiagree"; done. }
            iNext.
            iDestruct (mapsto_s_update (s, R, T) (s, {[ m ]} ∪ R, T) _ _ _ _ _ HSnh
                         with "[$Hn $Hs $HsCtx $Hsockets]") as ">(Hsockets & Hshs & Hs)".
            iModIntro. iSplitR "HΦ Hs Hn Hm".
            -- iExists γmap. iFrame. iSplitR.
               { rewrite /gnames_coherence (dom_insert_Some (D:=gset ip_address) _ _ Sn) /= //. }
               iDestruct (map_local_state_i_update_sockets _ _ (<[h:=(s, {[m]} ∪ R, T)]> Sn)
                             with "HlocS") as "HlocS".
               iSplitL "Hn HhCtx Hsockets HlocS Hshs"; auto.
               ++ iDestruct (node_local_state_rev with "[Hn HhCtx Hsockets Hshs] HlocS")
                   as "HlocS"; first done; simpl; last by iFrame.
                  iExists _, (<[h:=_]> Sn). iFrame. iSplit; try done. iFrame "#".
                  iPureIntro. simpl. by rewrite lookup_insert.
               ++ iSplitL "HipsCtx".
                  ** iDestruct "HipsCtx" as (Fiu Piu) "((% & % & % & %) & HFP)".
                     iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto. set_solver.
                     ddeq ip0 ip; set_solver.
                  ** rewrite /network_coherence.
                     iDestruct "HnetCoh" as %HnetCoh.
                     iAssert
                       (([∗ set] y ∈ (state_ms σ1 ∖ {[m]}),
                         (∃ x : socket_interp Σ,
                             m_destination y ⤇ x ∗ x y) ∨
                          ⌜message_received (state_sockets σ1) y⌝) -∗
                              network_messages_coherence
                              (<[ip:=<[h:=(s, {[m]} ∪ R, T)]> Sn]>
                               (state_sockets σ1)) (state_ms σ1))%I as "H".
                     { iIntros "H". rewrite /network_messages_coherence.
                       rewrite (big_sepS_delete _ (state_ms σ1) m) // /=.
                       iSplitR.
                       iRight. iPureIntro.
                       exists a, (<[h:=(s, {[m]} ∪ R, T)]> Sn), h, s, ({[m]} ∪ R), T.
                       repeat split; try rewrite lookup_insert; eauto with set_solver.
                       iApply (big_sepS_mono with "H ").
                       iIntros (m' Hm') "[ H | H ]". iLeft.
                       iDestruct "H" as (x0) "(H1 & H2)". iExists x0. iFrame.
                       iRight. ddeq m' m; first by set_solver.
                       iDestruct "H" as %(a'&Sn'&h'&s'&R'&T'&HSn'&Hs'&Hsa'&HinR').
                       iPureIntro.
                       ddeq (ip_of_address a') ip.
                       - rewrite e in HSn'.  assert (Sn' = Sn) by set_solver. subst.
                         assert (m' ∈ state_ms σ1) by set_solver.
                         destruct (HnetCoh ip Sn)
                           as (HBpCoh & HshCoh & HsmCoh & HsaCoh); first done.
                         ddeq a' (m_destination m).
                         + assert (h' = h). eapply HshCoh; eauto. by rewrite Hla. subst.
                           rewrite Hs' in HSnh. simplify_eq /=.
                           exists (m_destination m), (<[h:=(s, {[m]} ∪ R, T)]> Sn), h, s, ({[m]} ∪ R), T.
                           repeat split; eauto with set_solver; try rewrite !lookup_insert; done.
                         + assert (h' ≠ h). intro. subst. rewrite Hs' in HSnh. set_solver.
                           exists a', (<[h:=(s, {[m]} ∪ R, T)]> Sn), h', s', R', T'.
                           repeat split; try done. rewrite e.
                             by rewrite lookup_insert. by rewrite !lookup_insert_ne; last done.
                       - exists a', Sn', h', s', R', T'.
                         repeat split; eauto. by rewrite lookup_insert_ne. }
                          iSpecialize ("H" with "HsiCoh").
                          iFrame.
                          iPureIntro. intros ip0 Sn0 Hip0.
                          ddeq ip0 ip; last by eauto.
                          specialize (HnetCoh ip Sn HSn) as (HBpCoh & HshCoh & HsmCoh & HsaCoh).
                          split. intros h' **. ddeq h' h; eauto using HBpCoh.
                          split. intros h1 h2 **.
                          ddeq h1 h; simplify_eq /=.
                          { ddeq h2 h; simplify_eq /=; first done.
                            assert (is_Some (saddress s0)) by eauto.
                            by specialize (HshCoh h h2 s0 s' R R' T0 T' HSnh H1 H2 H3). }
                          { ddeq h2 h; simplify_eq /=.
                            assert (is_Some (saddress s0)) by eauto.
                             by specialize (HshCoh h1 h2 s0 s' R0 R' T0 T' H0 H1 H4 H3). }
                          split.
                          { intros h' s' **; ddeq h' h; last by eapply HsmCoh.
                          split; intros m0 Hm0.
                          apply elem_of_union in Hm0 as [Hm0|Hm0]; first by set_solver.
                          eapply HsmCoh; eauto.
                          eapply HsmCoh; eauto. }
                          intros h' **; ddeq h' h; eauto.
            -- iApply "HΦ". iFrame. iRight. iExists m. rewrite Heq.
               do 2 (iSplit; first done). iLeft. eauto with iFrame.
          (* 2b.2: absurd case *)
          * iDestruct "Hrd" as %(a' & Hrd).
            iDestruct "HnetCoh" as %HnetCoh.
            assert (m ∈ R).
            { eapply message_received_at_coherence; eauto.
              destruct Hrd as (Sn'&h'&s'&R'&T'&HSn'&Hs'&Hsa'&HinR').
              assert (m_destination m = a').
              { destruct (HnetCoh (ip_of_address a') Sn') as (HBpCoh & HshCoh & HsmCoh & HsaCoh); first done.
                specialize (HsmCoh h' s' R' T' a' Hs' Hsa') as (Hmsg & _).
                  by specialize (Hmsg m HinR') as (-> & _). }
              subst. do 5 eexists; eauto. }
            set_solver.
   Qed.

   Lemma wp_receive_from k a E h s R T :
    let ip := ip_of_address a in
    saddress s = Some a →
    {{{ ▷ h s↦[ip]{1/2} (s, R, T) }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket h))) @ k; E
    {{{ r, RET (mkVal ip r);
        ((⌜r = NONEV⌝ ∗ h s↦[ip]{1/2} (s, R, T)) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h s↦[ip]{1/2} (s, {[ msg ]} ∪ R, T) ∗ ∃ φ, a ⤇ φ ∗ φ msg) ∨
            ⌜msg ∈ R⌝ ∗ h s↦[ip]{1/2} (s, R, T))))
    }}}.
   Proof.
     simpl.
     iIntros (Hs Φ) "Hsh HΦ".
     iApply (wp_receive_from_gen None with "[$]"); first done.
     iNext.
     iIntros (r) "Hr".
     iApply "HΦ"; eauto.
   Qed.

  Lemma wp_receive_from_2 k a E sh s R T φ :
    let ip := ip_of_address a in
    saddress s = Some a →
    {{{ ▷ sh s↦[ip]{1/2} (s, R, T) ∗ a ⤇ φ }}}
      (mkExpr ip (ReceiveFrom (Val $ LitV $ LitSocket sh))) @ k; E
    {{{ r, RET (mkVal ip r);
        (⌜r = NONEV⌝ ∗ sh s↦[ip]{1/2} (s, R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh s↦[ip]{1/2} (s, {[ msg ]} ∪ R, T) ∗ φ msg) ∨
            ⌜msg ∈ R⌝ ∗ sh s↦[ip]{1/2} (s, R, T))
    }}}.
   Proof.
     simpl.
     iIntros (Hs Φ) "Hsh HΦ".
     iApply (wp_receive_from_gen (Some φ) with "[$]"); first done.
     iNext.
     iIntros (r) "Hr".
     iApply "HΦ"; eauto.
   Qed.

End lifting.
