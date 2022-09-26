From stdpp Require Import fin_maps gmap.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import collect.
From aneris.aneris_lang Require Import aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Import state_interp_def state_interp_adversary_firewall_coh.
From RecordUpdate Require Import RecordSet.
From aneris.algebra Require Import disj_gsets.
From iris.algebra Require Import auth.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Lemma messages_resource_coh_init B :
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (◯ (DGSets B)) -∗
    messages_resource_coh (gset_to_gmap (∅, ∅) B).
  Proof.
    rewrite /messages_resource_coh messages_sent_init.
    iIntros "Hown".
    iSplitL; [ |].
    { by rewrite dom_gset_to_gmap. }
    iExists _.
    iSplit; [done|].
    iSplit; by iApply big_sepS_empty.
  Qed.

  (* TODO: Repeated lemma - Why is anerisG needed over anerisPreG? *)
  Lemma socket_address_group_own_subseteq
        γ (sags sags' : gset socket_address_group) :
    sags' ⊆ sags →
    own (A:=(authR socket_address_groupUR)) γ
        (◯ (DGSets sags)) -∗
    own (A:=(authR socket_address_groupUR)) γ
        (◯ (DGSets sags')).
  Proof.
    iIntros (Hle) "Hsags".
    apply subseteq_disjoint_union_L in Hle.
    destruct Hle as [Z [-> Hdisj]].
    setoid_rewrite <-disj_gsets_op_union.
    iDestruct "Hsags" as "[H1 H2]".
    iFrame.
  Qed.

  Lemma messages_resource_coh_socket_address_group_own
        (sag : socket_address_group) mh :
    sag ∈ dom mh →
    messages_resource_coh mh -∗
    messages_resource_coh mh ∗
    socket_address_group_own sag.
  Proof.
    iIntros (Hin) "[#H Hrest]".
    rewrite /socket_address_group_own.
    iPoseProof (socket_address_group_own_subseteq _ _ {[sag]} with "H") as "$";
      [set_solver|].
    rewrite /messages_resource_coh. iFrame "H".
    done.
  Qed.

  Lemma messages_resource_coh_send mh sagT sagR R T msg msg' ϕ :
    mh !! sagT = Some (R, T) →
    m_sender msg ∈ sagT →
    messages_addresses_coh mh →
    msg ≡g{sagT, sagR} msg' →
    adversary_saddr_nonadv_own (m_sender msg) -∗
    m_destination msg ∈g sagR -∗
    sagR ⤇* ϕ -∗
    messages_resource_coh mh -∗
    ϕ msg' -∗
    messages_resource_coh (<[sagT:=(R, {[msg]} ∪ T)]> mh).
  Proof.
    rewrite /messages_resource_coh /=.
    iIntros (Hmh HsagT Hmcoh Hmeq) "#Hnonadv [%HsagR _] #HΦ [#Hown Hcoh] Hm".
    iAssert (socket_address_group_own sagT) as "HownT".
    {
      rewrite -(insert_id mh sagT (R,T)); [|set_solver].
      rewrite dom_insert_L.
      rewrite -disj_gsets_op_union.
      rewrite auth_frag_op.
      iDestruct "Hown" as "[$ Hown]".
    }
    destruct Hmcoh as (Halldisj & Hne & Hmcoh).
    iDestruct "Hcoh" as (ms Hle) "[#HcohT Hcoh]".
    iDestruct (socket_interp_own with "HΦ") as "#Hown'".
    iSplitR.
    {
      rewrite dom_insert_L.
      rewrite -disj_gsets_op_union.
      rewrite auth_frag_op.
      iApply own_op.
      iFrame "Hown HownT".
    }
    iExists ({[msg]} ∪ ms).
    iSplitR.
    {
      iPureIntro.
      rewrite messages_sent_insert.
      rewrite -union_assoc_L.
      rewrite -(messages_sent_split sagT R T mh Hmh).
      set_solver.
    }
    iSplitR.
    {
      rewrite messages_sent_insert.
      rewrite -union_assoc_L.
      rewrite -(messages_sent_split sagT R T mh Hmh).
      rewrite !big_sepS_forall.
      iIntros (m' Hin).
      setoid_rewrite elem_of_union in Hin.
      destruct Hin as [Hin|Hin].
      {
        iRight; iRight.
        assert (m' = msg) as <- by set_solver.
        iExists sagT, sagR, m'.
        iSplit; [iSplit; [|iPureIntro; set_solver] |].
        { iPureIntro. apply message_group_equiv_refl.
          - by destruct Hmeq as (Hmin & _).
          - done. }
        iFrame "HownT Hown'".
      }
      iDestruct ("HcohT" $!(m') (Hin)) as "[Hadv|[Hadv|HcohT']]".
      - iLeft; done.
      - iRight; iLeft; done.
      - iRight; iRight.
        iDestruct "HcohT'" as (sagT' sagR' m'' [Hmeq' Hmin]) "[HownT'' HownR]".
        iExists sagT', sagR', m''.
        apply (elem_of_union_r m'' {[msg]} ms) in Hmin.
        iFrame "#".
        iSplit; [done|]. iPureIntro. done.
    }
    destruct (decide (msg ∈ ms)).
    {
      assert ({[msg]} ∪ ms = ms) as -> by set_solver. iClear "Hm".
      assert (ms ⊆ {[msg]} ∪ messages_sent mh) by set_solver.
      rewrite /message_received.
      rewrite !messages_received_insert.
      iApply (big_sepS_mono with "Hcoh").
      iIntros (x Hin') "Hcoh".
      iDestruct "Hcoh" as (sagT' sagR' m') "(%Hequiv & #Hsi & #HownT' & Hopt)".
      iExists sagT', sagR', m'.
      iSplitL ""; [done |].
      iFrame "#".
      iDestruct "Hopt" as "[Hl | Hr]".
      - iLeft; done.
      - iRight.
        iDestruct "Hr" as (m'') "(%&%Hrecv)".
        iPureIntro.
        exists m''.
        rewrite -(insert_id mh sagT (R,T) Hmh) in Hrecv.
        apply message_received_insert in Hrecv.
        eauto with set_solver.
    }
    (* msg ∉ ms*)
    rewrite big_sepS_union; [|set_solver].
    rewrite big_sepS_singleton.
    iSplitL "Hm".
    + iExists sagT, sagR, ϕ.
      iSplitL ""; [by iPureIntro|].
      iFrame "HΦ #".
      iLeft.
      eauto with iFrame.
    + iApply (big_sepS_mono with "Hcoh").
      iIntros (x Hin') "Hcoh".
      iDestruct "Hcoh" as (sagT' sagR' Φ') "(%Hin & #Hproto & [#? Hopt])".
      iExists sagT', sagR', Φ'.
      iSplitL ""; [done |].
      iFrame "#".
      iDestruct "Hopt" as "[Hres | Hrec]".
      * iLeft; done.
      * iRight.
        iDestruct "Hrec" as (m') "[% %Hrecv]".
        iExists m'. iPureIntro.
        split; [done|].
        rewrite -(insert_id mh sagT (R,T) Hmh) in Hrecv.
        rewrite message_received_insert.
        apply message_received_insert in Hrecv.
        done.
  Qed.

  Lemma messages_resource_coh_send_duplicate mh σ sags sagT sagR R T msg :
    mh !! sagT = Some (R, T) →
    m_sender msg ∈ sagT →
    messages_addresses_coh mh →
    set_Exists (λ m, m ≡g{sagT, sagR} msg) T →
    adversary_saddr_nonadv_own (m_sender msg) -∗
    adversary_firewall_coh σ sags -∗
    socket_address_group_ctx sags -∗
    m_destination msg ∈g sagR -∗
    messages_resource_coh mh -∗
      messages_resource_coh (<[sagT:=(R, {[msg]} ∪ T)]> mh).
  Proof.
    rewrite /messages_resource_coh /=.
    iIntros (Hmh HsagT Hmcoh Hexists) "#Hnon Hadvcoh Hsag [%HsagR #Hown'] [#Hown Hcoh]".
    iAssert (socket_address_group_own sagT) as "HownT".
    {
      rewrite -(insert_id mh sagT (R,T)); [|set_solver].
      rewrite dom_insert_L.
      rewrite -disj_gsets_op_union.
      rewrite auth_frag_op.
      iDestruct "Hown" as "[$ Hown]".
    }
    destruct Hmcoh as (Halldisj & Hne & Hmcoh).
    iDestruct "Hcoh" as (ms Hle) "[#Hcoh Hms]".
    iSplitR.
    {
      rewrite dom_insert_L.
      rewrite -disj_gsets_op_union.
      rewrite auth_frag_op.
      iApply own_op.
      iFrame "Hown HownT".
    }
    destruct Hexists as [m' [Hin Hmeq]].
    assert (m_destination m' ∈ sagR).
    { by destruct Hmeq as (_ & _ & H' & _). }
    rewrite -{2}(insert_id mh sagT (R,T)); [|set_solver].
    rewrite messages_sent_insert.
    iDestruct (big_sepS_elem_of_acc _ _ m' with "Hcoh") as "[Hmsg _]";
      [set_solver|].
    iDestruct "Hmsg" as "[#Hadv_send|[#Hadv_dest|#Hreg]]".
    - (* the sender's an adversary: contradiction *)
      iExFalso.
      iDestruct (adversary_saddr_adv_own_equiv_sender with "Hadvcoh Hsag HownT [] Hadv_send") as "(_&_&#Hcontra)".
      { iPureIntro; eauto. }
      iApply (adversary_saddr_adv_nonadv_own with "Hcontra Hnon").
    - (* the destination's an adversary: then our destination must be an adversary too *)
      iExists ms.
      iSplitL "".
      { iPureIntro.
        rewrite messages_sent_insert.
        rewrite -union_assoc_L.
        rewrite -(messages_sent_split sagT R T mh Hmh).
        set_solver. }
      iSplitL "Hadvcoh Hsag".
      { rewrite messages_sent_insert.
        rewrite -union_assoc_L.
        rewrite -(messages_sent_split sagT R T mh Hmh).
        destruct (decide (msg ∈ messages_sent mh)) as [Hin'|Hout].
        + iAssert ⌜({[msg]} ∪ messages_sent mh = messages_sent mh)⌝%I as "%Heq".
          { iPureIntro.
            set_solver. }
          rewrite Heq.
          iFrame "#".
        + iApply big_sepS_union; [set_solver|].
          iSplitL "Hadvcoh Hsag".
          { iApply big_sepS_singleton.
            iRight; iLeft.
            iDestruct (adversary_saddr_adv_own_equiv_destination with "Hadvcoh Hsag Hown' [] Hadv_dest") as "(_&_&#?)".
            { by iPureIntro. }
            iFrame "#". }
          iFrame "#". }
      iApply (big_sepS_mono with "Hms").
      iIntros (m Hin') "Hms".
      iDestruct "Hms" as (sagT' sagR' Φ) "(#Hdest&#Hsp&?&Hopts)".
      iExists sagT', _, _.
      iFrame "#∗".
      iDestruct "Hopts" as "[H1|H2]"; [iLeft; done|iRight].
      iDestruct "H2" as (?) "[? ?]".
      iExists _. iFrame.
      rewrite -{1}(insert_id mh sagT (R, T)); [|done].
      do 2 rewrite message_received_insert.
      done.
    - (* the standard case where none of the endpoints are necessarily adversaries *)
      (* TODO: this case is very similar to the previous one: refactor if possible *)
      iExists ms.
      iSplitL "".
      { iPureIntro.
        rewrite messages_sent_insert.
        rewrite -union_assoc_L.
        rewrite -(messages_sent_split sagT R T mh Hmh).
        set_solver. }
      iSplitL "Hadvcoh Hsag".
      { rewrite messages_sent_insert.
        rewrite -union_assoc_L.
        rewrite -(messages_sent_split sagT R T mh Hmh).
        destruct (decide (msg ∈ messages_sent mh)) as [Hin'|Hout].
        + iAssert ⌜({[msg]} ∪ messages_sent mh = messages_sent mh)⌝%I as "%Heq".
          { iPureIntro.
            set_solver. }
          rewrite Heq.
          iFrame "#".
        + iApply big_sepS_union; [set_solver|].
          iSplitL "Hadvcoh Hsag".
          { iApply big_sepS_singleton.
            iRight; iRight.
            iDestruct "Hreg" as (sagT' sagR' m'') "([%Hequiv %Hin'']&HownT'&HownR')".
            iExists sagT', sagR', m''.
            iFrame "#".
            iAssert (socket_address_groups_own
                       ({[sagT]} ∪ {[sagR]} ∪ {[sagT']} ∪ {[sagR']})) as "H".
            {
              iApply socket_address_groups_own_union. iFrame "HownR'".
              iApply socket_address_groups_own_union. iFrame "HownT'".
              iApply socket_address_groups_own_union. iFrame "Hown' HownT".
            }
            iDestruct (own_valid with "H") as %Hvalid.
            setoid_rewrite auth_frag_valid in Hvalid.
            setoid_rewrite disj_gsets_valid in Hvalid.
            iPureIntro.
            pose proof (message_group_equiv_trans _ sagT sagT' sagR sagR' msg m' m'' Hvalid) as (<- & <- & Hmeq'');
                                                        [set_solver|set_solver|set_solver|set_solver | |done |done].
            apply message_group_equiv_symmetry; done. }
          iFrame "#". }
      iApply (big_sepS_mono with "Hms").
      iIntros (m Hin') "Hms".
      iDestruct "Hms" as (sagT' sagR' Φ) "(#Hdest&#Hsp&?&Hopts)".
      iExists sagT', _, _.
      iFrame "#∗".
      iDestruct "Hopts" as "[H1|H2]"; [iLeft; done|iRight].
      iDestruct "H2" as (?) "[? ?]".
      iExists _. iFrame.
      rewrite -{1}(insert_id mh sagT (R, T)); [|done].
      do 2 rewrite message_received_insert.
      done.
  Qed.

  Lemma message_received_delete m mh sag1 sag2 :
    messages_addresses_coh mh →
    m_destination m ∈ sag1 →
    sag1 ∈ dom mh →
    sag2 ∈ dom mh →
    sag1 ≠ sag2 →
    message_received m mh →
    message_received m (delete sag2 mh).
  Proof.
    rewrite /message_received.
    rewrite !elem_of_messages_received.
    intros (Hdisj & Hne & Hcoh) Hdest Hsag1 Hsag2 Hrecv
           [sag [[R T] [Hlookup Hin]]].
    assert (sag = sag1) as ->.
    {
      eapply elem_of_all_disjoint_eq; eauto.
      apply elem_of_dom. eexists _. set_solver.
      eapply Hcoh. eauto. eauto.
    }
    eexists sag1, (R,T).
    rewrite lookup_delete_ne; last done.
    auto.
  Qed.

  (* TODO: Clean up these lemmas and proofs *)
  Lemma messages_resource_coh_receive_in sagR sagT R T R' T' m mh :
    mh !! sagR = Some (R, T) →
    mh !! sagT = Some (R',T') →
    set_Forall (λ m', ¬ (m ≡g{sagT,sagR} m')) R →
    m ∈ T' →
    messages_addresses_coh mh →
    adversary_saddr_nonadv_own (m_destination m) -∗
    m_destination m ∈g sagR -∗
    m_sender m ∈g sagT -∗
    messages_resource_coh mh -∗
      messages_resource_coh (<[sagR:=({[m]} ∪ R, T)]> mh) ∗
      ((∃ φ m', ⌜m ≡g{sagT,sagR} m'⌝ ∗ sagR ⤇* φ ∗ ▷ φ m') ∨
       (adversary_saddr_adv_own (m_sender m))).
  Proof.
    iIntros (Hmha Hmhb HmR HmT' (Hdisj & Hne & Hmacoh)).
    iIntros "#Hdestnon [%Hmdest _] [%Hmsend _]".
    iDestruct 1 as "[#Hown Hrcoh]". rewrite /messages_resource_coh.
    iDestruct "Hrcoh" as (ms Hle) "[#HrcohT Hrcoh]".
    assert (messages_sent mh = messages_sent (<[sagT:=(R', T')]>mh)) as Heq.
    { apply insert_id in Hmhb as Heq. by rewrite {1} Heq. }
    rewrite Heq messages_sent_insert.
    assert (T' = {[m]} ∪ T') as HTeq by set_solver.
    rewrite HTeq.
    iDestruct (big_sepS_elem_of_acc _ _ m with "HrcohT")
      as "[Hm _]"; [set_solver|].
    assert (messages_sent (<[sagR:=({[m]} ∪ R, T)]> mh) = messages_sent mh) as ->.
    { rewrite -{2}(insert_id mh sagR (R, T)); [|done].
      rewrite !messages_sent_insert; done. }
    iDestruct "Hm" as "[Hadv_send | [Hadv_dest | Hequiv]]".
    - (* the sender is an adversary: in this case, what we get out of the state interp
         is that the received message came from an adversary *)
      iSplitR ""; last first.
      { iRight. done. }
      iSplitL "".
      { rewrite dom_insert_lookup_L; [iFrame "#"|].
        eauto. }
      iExists ms.
      iSplitL ""; [by iPureIntro|].
      iSplitL "".
      { rewrite -HTeq -(messages_sent_insert _ R' T') -Heq.
        iApply (big_sepS_mono with "HrcohT").
        eauto. }
      iApply (big_sepS_mono with "Hrcoh").
      iIntros (x Hin) "H".
      iDestruct "H" as (sagT'' sagR'' Φ'') "(?&?&?&Hopt)".
      iExists sagT'', sagR'', Φ''.
      iFrame.
      iDestruct "Hopt" as "[H1|H2]".
      + iDestruct "H1" as (m'') "[#Hequiv HΦ'']".
        iLeft.
        eauto with iFrame.
      + iDestruct "H2" as (m'') "[#Hequiv %Hrecv]".
        iRight.
        iExists m''.
        iFrame "#".
        iPureIntro.
        rewrite message_received_insert.
        rewrite -(insert_id mh sagR (R, T)) in Hrecv; [ | done].
        rewrite message_received_insert in Hrecv.
        destruct Hrecv; [eauto with set_solver|eauto].
    - (* the destination is an adversary:contradiction *)
      iExFalso.
      iApply (adversary_saddr_adv_nonadv_own with "Hadv_dest Hdestnon").
    - iAssert (⌜∃ m', m ≡g{sagT,sagR} m' ∧ m' ∈ ms⌝%I) as %(m' & Hmeq & Hmin).
      { iDestruct "Hequiv" as (sagT' sagR' m' [Hmeq Hmin]) "[HownT' HownR']".
        assert (sagR ∈ dom mh).
        { apply elem_of_dom. eexists _. set_solver. }

        iAssert (socket_address_group_own sagT) as "HownT".
        {
          rewrite -(insert_id mh sagT (R',T')); [|set_solver].
          rewrite dom_insert_L.
          rewrite -disj_gsets_op_union.
          rewrite auth_frag_op.
          iDestruct "Hown" as "[$ Hown]".
        }
        iAssert (socket_address_group_own sagR) as "HownR".
        {
          rewrite -(insert_id mh sagR (R,T)); [|set_solver].
          rewrite dom_insert_L.
          rewrite -disj_gsets_op_union.
          rewrite auth_frag_op.
          iDestruct "Hown" as "[$ Hown]".
        }
        iAssert (socket_address_groups_own
                   ({[sagT]} ∪ {[sagR]} ∪ {[sagT']} ∪ {[sagR']})) as "Hown'".
        {
          iApply socket_address_groups_own_union. iFrame "HownR'".
          iApply socket_address_groups_own_union. iFrame "HownT'".
          iApply socket_address_groups_own_union. iFrame "HownR HownT".
        }
        iDestruct (own_valid with "Hown'") as %Hvalid.
        setoid_rewrite auth_frag_valid in Hvalid.
        setoid_rewrite disj_gsets_valid in Hvalid.
        assert (sagT = sagT') as <-.
        { eapply (message_group_equiv_dest_eq _
                  sagT sagT' sagR sagR' m m' Hvalid); try set_solver. }
        assert (sagR = sagR') as <-.
        { eapply (message_group_equiv_dest_eq _
                  sagT sagT sagR sagR' m m' Hvalid); try set_solver. }
        iPureIntro.
        eexists m'.
        done.
      }
      assert (ms = {[m']} ∪ (ms ∖ {[m']})) as ->.
      { rewrite -union_difference_L. eauto. set_solver. }
      iDestruct (big_sepS_union with "Hrcoh") as "[Hm' Hrcoh]"; [set_solver|].
      rewrite big_sepS_singleton.
      iDestruct "Hm'" as (sagT' sagR' Φ Hdest) "[#HΦ [#HownT' Hm]]".
      assert (sagR ∈ dom mh) as HsagR.
      { rewrite elem_of_dom. eexists _. set_solver. }
      iDestruct "Hm" as "[Hm | Hm]"; last first.
      {
        iDestruct "Hm" as %(m'' & Hmeq' & Hrecv).
        iAssert (socket_address_group_own sagT) as "HownT".
        {
          rewrite -(insert_id mh sagT (R',T')); [|set_solver].
          rewrite dom_insert_L.
          rewrite -disj_gsets_op_union.
          rewrite auth_frag_op.
          iDestruct "Hown" as "[$ Hown]".
        }
        iAssert (socket_address_group_own sagR) as "HownR".
        {
          rewrite -(insert_id mh sagR (R,T)); [|set_solver].
          rewrite dom_insert_L.
          rewrite -disj_gsets_op_union.
          rewrite auth_frag_op.
          iDestruct "Hown" as "[$ Hown]".
        }
        iDestruct (socket_interp_own with "HΦ") as "HownR'".
        iAssert (socket_address_groups_own
                   ({[sagT]} ∪ {[sagT']} ∪ {[sagR]} ∪ {[sagR']})) as "Hown'".
        {
          iApply socket_address_groups_own_union. iFrame "HownR'".
          iApply socket_address_groups_own_union. iFrame "HownR".
          iApply socket_address_groups_own_union. iFrame "HownT' HownT".
        }
        iDestruct (own_valid with "Hown'") as %Hvalid.
        setoid_rewrite auth_frag_valid in Hvalid.
        setoid_rewrite disj_gsets_valid in Hvalid.
        assert (m ≡g{sagT, sagR} m'') as Hmeq''.
        {  eapply (message_group_equiv_trans _ sagT sagT' sagR sagR' m m' m''); eauto.
           set_solver. set_solver. set_solver. set_solver. }
        assert (m_destination m'' ∈ sagR).
        { by eapply message_group_equiv_dest. }
        assert (m'' ∈ R).
        { eapply messages_received_in; eauto.
          by rewrite /messages_addresses_coh. }
        assert (¬ m ≡g{sagT,sagR} m'').
        { by apply HmR. }
        done.
      }
      iDestruct "Hm" as (m'' Hmeq') "Hm'".
      iAssert (socket_address_group_own sagT) as "HownT".
      {
        rewrite -(insert_id mh sagT (R',T')); [|set_solver].
        rewrite dom_insert_L.
        rewrite -disj_gsets_op_union.
        rewrite auth_frag_op.
        iDestruct "Hown" as "[$ Hown]".
      }
      iAssert (socket_address_group_own sagR) as "HownR".
      {
        rewrite -(insert_id mh sagR (R,T)); [|set_solver].
        rewrite dom_insert_L.
        rewrite -disj_gsets_op_union.
        rewrite auth_frag_op.
        iDestruct "Hown" as "[$ Hown]".
      }
      iDestruct (socket_interp_own with "HΦ") as "HownR'".
      iAssert (socket_address_groups_own
                 ({[sagT]} ∪ {[sagR]} ∪ {[sagT']} ∪ {[sagR']})) as "Hown'''".
      {
        iApply socket_address_groups_own_union. iFrame "HownR'".
        iApply socket_address_groups_own_union. iFrame "HownT'".
        iApply socket_address_groups_own_union. iFrame "HownT HownR".
      }
      iDestruct (own_valid with "Hown'''") as %Hvalid.
      setoid_rewrite auth_frag_valid in Hvalid.
      setoid_rewrite disj_gsets_valid in Hvalid.
      assert (sagR' = sagR) as ->.
      {
        symmetry.
        eapply (message_group_equiv_trans _ sagT sagT' sagR sagR' m m' m'' Hvalid);
          set_solver. }
      iSplitR "Hm'"; last first.
      {
        iLeft.
        iExists Φ, m''. iFrame "HΦ Hm'". iPureIntro.
        eapply message_group_equiv_trans; eauto.
        set_solver. set_solver. set_solver. set_solver.
      }
      iSplitR.
      { rewrite dom_insert_lookup_L; eauto. }
      iExists ms.
      iSplitR; [done|].
      assert (ms = {[m']} ∪ (ms ∖ {[m']})) as Hms.
      { rewrite -union_difference_L. eauto. set_solver. }
      iSplitR.
      {
        rewrite -HTeq -Hms.
        rewrite -(messages_sent_insert sagT R' T' mh).
        rewrite insert_id; [|done].
        iApply "HrcohT".
      }
      rewrite {4} Hms.
      rewrite (big_sepS_union _ {[m']} (ms ∖ {[m']})); last set_solver.
      rewrite big_sepS_singleton.
      iSplitR.
      { iExists sagT, sagR, Φ.
        iSplit; [iPureIntro; set_solver | ].
        iFrame "HΦ".
        iFrame "HownT".
        iRight.
        iExists m.
        iPureIntro.
        split; [by apply message_group_equiv_symmetry | ].
        rewrite message_received_insert.
        set_solver.
      }
      iApply (big_sepS_impl with "Hrcoh").
      iIntros "!>" (m''' Hmin') "Hrcoh".
      iDestruct "Hrcoh" as (sagT'' sagR' Φ' Hmin'') "[#HΦ' [#HownT'' H]]".
      iExists sagT'', sagR', Φ'.
      iFrame "#".
      iSplit; [done|].
      iDestruct "H" as "[H|H]"; [ by iFrame | iRight ].
      iDestruct "H" as %(m'''' & Hmeq''' & Hrecv).
      assert (m_destination m'''' ∈ sagR').
      { eapply message_group_equiv_dest; eauto. }
      pose proof Hrecv as Hrecv'.
      rewrite /message_received in Hrecv'.
      setoid_rewrite elem_of_messages_received in Hrecv'.
      destruct Hrecv' as (sag & [R'' T''] & Hlookup & Hin).
      simpl in *.
      iAssert (socket_address_group_own sag) as "Hown''''".
      {
        rewrite -(insert_id mh sag (R'',T'')); [|set_solver].
        rewrite dom_insert_L.
        rewrite -disj_gsets_op_union.
        rewrite auth_frag_op.
        iDestruct "Hown" as "[$ Hown]".
      }
      iDestruct (socket_interp_own with "HΦ'") as "Hown'''''".
      iDestruct (own_op with "[Hown'''' Hown''''']") as "Hown''''''".
      { iSplitL "".
        - iFrame "Hown''''".
        - iFrame "Hown'''''".
      }
      rewrite -auth_frag_op.
      iDestruct (own_valid with "Hown''''''") as %Hvalid'.
      setoid_rewrite auth_frag_valid in Hvalid'.
      setoid_rewrite disj_gsets_valid in Hvalid'.
      iPureIntro. exists m''''.
      split; [done|].
      rewrite message_received_insert.
      destruct (decide (sagR' = sagR)) as [->|Hneq]; [left|right].
      { apply elem_of_union_r. by eapply messages_received_in. }
      rewrite /message_received.
      rewrite !elem_of_messages_received.
      assert (sag = sagR') as ->.
      {
        eapply (elem_of_all_disjoint_eq sag sagR' (m_destination m'''')); eauto.
        set_solver. set_solver.
        eapply Hmacoh; eauto.
      }
      eexists _, _.
      rewrite lookup_delete_ne; last done.
      split; [done|done].
  Qed.

  Lemma messages_resource_coh_receive_nin sagR sagT R T R' T' m mh :
    mh !! sagR = Some (R, T) →
    mh !! sagT = Some (R',T') →
    m ∈ T' →
    messages_addresses_coh mh →
    m_destination m ∈g sagR -∗
    m_sender m ∈g sagT -∗
    messages_resource_coh mh -∗
    messages_resource_coh (<[sagR:=({[m]} ∪ R, T)]> mh).
  Proof.
    iIntros (Hmha Hmhb HmT' (Hdisj & Hne & Hmacoh)).
    iIntros "[%Hmdest _] [%Hmsend _] Hrcoh".
    iDestruct "Hrcoh" as "[#Hown Hrcoh]".
    iDestruct "Hrcoh" as (ms Hle) "[HrcohT Hrcoh]".
    rewrite /messages_resource_coh.
    rewrite dom_insert_L.
    iAssert (socket_address_group_own sagR) as "HownR".
    {
      rewrite -(insert_id mh sagR (R,T)); [|set_solver].
      rewrite dom_insert_L.
      rewrite -disj_gsets_op_union.
      rewrite auth_frag_op.
      iDestruct "Hown" as "[$ Hown]".
    }
    iSplitR.
    {
      rewrite -disj_gsets_op_union.
      rewrite auth_frag_op.
      iSplit. iApply "HownR". iApply "Hown".
    }
    iExists ms.
    iSplit.
    { rewrite messages_sent_insert.
      rewrite <- (insert_id _ sagR (R,T)) in Hle; auto.
      rewrite messages_sent_insert in Hle.
      iPureIntro.
      set_solver. }
    iSplitR "Hrcoh".
    {
      rewrite messages_sent_insert.
      rewrite -(messages_sent_split sagR R T mh Hmha).
      done.
    }
    iApply (big_sepS_impl with "Hrcoh").
    iIntros "!>" (m'' Hmin') "H".
    iDestruct "H" as (sagT' sagR' Φ Hdest) "(#Hsag' & HsagT & [H | H])".
    {
      iDestruct "H" as (m''' Hmeq') "HΦ".
      iExists sagT', sagR', Φ.
      iSplit; [done|].
      iSplit; [done|].
      iSplit; [done|].
      iLeft. eauto.
    }
    iDestruct "H" as %(m''' & Hmeq' & Hrecv).
    iExists sagT', sagR', Φ.
    iSplit; [done|].
    iSplit; [done|].
    iSplit; [done|].
    iRight.
    assert (m_destination m''' ∈ sagR').
    { eapply message_group_equiv_dest; eauto. }
    pose proof Hrecv as Hrecv'.
    rewrite /message_received in Hrecv'.
    setoid_rewrite elem_of_messages_received in Hrecv'.
    destruct Hrecv' as (sag & [R'' T''] & Hlookup & Hin).
    simpl in *.
    iAssert (socket_address_group_own sag) as "Hown'".
    {
      rewrite -(insert_id mh sag (R'',T'')); [|set_solver].
      rewrite dom_insert_L.
      rewrite -disj_gsets_op_union.
      rewrite auth_frag_op.
      iDestruct "Hown" as "[$ Hown]".
    }
    iDestruct (socket_interp_own with "Hsag'") as "Hown''".
    iDestruct (own_op with "[Hown' Hown'']") as "Hown'''".
    { iSplitL ""; [ iApply "Hown'" | iApply "Hown''" ]. }
    rewrite -auth_frag_op.
    iDestruct (own_valid with "Hown'''") as %Hvalid'.
    setoid_rewrite auth_frag_valid in Hvalid'.
    setoid_rewrite disj_gsets_valid in Hvalid'.
    iPureIntro. exists m'''.
    split; [done|].
    rewrite message_received_insert.
    destruct (decide (sagR' = sagR)) as [->|Hneq]; [left|right].
    { apply elem_of_union_r. by eapply messages_received_in. }
    assert (sag = sagR') as ->.
    {
      eapply (elem_of_all_disjoint_eq sag sagR' (m_destination m''')); eauto.
      set_solver. set_solver.
      eapply Hmacoh. eauto. eauto.
    }
    rewrite /message_received.
    rewrite !elem_of_messages_received.
    eexists _, _.
    rewrite lookup_delete_ne; last done.
    split; [done|done].
  Qed.

  (*
  Lemma messages_resource_coh_receive sagR sagT R T R' T' m mh :
    mh !! sagR = Some (R, T) →
    mh !! sagT = Some (R',T') →
    m ∈ T' →
    messages_addresses_coh mh →
    m_destination m ∈g sagR -∗
    m_sender m ∈g sagT -∗
    messages_resource_coh mh -∗
    messages_resource_coh (<[sagR:=({[m]} ∪ R, T)]> mh) ∗
    (adversary_saddr_nonadv_own (m_destination m) -∗
     ⌜set_Forall (λ m', ¬ (m ≡g{sagT,sagR} m')) R⌝ -∗
       ∃ φ m', ⌜m ≡g{sagT,sagR} m'⌝ ∗ sagR ⤇* φ ∗ ▷ φ m').
  Proof.
    iIntros (Hmha Hmhb HmT' Hcoh).
    iIntros "HsagR HsagT Hcoh".
    destruct (decide (set_Forall (λ m', ¬ (m ≡g{sagT,sagR} m')) R)).
    - iDestruct (messages_resource_coh_receive_in with "HsagR HsagT Hcoh")
        as "[Hcoh Hφ]"; [ by eauto.. |].
      by iFrame.
    - iDestruct (messages_resource_coh_receive_nin with "HsagR HsagT Hcoh")
        as "[Hcoh Hφ]"; [ by eauto.. |].
      iFrame. by iIntros (H).
  Qed.
  *)

End state_interpretation.
