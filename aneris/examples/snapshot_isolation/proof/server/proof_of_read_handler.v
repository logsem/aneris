From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model kvs_serialization rpc_user_params.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     resource_algebras server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Proof_of_read_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTss γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTss).
  Import snapshot_isolation_code_api.
  Import assert_proof.

  Lemma kvs_get_spec_aux (k : Key) (kvsV : val)
        (Hh : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   is_map kvsV m →
   M !! k = Some Hh →
   kvsl_in_model_empty_coh m M →
   kvsl_in_model_some_coh m M →
   kvsl_in_local_some_coh m M →
   {{{ ⌜True⌝ }}}
       kvs_get #k kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (vlo : option (list write_event)) (v : val), RET v;
        ⌜match vlo with
         | None =>
             v = NONEV ∧
             Hh = []
         | Some l =>
             v = $l ∧
             m !! k = Some v ∧
             l ≠ [] ∧
             l = reverse Hh
         end⌝
    }}}.
  Proof.
    iIntros (Hmap HMk Hc1 Hc2 Hc3 Φ) "_ HΦ".
    wp_lam.
    wp_pures.
    wp_apply (wp_map_lookup $! Hmap).
    iIntros (v) "%Hkv".
    destruct Hh as [|e h'] eqn:Heq; simplify_eq /=.
    - specialize (Hc1 k HMk).
      destruct (m !! k) as [hv | ] eqn:Hmk; first done.
      simplify_eq /=.
      do 3 wp_pure _.
      wp_pures.
      by iApply ("HΦ" $! None).
    - destruct (m !! k) as [hv | ] eqn:Hmk.
      2: { specialize (Hc2 k (e :: h') HMk).
           naive_solver. }
      assert (m !! k = Some $ (reverse (e :: h'))) as Hmk'.
      { by apply (Hc2 k (e :: h') HMk). }
      simplify_eq /=.
      specialize (Hc3 k (reverse (e :: h')) Hmk).
      do 3 wp_pure _.
      wp_smart_apply wp_assert.
      wp_pures.
      destruct ((reverse (e :: h'))) as [| x l] eqn:Hrev.
      -- rewrite reverse_nil in Hc3.
         by rewrite HMk in Hc3.
      -- wp_pures.
         iSplit; first done.
         iNext.
         wp_pures.
         by iApply ("HΦ" $! (Some (x :: l))).
  Qed.

  Lemma kvs_get_spec (k : Key) (kvsV : val) (h : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   is_map kvsV m →
   M !! k = Some h →
   kvsl_in_model_empty_coh m M →
   kvsl_in_model_some_coh m M →
   kvsl_in_local_some_coh m M →
   {{{ ⌜True⌝ }}}
       kvs_get #k kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (v : val), RET v; ⌜v = $ (reverse h)⌝ }}}.
  Proof.
    iIntros (???????) "Hp".
    iApply kvs_get_spec_aux; eauto.
    iNext.
    iIntros (vlo v Hvlo). 
    iApply "Hp".
    iPureIntro.
    destruct vlo; naive_solver.
  Qed.

  Lemma kvs_get_last_spec (k : Key) (ts : nat) (T : nat) (Tss Tssg : gset nat) (kvsV : val)
    (h Hk : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   (∀ e : events.write_event, e ∈ h → we_time e < ts) →
   is_map kvsV m →
   ts ∈ Tssg →
   kvsl_valid m M T Tss →
   kvs_valid M T Tssg →
   M !! k = Some Hk →
   h `prefix_of` Hk →
    {{{ ⌜True⌝
    }}}
        kvs_get_last (#k, #ts)%V kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (vo : option val), RET $vo;
        (⌜$vo = InjLV #()⌝ ∗ ⌜h = []⌝ ∨
        (∃ e : events.write_event, ⌜$vo = InjRV (we_val e)⌝ ∗
             ⌜hist_to_we h = Some e⌝))
    }}}.
  Proof.
    iIntros (Het Hm Hts Hcoh HcohM Hin Hpre Φ) "_ HΦ".
    wp_lam. do 15 wp_pures. destruct Hcoh.
    (** We start by getting the versions at the key k. *)
    wp_smart_apply (kvs_get_spec k kvsV Hk m M Hm Hin); eauto.
    iIntros (v) "%Hvlo".
    clear m Hm kvsl_ValidDom kvsl_ValidInModelEmpty
      kvsl_ValidInModelSome kvsl_ValidLocalSome
      kvsl_ValidModel Tss.
    (** Now we can proceed by induction on the list of versions Hk. *)
    (iLöb as "IH" forall (v M Hk Hin Hpre Hvlo HcohM)).
    destruct (reverse Hk) as [| e Hr] eqn:Hkeq.
    (** There are two cases to consider. 
        First, we assume that the history is empty.  *)
    - subst; simpl.
      wp_pures.
      iApply ("HΦ" $! None); eauto.
      iLeft; iPureIntro; split; first done.
      rewrite -reverse_nil in Hkeq.
      list_simplifier.
      by apply prefix_nil_inv in Hpre.
    (* Suppose now that there exists e and Hr such that 
       reverse Hk = e :: Hr. We start by rewriting Hr so that
       we can later apply the induction hypothesis. *)
    - assert (∃ Hr', Hr = reverse Hr') as (Hr' & Hrr).
      { subst. destruct (reverse Hk); first done. exists (reverse (Hr)).
        by rewrite reverse_involutive. }
      rewrite Hrr in Hkeq.
      rewrite Hrr in Hvlo.
      clear Hrr Hr.
      rewrite Hvlo.
      (** We now go throught the body of the function. *)
      wp_pures.
      (** First we prove that `ts` is indeed a start time,
       so no element `e` in the memory has it as a commit time. *)
      case_bool_decide.
      (** We prove it by contradiction. *)
      { assert False.
        destruct HcohM.
        destruct (kvs_ValidSnapshotTimesCuts k Hk ts Hin Hts)
          as (hl & hr & Hd & Hlt & Hgt).
        assert (e ∈ hl ∨ e ∈ hr) as Habs.
        { assert (e ∈ Hk) as Hke.
          { assert (e ∈ (reverse Hk)).
            { rewrite Hkeq. apply elem_of_list_here. }
            by set_solver. }
          by set_solver. }
        destruct Habs as [Habs|Habs].
        - specialize (Hlt e Habs); lia.
        - specialize (Hgt e Habs); lia.
        - done. }
      wp_pures.
      (** Now we have two cases depending on whether the time of `e`
          is smaller than the timestamp `t` or greater than it. *)
      case_bool_decide.
      (** In the case `e.t < ts`, we return the element `e`. *)
      { wp_pures.
        iApply ("HΦ" $! (Some (we_val e))).
        iRight.
        iExists e.
        iSplit; first done.
        (** It remains thus to prove that the element `e` is 
            indeed the snapshot of the transaction that started at 
            the time `ts`. *)
        iPureIntro.
        (** We proceed by case analysis on whether e ∈ h ∨ e ∉ h. *)
        assert (e ∈ h ∨ e ∉ h) as [Heh|Heh].
        {  destruct (bool_decide (e ∈ h)) eqn:Heh.
           - apply bool_decide_eq_true in Heh; set_solver.
           - apply bool_decide_eq_false in Heh; set_solver.
        }
        (** Case (e ∈ h). The proof boils down to show that 
         the current history Hk and the snapshot history 
         are indeed the same, which intuitively true, since 
         e is the most recent element in the current history Hk. *)
        - rewrite /hist_to_we.
          rewrite -head_reverse.
          assert (Some e = head (reverse Hk)) as Hek.
          { rewrite Hkeq. by list_simplifier. }
          rewrite Hek.
          do 2 f_equal.
          (** To prove this equality, we use the cuts invariant of the 
           coherence of the database together with the fact that the 
           snapshot of the transaction is valid, i.e. 
           ∀ e : events.write_event, e ∈ h → we_time e < ts. *)
          destruct HcohM.
          destruct (kvs_ValidSnapshotTimesCuts k Hk ts Hin Hts)
              as (hl & hr & (Hc1 & Hc2 & Hc3)).
          destruct Hpre as (hr' & Hc1').
          apply Inj_instance_2.
          (** State, prove, and use a lemma about unicity of half-cut. *)
            admit.
        - (** Case (e ∉ h). This case is absurd, since by hypotheses, 
          we have e.t < ts, h prefix of Hk and e ∈ Hk. To show the 
          contradiction, we will use again the cut property. *)
          destruct HcohM.
          destruct (kvs_ValidSnapshotTimesCuts k Hk ts Hin Hts)
            as (hl & hr & (Hc1 & Hc2 & Hc3)).
          (** Prove by absurdity, using again the fact that hl = h. *)
          admit. }
      (** Finally, if ts < e.t, that means that e is a more recent element
       which is thus not in the snapshot of the current transaction, so 
       we conclude the proof by induction hypothesis. *)
      wp_pure _.
      iApply ("IH" $! ($(reverse Hr')) (<[ k := Hr']> M) Hr'
               with "[][][//][][$HΦ]").
      + iPureIntro. by rewrite lookup_insert. 
      + iPureIntro. list_simplifier.
        (* h prefix of Hk = Hr' ++ [e] and e ∉ h *) admit.
      + (** Use a weakining lemma. *)
        admit.
  Admitted.

  Lemma read_handler_spec
        (k : string)
        (lk : val)
        (kvs vnum : loc)
        (reqd : ReqData)
        (ts : nat)
        (h : list write_event)
        (Φ : val → iPropI Σ) :
    k ∈ KVS_keys →
    reqd = inl (k, ts, h) →
    (∀ e : events.write_event, e ∈ h → we_time e < ts) →
    server_lock_inv γGauth γT γTss γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT γTss -∗
    ownTimeSnap γT γTss ts -∗
    ownMemSeen γGsnap k h -∗
    (∀ (repv : val) (repd : RepData),
       ⌜sum_valid_val (option_serialization KVS_serialization)
        (sum_serialization int_serialization bool_serialization) repv⌝ ∗
         ReqPost clients γKnownClients γGauth γGsnap γT γTss repv reqd repd -∗
           Φ repv) -∗
    WP let: "res" := InjL
                     (acquire lk ;;
                      let: "res" := (λ: <>, kvs_get_last (#k, #ts)%V ! #kvs)%V
                                      #() in release lk ;; "res") in "res" @[
  ip_of_address KVS_address] {{ v, Φ v }}.
  Proof.
    iIntros (Hin Hreqd Hts) "#Hlk #HGlobInv #HsnapT #HsnapH HΦ".
    (** We start by acquiring the lock and getting the lock invariant. *)
    wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (?) "(-> & Hlock & Hlkres)".
    wp_pures.
    iDestruct "Hlkres"
      as (kvsV T Tss m M Hmap Hvalid Hforall)
           "(HmemLoc & HtimeLoc & #Hstarts & HkvsL & HvnumL)".
    wp_load.
    (** We also open the global system invariant as we will need 
        to unify variables M and Mg and T and Tg, and get additional pure facts. *)
    wp_apply fupd_aneris_wp.
    iInv KVS_InvName
      as (Mg Tg Tssg gMg)
           ">((HmemG & HmemGmono) &
             HtimeGlob & HtimeStartsGlob & Hccls & %Hdom & %HkvsValid)".
    iDestruct (ownMemSeen_lookup with "[$HmemGmono][$HsnapH]") as "%HinM".
     iAssert (⌜M = Mg⌝%I) as "<-".
    { rewrite /ownMemAuthLocal /ownMemAuthGlobal.
      iApply (ghost_map.ghost_map_auth_agree γGauth (1/2)%Qp (1/2)%Qp M
               with "[$HmemLoc][$HmemG]"). }
    destruct HinM as (Hk & Hpre & Hkin).
     iAssert (⌜ts ∈ Tssg⌝%I) as "%Hintss1".
     { rewrite /ownTimeSnap /ownTimeStartsSnap /ownTimeStartsAuth.
       iDestruct "HsnapT" as "(_ & HsnapT)".
       iDestruct (own_valid_2 with "HtimeStartsGlob HsnapT")
         as %[Hv'1 Hv'2]%auth_both_valid_discrete.
       apply gset_included in Hv'1; set_solver. }
     iAssert (⌜Tg = T⌝%I) as "->".
     { by iDestruct (mono_nat.mono_nat_auth_own_agree
                   with "[$HtimeGlob][$HtimeLoc]")
         as "(_ & <-)". }
     (** We can now close the global invariant. *)
    iSplitL "HtimeGlob HmemG HmemGmono Hccls HtimeStartsGlob".
    { iModIntro. iNext.
      iExists _, _, _, _.
      by iFrame "#∗".
    }
    iModIntro.
    iModIntro.
    (** Next, we apply the lemma above to get the most recent element (if any) from the DB. *)
    wp_apply (kvs_get_last_spec k ts T Tss Tssg kvsV h Hk); try eauto.
    (** We can now release the lock and conclude the proof in each of two cases. *)
    iIntros (vo) "[(-> & ->)|Hres]".
    - wp_pures.
      wp_smart_apply (release_spec with "[-HΦ]").
      iFrame "#∗".
      { rewrite /lkResDef.
        iExists  kvsV, _, _, m, M.
        by iFrame "#∗". }
      iIntros (? ->).
      wp_pures.
      iApply ("HΦ" $! _ _).
      iSplit. 
      -- iPureIntro. simplify_eq /=.
         eapply sum_is_ser_valid. rewrite /sum_is_ser.
         eexists (InjLV #()), _. left.  split; first eauto.
         simpl. split; last done. by left.
      -- rewrite /ReqPost.
         iFrame "#". iLeft. iExists k, ts, [], NONEV.
         iFrame "#∗". iPureIntro. split_and!; eauto.
    - iDestruct "Hres" as (e) "(-> & %Hhist)".
      wp_pures.
      wp_smart_apply (release_spec with "[-HΦ]").
      iFrame "#∗".
      { rewrite /lkResDef.
        iExists  kvsV, _, _, m, M.
        by iFrame "#∗". }
      iIntros (? ->).
      wp_pures.
      iApply ("HΦ" $! _ _).
      iSplit.
      -- iPureIntro. simplify_eq /=.
         exists (SOMEV (we_val e)). left. split; first done.
         left. exists (we_val e). split; first done.
         specialize (map_Forall_lookup_1 _ M k Hk Hforall Hkin).
         simpl. intros Hser1.
         destruct (Forall_forall (λ we, KVS_Serializable (we.(we_val))) Hk)
           as [Hs1 _].  specialize (Hs1 Hser1). apply Hs1.
         rewrite /hist_to_we in Hhist. apply last_Some_elem_of in Hhist.
         by eapply elem_of_prefix.
      -- rewrite /ReqPost. iFrame "#". iLeft.
         iExists k, ts, h, _. iFrame "#∗".
         iPureIntro. split_and!; eauto.
  Qed.

End Proof_of_read_handler.
