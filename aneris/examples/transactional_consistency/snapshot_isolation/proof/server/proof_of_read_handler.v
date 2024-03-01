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
From aneris.examples.transactional_consistency.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  user_params time events aux_defs resource_algebras.
From aneris.examples.transactional_consistency.snapshot_isolation.proof
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.server
     Require Import proof_of_utility_code.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Proof_of_read_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTrs).
  Import snapshot_isolation_code_api.
  Import assert_proof.

  Lemma kvs_get_last_spec 
    (M Mt : global_mem) (S Sg: snapshots) (T : nat)
    (k : Key) (t : nat) (h hc : whist)
    (m : gmap Key val) (kvsV : val) :
    (∀ e : events.write_event, e ∈ h → we_time e < t) →
    is_map kvsV m →
    kvsl_valid m M Sg T →
    kvs_valid M S T →
    M !! k = Some hc →
    S !! t = Some Mt →
    Mt !! k = Some h →
    {{{ ⌜True⌝ }}}
      kvs_get_last (#k, #t)%V kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (vo : option val), RET $vo;
        (⌜$vo = InjLV #()⌝ ∗ ⌜h = []⌝ ∨
        (∃ e : events.write_event, ⌜$vo = InjRV (we_val e)⌝ ∗
             ⌜hist_to_we h = Some e⌝)) }}}.
  Proof.
    iIntros (Hlt Hmv Hkvsl Hkvs Hmk Hst Hmtk Φ) "_ HΦ".
    wp_lam. do 15 wp_pures. destruct Hkvsl.
    (** We start by getting the versions at the key k. *)
    wp_smart_apply (kvs_get_spec_some _ _ _ _ _ _ k kvsV hc m M Hmv); eauto.
    iIntros (v) "%Hvres".
    eapply kvs_valid_single_snapshot in Hkvs;  try eauto.
    clear m Hmv kvsl_ValidDom kvsl_ValidInModelEmpty
      kvsl_ValidInModelSome kvsl_ValidLocalSome kvsl_ValidModel S Hst.
    (** Now we can proceed by induction on the list of versions hc. *)
    (iLöb as "IH" forall (v M hc Hmk Hvres Hkvs)).
    destruct (reverse hc) as [| e Hr] eqn:hceq.
    (** There are two cases to consider. First, assume that h is empty. *)
    - subst; simpl. wp_pures.
      iApply ("HΦ" $! None); eauto.
      iLeft; iPureIntro; split; first done.
      rewrite -reverse_nil in hceq. list_simplifier.
      destruct Hkvs, (kvs_ValidSnapshotTimesCuts t k h [] Mt)
        as (x & Hnil & _); try eauto; [ apply lookup_insert |].
      symmetry in Hnil. apply app_eq_nil in Hnil; naive_solver.
    (** Otherwise, there exists e and Hr such that 
       reverse hc = e :: Hr. We start by rewriting Hr so that
       we can later apply the induction hypothesis. *)
    - assert (∃ Hr', Hr = reverse Hr') as (Hr' & Hrr).
      { subst. destruct (reverse hc); first done. exists (reverse (Hr)).
        by rewrite reverse_involutive. }
      rewrite Hrr in hceq. rewrite Hrr in Hvres.
      clear Hrr Hr. rewrite Hvres.
      (** We now go throught the body of the function. *)
      wp_pures.
      (** First we prove that `ts` is indeed a start time,
       so no element `e` in the memory has it as a commit time. *)
      case_bool_decide.
      { assert False; [|done].
        destruct Hkvs, (kvs_ValidSnapshotTimesCuts t k h hc Mt)
          as (hr & Hd & Hlt' & Hgt'); try eauto; [apply lookup_insert|].
        assert (e ∈ h ∨ e ∈ hr) as Habs.
        { assert (e ∈ hc) as hce.
          { assert (e ∈ (reverse hc)).
            { rewrite hceq. apply elem_of_list_here. }
            by set_solver. }
          by set_solver. }
        destruct Habs as [Habs|Habs]. 
        - specialize (Hlt' e Habs); lia.
        - specialize (Hgt' e Habs); lia. }
      (** Otherwise, we have two cases depending on whether the time of `e`
          is smaller than the timestamp `t` or greater than it. *)
      wp_pures. case_bool_decide.
      (** In the case `e.t < ts`, we return the element `e`. *)
      { wp_pures. iApply ("HΦ" $! (Some (we_val e))).
        iRight. iExists e. iSplit; first done.
        (** It remains thus to prove that the element `e` is 
            indeed the snapshot of the transaction that started at 
            the time `ts`. *)
        iPureIntro. rewrite /hist_to_we -head_reverse.
        assert (Some e = head (reverse hc)) as Hek.
        { rewrite hceq. by list_simplifier. }
        rewrite Hek. do 2 f_equal.
        (** To prove this equality, we use the cuts invariant of the 
           coherence of the database together with the fact that the 
           snapshot of the transaction is valid, i.e. 
           ∀ e : events.write_event, e ∈ h → we_time e < ts. *)
        destruct Hkvs, (kvs_ValidSnapshotTimesCuts t k h hc Mt)
          as (hr & Heq & Hlt' & Hgt'); try eauto; [apply lookup_insert|].
        assert (reverse hc = reverse hr ++ reverse h) as Hreveq.
        { list_simplifier. by apply reverse_app. }
        rewrite Hreveq in hceq.
        assert (reverse hr = []) as Hrnil.
        { destruct (reverse hr) as [|x hrr] eqn:Hrev; first done.
          - assert (x = e) by naive_solver.
            assert (x ∈ reverse hr).
            { rewrite Hrev. set_solver. } 
            assert (x ∈ hr) as Hrin by set_solver.
            specialize (Hgt' x Hrin).
            subst. lia. }
        simplify_eq /=.
        rewrite Hrnil in Hreveq.
        by apply Inj_instance_2. }
      (** Finally, if `e.t > ts`, we proceed by induction. *)
      wp_pure _.
      iApply ("IH" $! ($(reverse Hr')) (<[ k := Hr']> M) Hr'
               with "[][//][][$HΦ]").
      + iPureIntro. by rewrite lookup_insert. 
      + iPureIntro.
        assert (map_included Mt M) as (Hi1 & Hi2).
        { destruct Hkvs.
          assert ((({[t := Mt]} : snapshots) !! t) = Some Mt)
            as Hinsr by apply lookup_insert.
          by specialize (kvs_ValidSnapshotTimesInclusion t Mt Hinsr)
            as (Hi1 & Hi2). }
        assert (k ∈ dom M) by by apply elem_of_dom; naive_solver.
        eapply (kvs_valid_global_mem_prefix
                  M ({[t := Mt]}) T t Mt ((<[k:=Hr']> M)));
          [eauto | apply lookup_insert | |].
        ++ split; first by set_solver.
           intros x hx Hhx.
           destruct (bool_decide (k = x)) eqn:Hkx.
           +++ apply bool_decide_eq_true in Hkx.
               subst. exists Hr'. rewrite lookup_insert. split; first done.
               rewrite Hhx in Hmtk. list_simplifier.
               destruct (Hi2 x h Hhx) as (hy & Hhy1 & Hhy2).
               rewrite Hhy1 in Hmk. list_simplifier.
               assert (hc = Hr' ++ [e]) as Heqhc.
               { apply Inj_instance_2. rewrite hceq.
                 by rewrite reverse_snoc. }
               rewrite Heqhc in Hhy2.
               destruct Hhy2 as (hsuf & Heq).
               assert (∃ hsuf', hsuf = hsuf' ++ [e]) as (hsuf' & ->). 
               { destruct (reverse hsuf) as [|z Hz] eqn:Hrev.
                 -  rewrite -reverse_nil in Hrev.
                    apply Inj_instance_2 in Hrev as ->.
                    rewrite app_nil_r in Heq.
                    assert (e ∈ h) as Habs.
                    { rewrite -Heq. set_solver. }
                    specialize (Hlt e Habs).
                    lia. 
                 - assert (hsuf = reverse Hz ++ [z]) as Hsufrev.
                   { apply Inj_instance_2. rewrite Hrev.
                     by rewrite
                          reverse_app reverse_involutive reverse_singleton. }
                   rewrite Hsufrev app_assoc in Heq.
                   apply app_inj_tail in Heq as (Hres & ->).
                   by exists (reverse Hz). }
               list_simplifier. by exists hsuf'.
           +++ apply bool_decide_eq_false in Hkx.
               destruct (Hi2 x hx Hhx) as (hy & Hhy1 & Hhy2).
               exists hy. by rewrite lookup_insert_ne; last done.
        ++ split; first by set_solver.
           intros x hx Hhx.
           destruct (bool_decide (k = x)) eqn:Hkx.
           +++ apply bool_decide_eq_true in Hkx.
               subst. rewrite lookup_insert in Hhx.
               eexists. list_simplifier. split; first done.
               exists [e]. apply Inj_instance_2. rewrite hceq.
               rewrite reverse_app. done.
           +++ apply bool_decide_eq_false in Hkx.
               rewrite lookup_insert_ne in Hhx; last done; eauto.
  Qed. 

  Lemma read_handler_spec
    (k : string) (lk : val) (kvs vnum : loc)
    (reqd : ReqData) (ts : nat) (h : whist)
    (Msnap : global_mem) (Φ : val → iPropI Σ) :
    k ∈ KVS_keys →
    reqd = inl (k, ts, h) →
    (∀ e : events.write_event, e ∈ h → we_time e < ts) →
    Msnap !! k = Some h →
    server_lock_inv γGauth γT γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT γTrs -∗
    ownTimeSnap γT ts -∗
    ownMemSeen γGsnap k h -∗
    ownSnapFrag γTrs ts Msnap -∗
    (∀ (repv : val) (repd : RepData),
       ⌜sum_valid_val (option_serialization KVS_serialization)
        (sum_serialization int_serialization bool_serialization) repv⌝ ∗
         ReqPost clients γKnownClients γGauth γGsnap γT γTrs repv reqd repd -∗
           Φ repv) -∗
    WP let: "res" := InjL
                     (acquire lk ;;
                      let: "res" := (λ: <>, kvs_get_last (#k, #ts)%V ! #kvs)%V
                                      #() in release lk ;; "res") in "res" @[
  ip_of_address KVS_address] {{ v, Φ v }}.
  Proof.
    iIntros (Hin Hreqd Hts Hsnap) "#Hlk #HGlobInv #HsnapT #HsnapH #HsnapS HΦ".
    (** We start by acquiring the lock and getting the lock invariant. *)
    wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (?) "(-> & Hlock & Hlkres)". wp_pures.
    iDestruct "Hlkres"
      as (M S T m kvsV Hmap Hvalid Hforall)
           "(HmemLoc & HtimeLoc & hcvsL & HvnumL)".
    wp_load. wp_apply fupd_aneris_wp.
    iInv KVS_InvName
      as (Mg Sg Tg gMg)
           ">((HmemG & HmemGmono) &
              HsnapsG & HtimeGlob & Hccls & %Hdom & %hcvsValid)".
    iDestruct (ownMemSeen_lookup with "[$HmemGmono][$HsnapH]") as "%HinM".
    iDestruct (ghost_map.ghost_map_auth_agree γGauth (1/2)%Qp (1/2)%Qp M
        with "[$HmemLoc][$HmemG]") as "<-".
    destruct HinM as (hc & Hpre & hcin).
    iDestruct (mono_nat.mono_nat_auth_own_agree
              with "[$HtimeGlob][$HtimeLoc]") as "(%_ & ->)".
    iDestruct (ownSnapAgree with "[$HsnapS][$HsnapsG]") as "%Hmt1".
    iSplitL "HtimeGlob HmemG HmemGmono Hccls HsnapsG".
    { iModIntro. iNext. iExists _, _, _, _. by iFrame "#∗". }
    do 2 iModIntro.
    (** Next, we apply the lemma above to 
        get the most recent element (if any) from the DB. *)
    wp_apply (kvs_get_last_spec M Msnap Sg S T k ts h hc m kvsV); try eauto.
    iIntros (vo) "[(-> & ->)|Hres]".
    - wp_pures. wp_smart_apply (release_spec with "[-HΦ]").
      iFrame "#∗". { do 5 iExists _. by iFrame "#∗". }
      iIntros (? ->). wp_pures.
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
      wp_pures. wp_smart_apply (release_spec with "[-HΦ]").
      iFrame "#∗". { do 5 iExists _. by iFrame "#∗". }
      iIntros (? ->).
      wp_pures.
      iApply ("HΦ" $! _ _).
      iSplit.
      -- iPureIntro. simplify_eq /=.
         exists (SOMEV (we_val e)). left. split; first done.
         left. exists (we_val e). split; first done.
         specialize (map_Forall_lookup_1 _ M k hc Hforall hcin).
         simpl. intros Hser1.
         destruct (Forall_forall (λ we, KVS_Serializable (we.(we_val))) hc)
           as [Hs1 _].  specialize (Hs1 Hser1). apply Hs1.
         rewrite /hist_to_we in Hhist. apply last_Some_elem_of in Hhist.
         by eapply elem_of_prefix.
      -- rewrite /ReqPost. iFrame "#". iLeft.
         iExists k, ts, h, _. iFrame "#∗".
         iPureIntro. split_and!; eauto.
  Qed.

End Proof_of_read_handler.
