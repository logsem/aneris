From iris.algebra Require Import agree gmap auth.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     network tactics proofmode lifting lang.
From aneris.aneris_lang.lib Require Import network_util_proof lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec resources.
From aneris.examples.ccddb.examples.session_guarantees
     Require Import res sm_code.

Section spec.
  Context `{!anerisG Mdl Σ, !lockG Σ}.
  Context `{!DB_params}.
  Context `{!DB_time, !DB_events}.
  Context `{!DB_resources Mdl Σ}.
  Context `{!Maximals_Computing}.
  Context `{!inG Σ (authUR (gmapUR nat (agreeR (leibnizO log_req))))}.

  (* Session manager specs *)
  Variable client_addr : socket_address.

  Definition ip := ip_of_address client_addr.
  Lemma ip_eq : ip = ip_of_address client_addr. Proof. done. Qed.
  Typeclasses Opaque ip.
  Global Opaque ip.

  Definition mk_socket z :=
    {| sfamily := PF_INET;
       stype := SOCK_DGRAM;
       sprotocol := IPPROTO_UDP;
       saddress := Some z;
       sblock := true |}.

  Definition lock_inv (lsid : loc) (γ : gname) (sh : socket_handle) : iProp Σ :=
    (∃ (n : nat) (M : req_map) R S,
        lsid ↦[ip] #n (* connects lock invariant with dynamic check *)
        ∗ own γ (● M)
        ∗ (∀ m, ⌜m ≥ n⌝ -∗ ⌜m ∉ dom M⌝)
        ∗ sh ↪[ip] mk_socket client_addr
        ∗ client_addr ⤳ (R, S)
        ∗ ([∗ set] m ∈ R, ∃ (sid : seq_id) dres,
              ⌜s_is_ser resp_serialization
               (#sid, des_resp_to_val dres) (m_body m)⌝ ∗ ⌜sid < n⌝))%I.

  Theorem listen_wait_for_seqid_spec lsid M γ sh (n : seq_id) R S lrq :
    {{{ client_addr ⤇ client_si γ
        ∗ lsid ↦[ip] #n
        ∗ own γ (● M)
        (* this is not quite the loop invariant, since we have m >= n + 1
           instead of m >= n *)
        ∗ (∀ m, ⌜m ≥ n + 1⌝ -∗ ⌜m ∉ dom M⌝)
        ∗ sh ↪[ip] mk_socket client_addr
        ∗ client_addr ⤳ (R, S)
        ∗ ([∗ set] m ∈ R, ∃ (sid : seq_id) dres,
              ⌜s_is_ser resp_serialization
               (#sid, des_resp_to_val dres) (m_body m)⌝ ∗ ⌜sid < n⌝)
        ∗ is_req γ n lrq
    }}}

      listen_wait_for_seqid #(LitSocket sh) #lsid @[ip]
      {{{ v, RET v;
          lock_inv lsid γ sh
          ∗ ∃ dres vo, (⌜des_resp_to_val dres = v⌝ ∗ resp_body_post dres lrq vo)
      }}}.
  Proof.
    iIntros (Φ) "(#Hcsi & Hseq & Hown & #Hdom & Hsh & Hrs & HR & #Hisreq) Hcont".
    iLöb as "IH" forall (R).
    iDestruct "Hdom" as %Hdom.
    rewrite /listen_wait_for_seqid.
    wp_pures.
    rewrite ip_eq.
    wp_apply (aneris_wp_receivefrom _ client_addr _ sh (mk_socket client_addr) with "[$Hsh $Hrs $Hcsi]");
      [done | done | done | ].
    rewrite -ip_eq.
    iIntros (m) "[% [(#Hnotin & Hsh & Hrs & _ & Hpred) | (% & Hsh & Hrs)]]".
    - (* message is fresh *)
      iDestruct "Hnotin" as %Hnotin.
      wp_pures. rewrite /client_si.
      iDestruct "Hpred" as (sid dres lrq' vo) "(#Hmsg & #Hisreq' & Hcons & Hpost)".
      wp_apply wp_unSOME; [done |].
      iDestruct "Hmsg" as %Hmsg. iDestruct "Hcons" as %Hcons.
      iIntros "_"; wp_pures.
      wp_apply (s_deser_spec resp_serialization); first done.
      iIntros "_"; simpl.
      wp_pures.
      wp_load. wp_pure _. case_bool_decide as Heqn.
      + (* message passes the dynamic check *)
        wp_pures. wp_load.
        wp_store. wp_pures.
        iApply "Hcont".
        iSplitL "Hown Hseq HR Hsh Hrs".
        * (* show we can restore the lock invariant *)
          rewrite /lock_inv.
          iExists (n + 1)%nat, M, ({[m]} ∪ R), S.
          iFrame. iFrame "#".
          assert (((Z.of_nat n) + 1)%Z = Z.of_nat (n + 1)) as -> by lia.
          iFrame.
          rewrite big_opS_union; last by set_solver.
          iSplitL ""; [by iPureIntro |].
          iSplitL "".
          ** rewrite big_opS_singleton.
             iExists sid, dres.
             rewrite <- Heqn.
             eauto with lia.
          ** iApply big_sepS_mono; last by eauto.
             iIntros (x Hinr Ha).
             destruct Ha as (sid' & dres' & Hser & Hlt).
             eauto with lia.
        * (* show the postcondition of the right request type holds *)
          iExists dres, vo.
          assert (sid = n) as ->; first by apply (inj Z.of_nat).
          (* reason using the resource algebra *)
          iAssert (⌜lrq = lrq'⌝%I) as "->".
          { iApply is_req_agree; iFrame "#". }
          destruct dres; simpl; inversion Hcons; subst;
            [by eauto with iFrame| |by eauto with iFrame].
          iDestruct "Hpost" as "[#Hvvo #Hreadp]". iDestruct "Hvvo" as %Hvvo.
          assert (v = vo) as ->; first by injection Hvvo.
          iFrame "#"; eauto.
      + (* message doesn't pass the dynamic check *)
        destruct (decide (sid < n)) as [Hlt | Hgt].
        ** (* response id < seq id *)
           wp_pure _.
           iApply ("IH" with "Hseq Hown Hsh Hrs [HR] Hcont").
           rewrite big_opS_union; last by set_solver.
           iSplitL ""; last by iFrame.
           iApply big_opS_singleton; eauto.
        ** (* response id > seq id *)
           (* in this case we want to derive a contradiction with the fact that
              every element in the authoritative map has key < n *)
          iDestruct (is_req_auth_disagree with "Hown Hisreq'") as %Hsid.
          exfalso; eapply Hdom; last done; lia.
    - (* message is not fresh *)
      (* conclude from the lock invariant that the message's seq id must be
         < than the current seq id, and then proceed by Lob induction *)
      wp_pures.
      iDestruct (big_sepS_elem_of _ _ m with "HR") as (sid dres) "[% %]";
        first done.
      wp_apply wp_unSOME; [done |].
      iIntros "_"; wp_pures.
      wp_apply (s_deser_spec resp_serialization); first done.
      iIntros "_"; simpl.
      wp_pures.
      wp_load.
      wp_pures.
      rewrite bool_decide_eq_false_2; last lia.
      wp_pure _.
      iApply ("IH" with "Hseq Hown Hsh Hrs HR Hcont").
  Qed.

  Theorem session_exec_spec
          (drq : des_req)
          (s : lhst) (h : gmem)
          (γ γ_lock: gname) (sh : socket_handle)
          (seq_id : loc) (lock req_body : val)
          (db_addr : socket_address) (db_id : rep_id)
          {Hser : ∀ (sid : Z), Serializable req_serialization (#sid, req_body)}:
    des_req_to_val drq = req_body →
    let PQ :=
        match drq with
        | DInit => (True, fun u => init_post db_id)
        | DRead k => (⌜k ∈ DB_keys⌝ ∗ Seen db_id s ∗ OwnMemSnapshot k h,
                     fun res => ∃ vo, ⌜res = (des_resp_to_val (RRead vo))⌝ ∗
                        read_post db_id k s h vo)
        | DWrite k v =>
          (⌜k ∈ DB_keys⌝ ∗ Seen db_id s ∗ OwnMemSnapshot k h
            ∗ ⌜DB_Serializable v⌝, fun u => write_post db_id k v s h)
        end%I
    in
    {{{ client_addr ⤇ client_si γ
        ∗ db_addr ⤇ (db_si db_id)
        ∗ is_lock SM_N ip γ_lock lock (lock_inv seq_id γ sh)
        ∗ PQ.1 }}}

      session_exec #(LitSocket sh) #seq_id lock #db_addr req_body @[ip]

      {{{ v, RET v; PQ.2 v}}}.
  Proof.
    (* The start of the proof is shared by the three cases *)
    iIntros (Hraw PQ).
    iIntros (Φ) "(#Hcsi & #Hssi & #Hlock & HP) Hcont".
    rewrite /session_exec; wp_pures.
    wp_apply (acquire_spec SM_N with "Hlock").
    iIntros (w) "(-> & Hlocked & Hlock_inv)"; wp_pures.
    iDestruct "Hlock_inv" as
        (n M R S) "(Hseqid & Hauth & #Hnotin & Hsh & Hrs & Hrinv)".
    iDestruct "Hnotin" as %Hnotin.
    wp_bind (! _)%E; wp_load; rewrite -/ip_of_address; simpl; wp_pures.
    set socket := mk_socket client_addr.
    wp_apply (s_ser_spec req_serialization); first by iPureIntro; apply Hser.
    iIntros (serm) "#Hisser"; iDestruct "Hisser" as %Hisser; wp_pures.
    destruct drq.
    (* Init request *)
    - iDestruct (is_req_alloc γ M n with "Hauth") as "> [Hauth #Hisreq]";
      first by apply Hnotin; auto.
      rewrite ip_eq.
      wp_apply (aneris_wp_send with "[$Hsh $Hrs]"); auto.
      (* Show that the request satisfies the db's si *)
      { iFrame; iFrame "#".
        iExists (client_si γ), n, DInit, γ, (LInit _); simpl.
        iFrame "#".
        rewrite <- Hraw in *.
        repeat (iSplit; first by eauto).
        do 2 iModIntro.
        iIntros (res) "Hpost".
        iDestruct "Hpost" as (dres) "(#Hresp & #Hisreq' & #Hcons & #Hinit)".
        iExists n, dres, (LInit _); by iFrame "#". }
      rewrite -ip_eq.
      simpl. iIntros "[Hsh Hrs]".
      wp_pures.
      wp_apply (listen_wait_for_seqid_spec
                  with "[$Hseqid $Hauth $Hcsi $Hsh $Hrs $Hrinv $Hisreq]").
      { iIntros (? ?); iPureIntro.
        rewrite dom_insert.
        intros [->%elem_of_singleton|]%elem_of_union; first lia.
        eapply Hnotin; last done; lia. }
      iIntros (v) "[Hlockinv Hpost]".
      iDestruct "Hpost" as (dres vo) "[#Hdes [#Hcons Hpost]]".
      wp_pures.
      wp_apply (release_spec with "[$Hlock $Hlocked $Hlockinv]").
      iIntros (vres) "#Heqres".
      wp_pures.
      iApply "Hcont"; done.
    - (* Read request *)
      iDestruct "HP" as "[#Hseen #Hmemsnap]".
      iDestruct (is_req_alloc γ M n with "Hauth") as "> [Hauth #Hisreq]";
      first by apply Hnotin; auto.
      rewrite ip_eq.
      wp_apply (aneris_wp_send with "[$Hsh $Hrs]"); auto.
      (* Show that the request satisfies the db's si *)
      { iFrame; iFrame "#".
        iExists (client_si γ), n, (DRead k), γ, (LRead _ _ _ _); simpl.
        iFrame "#".
        simpl in Hraw. rewrite <- Hraw in *.
        repeat (iSplit; first by eauto).
        do 2 iModIntro.
        iIntros (res) "Hpost".
        iDestruct "Hpost" as (dres) "(#Hresp & #Hisreq' & #Hcons & #Hread)".
        iDestruct "Hread" as (vo) "[Hreseq Hreadpost]".
        rewrite /client_si. iExists n, dres, (LRead _ _ _ _), vo.
        iDestruct "Hresp" as %Hresp.
        iFrame "#"; done. }
      iIntros "[Hsh Hrs]". wp_pures.
      rewrite -ip_eq.
      wp_apply (listen_wait_for_seqid_spec
                  with "[$Hseqid $Hauth $Hcsi $Hsh $Hrs $Hrinv $Hisreq]").
      { iIntros (? ?). iPureIntro.
        rewrite dom_insert.
        intros [?%elem_of_singleton_1|]%elem_of_union; first by lia.
        eapply Hnotin; last done. lia. }
      iIntros (v) "[Hlockinv Hpost]".
      iDestruct "Hpost" as (dres vo) "[#Hdes [#Hcons Hpost]]".
      wp_pures.
      wp_apply (release_spec with "[$Hlock $Hlocked $Hlockinv]").
      iIntros (vres) "#Heqres".
      wp_pures.
      iApply "Hcont".
      iDestruct "Hpost" as "[% #Hpost]".
      iExists vo. iFrame "#". iDestruct "Hdes" as %Hdes.
      subst; done.
    - (* Write request *)
      iDestruct "HP" as "(#Hkin & #Hseen & #Hmemsnap & #Hserval)".
      iDestruct "Hkin" as %Hkin.
      iDestruct "Hserval" as %Hserval.
      iDestruct (is_req_alloc γ M n with "Hauth") as "> [Hauth #Hisreq]";
      first by apply Hnotin; auto.
      rewrite ip_eq.
      wp_apply (aneris_wp_send with "[$Hsh $Hrs]"); auto.
      (* Show that the request satisfies the db's si *)
      { iFrame; iFrame "#".
        iExists (client_si γ), n, (DWrite k (SerVal v)), γ,
        (LWrite db_id k (SerVal v) s h).
        iFrame "#".
        simpl in Hraw. rewrite <- Hraw in *.
        repeat (iSplit; first by eauto).
        do 2 iModIntro.
        iIntros (res) "Hpost".
        iDestruct "Hpost" as (dres) "(#Hresp & #Hisreq' & #Hcons & #Hwrite)".
        iExists n, dres, (LWrite db_id k (SerVal v) s h).
        iDestruct "Hresp" as %Hresp.
        iFrame "#"; eauto. }
      iIntros "[Hsh Hrs]". wp_pures. simpl.
      rewrite -ip_eq.
      wp_apply (listen_wait_for_seqid_spec
                  with "[$Hseqid $Hauth $Hcsi $Hsh $Hrs $Hrinv $Hisreq]").
      { iIntros (? ?). iPureIntro.
        rewrite dom_insert.
        intros [?%elem_of_singleton_1|]%elem_of_union; first by lia.
        eapply Hnotin; last done. lia. }
      iIntros (v') "[Hlockinv Hpost]".
      iDestruct "Hpost" as (dres vo) "[#Hdes [#Hcons Hpost]]".
      wp_pures.
      wp_apply (release_spec with "[$Hlock $Hlocked $Hlockinv]").
      iIntros (vres) "#Heqres".
      wp_pures.
      by iApply "Hcont".
  Qed.

  Definition init_spec ip (init_fn : val) : iProp Σ :=
    ∀ (db_addr : socket_address) (db_id : rep_id),
      {{{ db_addr ⤇ (db_si db_id) }}}
        init_fn #db_addr @[ip]
      {{{ RET #(); init_post db_id }}}.

  Definition read_spec ip (read_fn : val) : iProp Σ :=
    ∀ (db_addr : socket_address) (db_id : rep_id) (k : Key)
      (s : lhst) (h : gmem),
      {{{ db_addr ⤇ (db_si db_id) ∗ ⌜k ∈ DB_keys⌝
          ∗ Seen db_id s ∗ OwnMemSnapshot k h }}}
        read_fn #db_addr #k @[ip]
      {{{ vo, RET vo; read_post db_id k s h vo }}}.

  Definition write_spec ip (write_fn : val) : iProp Σ :=
    ∀ (db_addr : socket_address) (db_id : rep_id) (k : Key)
      (v : SerializableVal) (s : lhst) (h : gmem),
      {{{ db_addr ⤇ (db_si db_id) ∗ ⌜k ∈ DB_keys⌝
          ∗ Seen db_id s ∗ OwnMemSnapshot k h }}}
        write_fn #db_addr #k v @[ip]
      {{{ RET #(); write_post db_id k v s h }}}.

  Theorem sm_setup_spec :
    {{{ free_ports ip {[ port_of_address client_addr ]} ∗
        unfixed {[client_addr]} ∗
        client_addr ⤳ (∅, ∅) }}}
      sm_setup #client_addr @[ip]
    {{{ fns, RET fns;
        ∃ init_fn read_fn write_fn, ⌜fns = (init_fn, read_fn, write_fn)%V⌝
          ∗ (init_spec ip init_fn)
          ∗ (read_spec ip read_fn)
          ∗ (write_spec ip write_fn) }}}.
  Proof.
    iIntros (ϕ) "(Hfree & Hunfixed & Hrs) Hcont".
    wp_lam.
    iDestruct (request_init $! I) as "> Hown".
    iDestruct "Hown" as (γ) "Hown".
    wp_socket sh as "Hsh /=". wp_pures.
    rewrite ip_eq.
    set socket := {| sfamily := PF_INET; stype := SOCK_DGRAM;
                     sprotocol := IPPROTO_UDP; saddress := None |}.
    iApply (aneris_wp_socket_interp_alloc_singleton (client_si γ) with "Hunfixed").
    iIntros "#Hclient".
    wp_socketbind.
    wp_alloc l as "Hl". wp_pures.
    wp_apply (newlock_spec SM_N _ (lock_inv l γ sh) with "[Hown Hl Hsh Hrs]").
    { rewrite -/ip_of_address. iFrame "#".
      rewrite /lock_inv. iExists 0, ∅, ∅, ∅.
      iFrame. rewrite -ip_eq. iFrame "#".
      assert (Z.of_nat 0 = 0%Z) as -> by lia.
      iFrame.
      iSplit; first (iIntros (m ? Hm); rewrite dom_empty_L in Hm; set_solver).
      by rewrite big_opS_empty. }
    rewrite -/ip_of_address.
    iIntros (lock γ_lock) "#Hislock". simpl.
    wp_pures.
    rewrite -ip_eq.
    iApply "Hcont".
    iExists _, _, _; repeat iSplit; first by iPureIntro.
    - (* init *)
      iIntros (db_addr db_id). iModIntro. iIntros (Cont) "Hdb_si Hcont".
      wp_pures.
      wp_apply (session_exec_spec DInit ∅ ∅ γ γ_lock
                  with "[Hdb_si] [Hcont]"); [done|by eauto|].
      iNext.
      iIntros (v) "Hinitpost".
      wp_pures. by iApply "Hcont".
    - (* read *)
      iIntros (db_addr db_id k s h).
      iModIntro. iIntros (Cont) "(Hdb_si & #Hkin & #Hseen & #Hmemsnap) Hcont".
      wp_pures.
      wp_apply (session_exec_spec (DRead k) _ _ γ γ_lock
                  with "[Hdb_si]"); [done|by iFrame "#"|].
      iIntros (v) "Hreadpost"; simpl.
      iDestruct "Hreadpost" as (vo) "[-> #Hreadpost]".
      wp_pures.
      iPoseProof "Hreadpost" as (s' h')
        "(#Hss' & #Hhh' & #Hseen_res & #Hsnap_res & [[-> #Hrestr] | Hsome])".
      + wp_pures.
        iApply "Hcont".
        rewrite /read_post; eauto 10.
      + iDestruct "Hsome" as (e v) "(-> & #H)".
        wp_pures.
        iApply "Hcont".
        rewrite /read_post; eauto 20.
    - (* write *)
      iIntros (db_addr db_id k v s h).
      iModIntro. iIntros (Cont) "(Hdb_si & #Hin & #Hseen & #Hmemsnap) Hcont".
      wp_pures.
      wp_apply (session_exec_spec (DWrite k v) _ _ γ γ_lock
                    with "[Hdb_si]"); first done.
      { iFrame; iFrame "#". iPureIntro; apply _. }
      iIntros (res) "Hwritepost".
      wp_pures. by iApply "Hcont".
  Qed.
End spec.
