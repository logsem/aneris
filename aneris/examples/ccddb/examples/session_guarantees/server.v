From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import agree gmap auth.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     network tactics proofmode lifting lang.
From aneris.aneris_lang.lib Require Import lock_proof network_util_proof list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec resources.
From aneris.examples.ccddb Require Import spec_util.
From aneris.examples.ccddb.examples.session_guarantees
     Require Import res sm_code.
From aneris.examples.ccddb.examples.session_guarantees Require Import res.

Context `{!anerisG Mdl Σ, !lockG Σ}.
Context `{!DB_params}.
Context `{!DB_time, !DB_events}.
Context `{!DB_resources Mdl Σ}.
Context `{!Maximals_Computing}.
Context `{!inG Σ (authUR req_map)}.
Context `{!DB_init_function}.

Section code.

  (* Request handler that loops while replying to client requests.
   * Requests are answererd by proxying them to the corresponding
   * db function: e.g. read requests are answered via db reads.
   *)
  Definition request_handler : val :=
    rec: "req_handler" "sh" "rd_fn" "wr_fn" :=
      let: "req_raw" := unSOME (ReceiveFrom "sh") in
      let: "sender" := Snd "req_raw" in
      let: "req" := s_deser (s_serializer req_serialization) (Fst "req_raw") in
      let: "seq_id" := Fst "req" in
      let: "req_body" := Snd "req" in
      let: "res" :=
         match: "req_body" with
           InjL "init_body" => InjLV #"Ok"
         | InjR "r" =>
           match: "r" with
             InjL "k" =>
             InjR (InjL ("rd_fn" "k"))
           | InjR "write_body" =>
             let: "k" := Fst "write_body" in
             let: "v" := Snd "write_body" in
             "wr_fn" "k" "v";;
             InjRV (InjRV #"Ok")
           end
         end
      in
      SendTo "sh" (s_ser (s_serializer resp_serialization) ("seq_id", "res")) "sender";;
      "req_handler" "sh" "rd_fn" "wr_fn".

  (* Main server entry point.
   * Performs two main functions:
   * - runs a local replica of the causally-consistent db
   * - runs an request handler that answers read and write requests from clients
   *   by querying the db
   *
   * Params:
   * - dbs: a list of all socket addresses serving as db replicas
   * - db_id: the id of the replica that will be run on this node
   * - req_addr: the socket address at which to run the request handler to
   *   answer queries from clients
   *)
  Definition server : expr :=
    λ: "dbs" "db_id" "req_addr",
    (* Initialize the local db replica *)
    let: "fns" := init "dbs" "db_id" in
    let: "rd_fn" := Fst "fns" in
    let: "wr_fn" := Snd "fns" in
    (* Set up and launch request handler *)
    let: "sh" := NewSocket in
    SocketBind "sh" "req_addr";;
               request_handler "sh" "rd_fn" "wr_fn".

End code.

Section spec.

  Definition ip sh := ip_of_address sh.

  (* A version of read_post where we're guaranteed to read something *)
  Definition read_some_post (db : rep_id) (k : Key) (s : lhst) (h : gmem)
             (vo : val) e v : iProp Σ :=
    ∃ s' h',
      ⌜s ⊆ s'⌝
      ∗ ⌜h ⊆ h'⌝
      ∗ Seen db s'
      ∗ OwnMemSnapshot k h'
      ∗ (⌜vo = InjRV v⌝)
      ∗ (⌜AE_val e = v⌝)
      ∗ (⌜AE_key e = k⌝)
      ∗ ⌜e ∈ Maximals (restrict_key k s')⌝
      ∗ ⌜(erasure e) ∈ h'⌝
      ∗ ⌜s_valid_val DB_serialization v⌝.

  (* A version of write_post that's compatible with the view shift in the DB's write
     function.*)
  Definition write_post_precise (db : rep_id) (k : Key) (v : val) (s : lhst)
             (h : gmem) e s_new h_new : iProp Σ :=
    let s' := s_new ∪ {[ e ]} in
    let h' := h_new ∪ {[ erasure e ]} in
      ⌜AE_key e = k⌝
      ∗ ⌜AE_val e = v⌝
      ∗ ⌜s ⊆ s'⌝
      ∗ ⌜h ⊆ h'⌝
      ∗ Seen db s'
      ∗ OwnMemSnapshot k h'
      ∗ ⌜e ∉ s⌝
      ∗ ⌜e ∈ s'⌝
      ∗ ⌜(erasure e) ∉ h⌝
      ∗ ⌜(erasure e) ∈ h' ⌝
      ∗ ⌜(erasure e) ∈ Maximals h'⌝
      ∗ ⌜Maximum s' = Some e⌝.

  Definition mem_inv : iProp Σ :=
    ([∗ set] k ∈ DB_keys,
     (∃ h : gmem, OwnMemUser k h ∗
        ∀ we, ⌜we ∈ h⌝ → ⌜s_valid_val DB_serialization (WE_val we)⌝)%I).
  Definition SERVER_NM : namespace := nroot.@"SERVER".
  Hypothesis inv_ne : nclose SERVER_NM ## nclose DB_InvName.

  Lemma mem_inv_alloc E :
    ([∗ set] k ∈ DB_keys, OwnMemUser k ∅) ⊢ |={E}=> inv SERVER_NM mem_inv.
  Proof.
    rewrite /mem_inv.
    iIntros "Hks".
    iApply inv_alloc.
    iNext.
    iApply big_sepS_mono; last done.
    iIntros (x Hx) "Hx"; eauto.
  Qed.

  Theorem server_spec (db_id : rep_id)
          (dbs : val) (db_addr req_addr : socket_address) :
    DB_addresses !! db_id = Some db_addr ->
    is_list DB_addresses dbs ->
    (ip db_addr) = (ip req_addr) ->
    (port_of_address db_addr) ≠ (port_of_address req_addr) ->
    {{{ req_addr ⤇ db_si db_id
        ∗ req_addr ⤳ (∅, ∅)
        ∗ free_ports (ip req_addr) {[port_of_address req_addr]}
        ∗ GlobalInv
        ∗ init_spec init
        ∗ init_resources db_addr db_id
        ∗ ([∗ set] k ∈ DB_keys, OwnMemSnapshot k ∅)
        ∗ inv SERVER_NM mem_inv
    }}}
      server dbs #db_id #req_addr @[ip req_addr]
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Hith_addr Hcoh Hips_eq Hports_ne ϕ)
            "(#Hreq_si & Hrs & Hreq_free & #Hinv & #Hinit_spec & Hinit_res
               & #Hsnap0 & #Hmem_inv) Hcont".
    iDestruct "Hinit_res" as "(#Hproto & Hdb_free & Htoken)".
    wp_pures.
    wp_bind (init _ _)%E. rewrite -/ip_of_address.
    rewrite -Hips_eq.
    wp_apply ("Hinit_spec" $! db_id db_addr
                with "[] [] [$Htoken $Hdb_free] [Hreq_free Hrs]"); auto.
    iNext.
    iIntros (rd wr) "(#Hseen & #Hread_spec & #Hwrite_spec)".
    wp_pures.
    rewrite Hips_eq.
    wp_socket h as "Hsh /=".
    wp_pures.
    set socket := {| saddress := None |}.
    wp_socketbind.
    set socket' :=
      RecordSet.set saddress (λ _ : option socket_address, Some req_addr) socket.
    (* Establish the loop invariant *)
    iAssert (∃ R S,
                (h ↪[ip_of_address req_addr] socket')
                  ∗ req_addr ⤳ (R, S)
                  ∗ ([∗ set] m ∈ R, (db_si db_id) m)
            )%I with "[Hsh Hrs]" as "Hrecvd".
    { by (iExists ∅, ∅); iFrame. }
    iLöb as "IH".
    wp_lam. wp_pures.
    iDestruct "Hrecvd" as (R S) "(Hsh & Hrs & #Hrecvd)".
    wp_pures.
    wp_bind (ReceiveFrom _).
    (* Receive the request *)
    wp_apply (aneris_wp_receivefrom _ _ _ _ socket' with "[$Hsh $Hrs]"); auto.
    iIntros (m) "Hm".
    iAssert (▷ ∃ R' S' : message_soup,
               db_si db_id m ∗
                     h ↪[ip_of_address req_addr] socket' 
                     ∗ req_addr ⤳ (R', S')
                     ∗ ([∗ set] m ∈ R', db_si db_id m))%I with "[Hm]"
      as (R' S') "(Hm & Hsh & Hrs & HR')".
    { iDestruct "Hm" as "[Heq [(%Hnotin & Hsh & Hrs & #Hsi & #?) | (%Hin & Hsh & Hrs)]]".
      - iNext.
        iExists _, _. iFrame.
        rewrite big_sepS_union; last set_solver.
        rewrite big_sepS_singleton. iFrame "#".
      - iNext.
        iExists _, _; iFrame; iFrame "#".
        iApply big_sepS_elem_of; done. }
    wp_apply wp_unSOME; [done | iIntros "_"].
    wp_pures.
    iDestruct "Hm" as (Ψ sid drq γ lrq)
      "(#Hsender & %Hiser & #Hisreq & %Hreq_db & %Hcons & Hpre_post)".
    wp_bind (prod_deser _ _ _). rewrite -/ip_of_address.
    wp_apply (s_deser_spec req_serialization); [done |].
    iIntros (?). wp_pures.
    destruct drq; inversion Hcons; subst.
    - (* Init *)
      wp_pures.
      iDestruct "Hpre_post" as "(_ & #Hpost)".
      wp_apply (s_ser_spec resp_serialization).
      { iPureIntro. apply serializable. }
      iIntros (s) "%His_ser". rewrite -/ip_of_address /=.
      wp_apply (aneris_wp_send _ _ _ _ _ _ _ _ socket' with "[$Hsh $Hrs]"); auto.
      + iFrame; iFrame "#".
        iApply "Hpost".
        iDestruct (big_sepS_mono
                      (λ k, OwnMemSnapshot k ∅)%I
                      (λ k, ∃ h, OwnMemSnapshot k h)%I with "Hsnap0")
           as "Hsnap0'"; first by eauto.
        iExists RInit; rewrite /init_post; by eauto 10.
      + (* Apply IH *)
        iIntros "[Hsh Hrs]".
        wp_pures.
        wp_apply "IH"; eauto with iFrame.
    - (* Read *)
      wp_pures.
      iDestruct "Hpre_post" as "((%Hkin & #Hseen_req & #Hsnap_req) & #Hpost)".
      (* Run the read against the DB *)
      wp_bind (rd _).
      rewrite -Hips_eq.
      wp_apply ("Hread_spec" with "[//] Hseen_req").
      iIntros (vo) "H".
      iApply fupd_aneris_wp.
      iInv "Hmem_inv" as "> Hmi" "Hclose".
      rewrite /mem_inv.
      (* extract resource for k, use agreement, update,
         and then close the invariant *)
      iDestruct (big_sepS_elem_of_acc _ _ _ Hkin with "Hmi") as "(Hk & Hrest)".
      iDestruct "Hk" as (h1) "[Hk %Hser]".
      iAssert
        (∃ s', ⌜s ⊆ s'⌝ ∗ Seen db s' ∗
         |={⊤ ∖ ↑SERVER_NM}=>
         k ↦ᵤ h1 ∗
         (⌜vo = NONEV⌝ ∗ ⌜restrict_key k s' = ∅⌝ ∗
           read_post db k s h0 (InjLV #()) ∨
          (∃ v e, ⌜vo = SOMEV v⌝ ∗ ⌜AE_val e = v⌝ ∗
                  ⌜e = Observe (restrict_key k s')⌝ ∗
                  read_some_post db k s h0 (InjRV (AE_val e)) e (AE_val e))))%I
        with "[H Hk]" as (s') "(%Hss' & #Hseen' & >[Hk Hrdres])".
      { iDestruct "H" as (s' Hss') "[#Hseen' H]".
        iExists s'; iSplit; first done.
        iSplit; first done.
        iDestruct "H" as "[(% & %)|H]".
        { rewrite /read_post; eauto 20. }
        iDestruct "H" as (v e) "(% & % & % & #Hsnap' & %)".
        iMod (OwnMemSnapshot_included with "Hinv Hk Hsnap'") as "[Hk %Hincl]";
          first solve_ndisj.
        assert (AE_key e = k ∧ e ∈ s') as [? ?].
        { by eapply elem_of_Maximals_restrict_key. }
        iDestruct (OwnMemSnapshot_union with "Hsnap_req Hsnap'")
          as "Hsnap''".
        iModIntro.
        iFrame; iRight.
        iExists v, e.
        repeat (iSplit; first done).
        iExists s', (h0 ∪ {[erasure e]}).
        repeat (iSplit; first by eauto with set_solver).
        iPureIntro; rewrite -erasure_val; apply Hser; set_solver.
      }
      iDestruct ("Hrest" with "[Hk]") as "Hmi"; first by eauto.
      clear Hser.
      iMod ("Hclose" with "[$Hmi]") as "_".
      iModIntro.
      iDestruct "Hrdres" as "[(-> & _ & #Hpost') | Hsome]";
        simpl; wp_pures.
      + (* Returns nothing *)
        (* Show that the response can be serialized *)
        wp_apply (s_ser_spec resp_serialization).
        { iPureIntro. apply serializable. }
        iIntros (str) "%Hisser".
        rewrite Hips_eq.
        wp_apply (aneris_wp_send _ _ _ _ _ _ _ _ socket' with "[$Hsh $Hrs]"); auto.
        { (* Show that the message satisfies the protocol *)
          iFrame "#".
          iApply "Hpost".
          iExists (RRead (InjLV #())); simpl.
          repeat iSplit; [done| iFrame "#" | by iPureIntro; apply ConsResRead |
                          by iExists _; iFrame "#"; done]. }
        iIntros "[Hsh Hrs]". simpl.
        wp_pure _. wp_pure _.
        wp_apply "IH"; eauto with iFrame.
      + (* Returns something *)
        (* Show that the response can be serialized *)
        iDestruct "Hsome" as (v e) "(-> & <- & %Hobs & #Hreadpost)".
        iPoseProof "Hreadpost" as (? ?) "(_&_&_&_&_&_&_&_&_& %Hser)".
        wp_apply (s_ser_spec resp_serialization).
        { iPureIntro.
          assert (DB_Serializable (AE_val e)) by done.
          apply serializable. }
        iIntros (str) "%Hisser".
        rewrite Hips_eq.
        wp_apply (aneris_wp_send _ _ _ _ _ _ _ _ socket' with "[$Hsh $Hrs]"); auto.
        { (* Show that the message satisfies the protocol *)
          iFrame "#".
          iApply "Hpost".
          iExists (RRead (InjRV _)).
          repeat iSplit; [done| done | done |].
          iExists _; iSplit; first done.
          rewrite /read_post.
          iDestruct "Hreadpost" as
              (s'' h'') "(? & ? & ? & ? & ? & ? & ? & ? & ? & ?)"; eauto 20. }
        iIntros "[Hsh Hrs]". simpl.
        wp_pures.
        wp_apply "IH"; eauto with iFrame.
    - (* Write *)
      wp_pures.
      iDestruct "Hpre_post" as "((%Hkin & #Hseen_req & #Hsnap_req) & #Hres)".
      rewrite -Hips_eq. 
      wp_apply
        ("Hwrite_spec"
           $! (⊤ ∖ ↑SERVER_NM) k v0 s True%I
           (λ e h' s', write_post_precise db k v0 s h0 e s' (h0 ∪ h'))%I);
          [iPureIntro; done| iPureIntro; solve_ndisj | | by iFrame "#" |].
      + (* Prove the view shift *)
          iModIntro.
          iIntros (s' e') "%Hss' %Hhh' %Hkey %Hval _".
          iInv "Hmem_inv" as "> Hmi" "Hclose".
          rewrite /mem_inv.
          (* extract resource for k, use agreement, update,
             and then close the invariant *)
          iDestruct (big_sepS_elem_of_acc _ _ _ Hkin with "Hmi")
            as "(Hk & Hrest)".
          iDestruct "Hk" as (h1) "[Hk %Hser]".
          iMod (OwnMemSnapshot_included with "Hinv Hk Hsnap_req") as "[Hk %]";
            first solve_ndisj.
          iModIntro.
          iIntros (h') "%Herase1 %Herase2 %Hmax #Hseen' Hownh".
          iDestruct (User_Sys_agree with "Hk Hownh") as %->.
          iMod (OwnMem_update _ _ (h' ∪ {[erasure e']}) with "Hk Hownh")
            as "[Hk Hownh]"; first set_solver.
          iModIntro.
          iFrame "Hownh".
          iDestruct (User_Snapshot with "Hk") as "[Hk #Hsnap]".
          iDestruct ("Hrest" with "[Hk]") as "Hrest".
          { iExists _.
            iSplitL "Hk"; [iFrame|].
            iPureIntro.
            intros x [Hxin| ->%elem_of_singleton]%elem_of_union; first by auto.
            rewrite erasure_val Hval. apply serializable. }
          iMod ("Hclose" with "[Hrest]") as "_"; [by iNext|].
          iModIntro.
          rewrite /write_post_precise /=.
          iDestruct (OwnMemSnapshot_union with "Hsnap_req Hsnap") as "Hsnap'''".
          rewrite (assoc_L (∪)).
          iFrame "#".
          rewrite (subseteq_union_1_L _ h'); last done.
          iPureIntro.
          repeat split; auto;
            [set_solver | set_solver | set_solver|set_solver].
      + iIntros "H".
        iDestruct "H" as (h1 s1 e) "(%Hss1 & #Hwp)".
        wp_pures.
        wp_apply (s_ser_spec resp_serialization).
        { iPureIntro. apply serializable. }
        iIntros (resp) "%Hisser". rewrite Hips_eq.
        wp_apply (aneris_wp_send _ _ _ _ _ _ _ _ socket' with "[$Hsh $Hrs]"); auto. 
        * iFrame; iFrame "#".
          iApply "Hres".
          rewrite /write_post.
          iExists RWrite; eauto 20.
        * iIntros "[Hsh Hrs] /=".
          wp_pures.
          wp_apply "IH"; eauto with iFrame.
  Qed.

End spec.
