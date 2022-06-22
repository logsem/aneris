From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras
     resources_def
     resources_global_inv
     resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import
     repdb_serialization.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import
     clients_mt_user_params.

Section Client_Proxy_Proof.
  Context `{!anerisG Mdl Σ, dbparams : !DB_params, !IDBG Σ}.
  Context (γL γM : gname) (N : gmap socket_address gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_at_leader_user_params γL γM N).

  Definition write_spec_internal
      (wr : val) (sa : socket_address) : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key) (v : SerializableVal)
         (P : iProp Σ) (Q : write_event → wrlog → wrlog → iProp Σ),
        ⌜↑DB_InvName ⊆ E⌝ -∗
        ⌜k ∈ DB_keys⌝ -∗
        □ (P
            ={⊤, E}=∗
              ∃ (h : wrlog) (a_old: option write_event),
                ⌜at_key k h = a_old⌝ ∗
                own_mem_user γM k 1 a_old ∗
                own_obs γL DB_addr h ∗
                  ▷ (∀ (hf : ghst) (a_new : we),
                  ⌜at_key k hf = None⌝ -∗
                  ⌜we_key a_new = k⌝ -∗
                  ⌜we_val a_new = v⌝ -∗
                  ⌜∀ e, e ∈ h → e <ₜ a_new⌝ -∗
                  own_mem_user γM k 1 (Some a_new) -∗
                  own_obs γL DB_addr (h ++ hf ++ [a_new]) ={E,⊤}=∗ Q a_new h hf)) -∗
        {{{ P }}}
          wr #k v @[ip_of_address sa]
        {{{ RET #();
           ∃ (h hf : wrlog) (a: write_event), Q a h hf }}})%I.

 Lemma write_spec_internal_holds A sa (reqh : val) :
    Global_Inv γL γM N -∗
    fixed A -∗
    DB_addr ⤇ srv_si -∗
    @make_request_spec _ _ _ _ MTC reqh sa -∗
    write_spec_internal
      (λ: "k" "v",
         match: reqh (InjL ("k", "v")) with
           InjL "_u" => #()
         | InjR "_abs" => assert: #false
         end)
      sa.
  Proof.
    iIntros "#Hinv #HA #Hsi #Hspec".
    rewrite /write_spec_internal.
    iIntros (E k v P Q HE Hkeys) "!# #Hviewshift".
    iIntros (Φ) "!#".
    iIntros "HP HΦ".
    wp_pures.
    wp_apply ("Hspec" with "[HP]").
    Unshelve.
    3:{ simplify_eq /=. left. exact (E, (k, v.(SV_val)), (P, Q)). }
    iSplit.
    - iPureIntro.
      simplify_eq /=.
      assert (s_valid_val DB_serialization v) as Hs by (apply v.(SV_ser)).
      eexists _. left. split; first done.
      exists #k, v . split; first done. split; last done.
      simplify_eq /=. by eexists _.
    - simplify_eq /=.
      rewrite /ReqPre. iFrame "#". iLeft.
      iExists E, k, v, P, Q.
      do 4 (iSplit; first done).
      iFrame "#∗".
    - iIntros (repd repv) "Hpost".
      simplify_eq /=.
      rewrite /ReqPost.
      iDestruct "Hpost" as "[Hpost|Habs]".
      -- iDestruct "Hpost" as (E0 k0 v0 P0 Q0 Hinl) "Hpost".
         iDestruct "Hpost" as (a_new h hf Hrepd ->) "Hpost".
         wp_pures.
         iApply "HΦ".
         inversion Hinl.
         eauto with iFrame.
      -- by iDestruct "Habs" as (k0 w0 q0 Hinr) "_".
  Qed.

  Definition read_spec_internal
    (rd : val) (sa : socket_address) (k : Key) (q : Qp)
    (wo : option write_event) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ own_mem_user γM k q wo }}}
      rd #k @[ip_of_address sa]
    {{{vo, RET vo;
         own_mem_user γM k q wo ∗
         ((⌜vo = NONEV⌝ ∗ ⌜wo = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (we_val a)⌝ ∗ ⌜wo = Some a⌝))
    }}}%I.

  Lemma read_spec_internal_holds A sa (reqh : val) :
    Global_Inv γL γM N -∗
    fixed A -∗
    DB_addr ⤇ srv_si -∗
    @make_request_spec _ _ _ _ MTC reqh sa -∗
    ∀ (k : Key) (q : Qp) (h : option write_event),
    read_spec_internal
      (λ: "k",
         match: reqh (InjR "k") with InjL "_abs" => assert: #false | InjR "r" => "r" end)
           sa k q h.
  Proof.
    iIntros "#Hinv #HA #Hsi #Hspec".
    iIntros (k q h).
    rewrite /read_spec_internal.
    iIntros (Hkeys Φ) "!#".
    iIntros "Hk HΦ".
    wp_pures.
    wp_apply ("Hspec" with "[Hk]").
    Unshelve. 3:{ simplify_eq /=. right. done. }
    iSplit.
    - iPureIntro.
      simplify_eq /=.
      eapply sum_is_ser_valid.
      simplify_eq /=. simpl.
      rewrite /sum_is_ser.
      eexists _, _. by right.
    - simplify_eq /=.
      rewrite /ReqPre. iFrame "#". iRight.
      iExists _, _, _. by iFrame.
    - iIntros (repd repv) "Hpost".
      simplify_eq /=.
      rewrite /ReqPost.
      iDestruct "Hpost" as "[Habs|Hpost]".
      -- by iDestruct "Habs" as (E k0 v0 P0 Q0 Habs) "d".
      -- iDestruct "Hpost" as (k0 w0 q0 Hinr) "Hpost".
         iDestruct "Hpost" as (vo Hrepd ->) "(Hmem & Hpost)".
         wp_pures.
         iApply "HΦ".
         inversion Hinr.
         iFrame.
  Qed.

  Definition init_client_leader_proxy_internal
    (A : gset socket_address) (sa : socket_address) : iProp Σ :=
    ⌜DB_addr ∈ A⌝ →
    ⌜sa ∉ A⌝ →
    {{{ fixed A ∗
        DB_addr ⤇ srv_si ∗
        sa ⤳ (∅, ∅) ∗
        (∀ A sa, @init_client_proxy_spec _ _ _ _ MTC srv_si A sa) ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      init_client_leader_proxy (s_serializer DB_serialization)
                               #sa #DB_addr @[ip_of_address sa]
    {{{ wr rd, RET (wr, rd);
        (∀ k q h, read_spec_internal rd sa k q h) ∗
          write_spec_internal wr sa }}}.

  Lemma init_client_leader_proxy_internal_holds A sa :
    Global_Inv γL γM N ⊢ init_client_leader_proxy_internal A sa.
  Proof.
    iIntros "#Hinv".
    iIntros (HA HnA).
    iIntros (Φ) "!#".
    iIntros "(#Hf & #Hsi & Hmh & #HClient_proxySpec & Hfp) HΦ".
    rewrite /init_client_leader_proxy.
    wp_pures.
    wp_apply ("HClient_proxySpec" with "[$Hf $Hfp $Hmh $Hsi][HΦ]"); first done.
    iNext.
    iIntros (reqh) "#Hspec".
    wp_pures.
    iApply "HΦ".
    iSplit.
    - by iApply read_spec_internal_holds.
    - by iApply write_spec_internal_holds.
  Qed.

End Client_Proxy_Proof.
