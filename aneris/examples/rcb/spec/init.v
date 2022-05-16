From iris.algebra Require Import auth gmap excl.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import list_proof lock_proof vector_clock_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.rcb.spec Require Import base events resources.


(** Specifications for read and write operations.  *)

Section Specification.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCB_events, !RCB_resources Mdl Σ}.

  Definition deliver_spec
       (deliver : val) (i: nat) (z : socket_address) : iProp Σ :=
         ⌜RCB_addresses !! i = Some z⌝ -∗
         <<< ∀∀ (s : lstate), OwnLocal i s >>>
           deliver #() @[ip_of_address z] ↑RCB_InvName
         <<<▷ ∃∃ s' vo,
                RET vo; OwnLocal i s' ∗
                        ((⌜s' = s⌝ ∗ ⌜vo = NONEV⌝) ∨
                         (∃ a,
                          ⌜s' = s ∪ {[ a ]}⌝ ∗
                          ⌜a ∉ s⌝ ∗
                          ⌜a ∈ compute_maximals LE_vc s'⌝ ∗
                          ⌜(LE_origin a) ≠ i⌝ ∗
                          OwnGlobalSnapshot {[ erasure a ]} ∗
                          ∃ v, ⌜vo = SOMEV v⌝ ∗
                               ⌜is_le v a⌝)) >>>.

  Definition broadcast_spec
      (broadcast : val) (i: nat) (z : socket_address) : iProp Σ :=
    ∀ (v : SerializableVal),
    ⌜RCB_addresses !! i = Some z⌝ -∗
    <<< ∀∀ (h : gstate) (s : lstate), OwnGlobal h ∗ OwnLocal i s >>>
      broadcast v @[ip_of_address z] ↑RCB_InvName
    <<<▷ ∃∃ w (a : le),
            RET w;
               ⌜is_le w a⌝ ∗
               ⌜a ∉ s⌝ ∗
               ⌜erasure a ∉ h⌝ ∗
               ⌜LE_payload a = v⌝ ∗
               ⌜LE_origin a = i⌝ ∗
               let e := erasure a in
               let s' := s ∪ {[ a ]} in
               let h' := h ∪ {[ e ]} in
               ⌜e ∈ compute_maximals GE_vc h'⌝ ∗
               ⌜compute_maximum LE_vc s' = Some a⌝ ∗
               OwnGlobal h' ∗
               OwnLocal i s' >>>.

  Definition init_spec (init : val) : iProp Σ :=
    □ ∀ (A : gset socket_address) (i : nat) (z : socket_address)
        (v : val),
        ⌜is_list RCB_addresses v⌝ →
        ⌜RCB_addresses !! i = Some z⌝ →
        ⌜z ∈ A⌝ →
        {{{ fixed A ∗
             ([∗ list] i ↦ z ∈ RCB_addresses, z ⤇ RCB_socket_proto i) ∗
             z ⤳ (∅, ∅) ∗
             free_ports (ip_of_address z) {[port_of_address z]} ∗
            init_token i}}}
          init v #i @[ip_of_address z]
        {{{ deliver broadcast, RET (deliver, broadcast);
            OwnLocal i ∅ ∗ deliver_spec deliver i z ∗
                     broadcast_spec broadcast i z}}}.

  Definition simplified_deliver_spec
       (deliver : val) (i: nat) (z : socket_address) : iProp Σ :=
    ∀ (s : lstate),
        ⌜RCB_addresses !! i = Some z⌝ -∗
        {{{ OwnLocal i s }}}
          deliver #() @[ip_of_address z]
        {{{ vo, RET vo;
                ((⌜vo = NONEV⌝ ∗ OwnLocal i s)  ∨
                 (∃ (v: val) (e : le),
                     ⌜vo = SOMEV v⌝ ∗ ⌜is_le v e⌝
                      ∗ OwnLocal i (s ∪ {[ e ]})
                      ∗ ⌜e ∉ s⌝
                      ∗ ⌜((LE_origin e) ≠ i)⌝
                      ∗ OwnGlobalSnapshot ({[ erasure e ]})
                      ∗ ⌜e ∈ compute_maximals LE_vc (s ∪ {[ e ]})⌝))
         }}}.

  Lemma deliver_spec_implies_simplified_spec deliver i z :
    deliver_spec deliver i z ⊢ simplified_deliver_spec deliver i z.
  Proof.
    iIntros "#Hdeliver".
    rewrite /simplified_deliver_spec.
    iIntros (s) "%Haddr".
    iIntros (Φ) "!> Hloc HΦ".
    iApply "Hdeliver"; [done |].
    iApply fupd_mask_intro; [set_solver |].
    iIntros "Hcl".
    iExists s; iFrame.
    iIntros "!>" (s' vo) "[Hloc [[-> ->] |Hsome]]";
      iMod "Hcl"; iModIntro; iApply "HΦ".
    - eauto with iFrame.
    - iDestruct "Hsome" as (a) "(-> & ? & ? & ? & ? & Hv)".
      iDestruct "Hv" as (v) "[? ?]".
      eauto with iFrame.
  Qed.

  Definition simplified_broadcast_spec
      (broadcast : val) (i: nat) (z : socket_address)
      (v : SerializableVal) (h : gstate) (s : lstate) : iProp Σ :=
     ⌜RCB_addresses !! i = Some z⌝ -∗
     {{{ OwnGlobal h ∗ OwnLocal i s }}}
       broadcast v @[ip_of_address z]
     {{{ (w : val), RET w;
         ∃ (a : le),
          ⌜LE_payload a = v⌝ ∗
          ⌜LE_origin a = i⌝ ∗
          ⌜is_le w a⌝ ∗
          ⌜compute_maximum LE_vc (s ∪ {[ a ]}) = Some a⌝ ∗
          let e := erasure a in
          ⌜e ∈ compute_maximals GE_vc (h ∪ {[ e ]})⌝ ∗
          OwnLocal i (s ∪ {[ a ]}) ∗
          OwnGlobal (h ∪ {[ e ]}) }}}.

  Lemma broadcast_spec_implies_simplified_spec broadcast i z :
    broadcast_spec broadcast i z ⊢ ∀ v h s, simplified_broadcast_spec broadcast i z v h s.
  Proof.
    iIntros "#Hbr" (v h s).
    rewrite /simplified_broadcast_spec.
    iIntros (Hi Φ) "!>".
    iIntros "[Hglob Hloc] HΦ".
    iApply "Hbr"; [done |].
    iApply fupd_mask_intro; [set_solver |].
    iIntros "Hmask".
    iExists h, s. iFrame.
    iIntros "!>" (w a) "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
    iMod "Hmask". iModIntro.
    iApply "HΦ". eauto with iFrame.
  Qed.

End Specification.

(* An example of using the deliver and broadcast specs through invariants (logical atomicity) *)
Section DeliverBroadcastInvExample.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCB_events, !RCB_resources Mdl Σ}.

  Context (LInv : namespace) (names_disj : LInv ## RCB_InvName).

  (* TODO: here we'd like to take local snapshots, but we can't.
     Implement local snapshots. *)
  Definition deliver_with_inv_example
      (deliver : val) (i: nat) (z : socket_address) : iProp Σ :=
    (⌜RCB_addresses !! i = Some z⌝ -∗
     {{{ inv LInv (∃ s, OwnLocal i s) }}}
       deliver #() @[ip_of_address z]
     {{{ (vo : val), RET vo;
             (⌜vo = NONEV⌝ ∨
              (∃ (s : lstate) (v: val) (e : le),
              ⌜vo = SOMEV v⌝
              ∗ ⌜is_le v e⌝
              ∗ ⌜e ∉ s⌝
              ∗ ⌜(LE_origin e) ≠ i⌝
              ∗ OwnGlobalSnapshot ({[ erasure e ]})
              ∗ ⌜e ∈ compute_maximals LE_vc (s ∪ {[ e ]})⌝))
    }}})%I.

  Lemma deliver_spec_implies_inv_example deliver i z :
    deliver_spec deliver i z ⊢ deliver_with_inv_example deliver i z.
  Proof.
    iIntros "#Hdel".
    rewrite /deliver_with_inv_example.
    iIntros "#Haddr !>" (Φ) "#Hinv HΦ".
    iApply "Hdel"; [done |].
    (* Before we intro the mask as in the sequential case, we have to open
       the local invariant. *)
    iInv LInv as "> Hloc" "Hcl". iDestruct "Hloc" as (s) "Hloc".
    iApply fupd_mask_intro; [set_solver |]. iIntros "Hmask".
    iExists s; iFrame. iIntros "!>" (s' vo) "[Hloc Hopt]".
    iMod "Hmask". iMod ("Hcl" with "[Hloc]") as "_".
    { eauto with iFrame. }
    iModIntro.
    iApply "HΦ". iDestruct "Hopt" as "[[? ?] | Hsome]".
    - eauto with iFrame.
    - iDestruct "Hsome" as (a) "(-> & ? & ? & ? & ? & Hv)".
      iDestruct "Hv" as (v) "[-> ?]".
      eauto 15 with iFrame.
  Qed.

  Definition broadcast_with_inv_example
      (broadcast : val) (i: nat) (z : socket_address)
      (v : SerializableVal) : iProp Σ :=
    (⌜RCB_addresses !! i = Some z⌝ -∗
     {{{ inv LInv (∃ h s, OwnGlobal h ∗ OwnLocal i s) }}}
       broadcast v @[ip_of_address z]
     {{{ (w : val), RET w;
         ∃ (a : le) h s,
          ⌜LE_payload a = v⌝ ∗
          ⌜LE_origin a = i⌝ ∗
          ⌜is_le w a⌝ ∗
          ⌜compute_maximum LE_vc (s ∪ {[ a ]}) = Some a⌝ ∗
          let e := erasure a in
          ⌜e ∈ compute_maximals GE_vc (h ∪ {[ e ]})⌝ }}})%I.

  Lemma broadcast_spec_implies_inv_example broadcast i z :
    broadcast_spec broadcast i z ⊢ ∀ v, broadcast_with_inv_example broadcast i z v.
  Proof.
    iIntros "#Hbr" (v).
    rewrite /broadcast_with_inv_example.
    iIntros (Hi Φ) "!> #HInv HΦ".
    iApply "Hbr"; [done |].
    iInv LInv as "> Hinv" "Hcl".
    iDestruct "Hinv" as (h s) "[Hglob Hloc]".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iExists h, s; iFrame.
    iIntros "!>" (w a) "(? & ? & ? & ? & ? & ? & ? & Hloc & Hglob)".
    iMod "Hmask". iMod ("Hcl" with "[Hloc Hglob]").
    { eauto with iFrame. }
    iModIntro. iApply "HΦ".
    eauto with iFrame.
  Qed.

End DeliverBroadcastInvExample.

(** Modular specification for causal memory
    vector-clock based implementation. *)

Class RCBG `{!RCB_events} Σ := {
  RCBG_global_history_excl :> inG Σ (prodR fracR (agreeR (gsetO ge)));
  RCBG_global_history_pers :> inG Σ (authUR (gsetUR ge));
  RCBG_local_history_excl :> inG Σ (prodR fracR (agreeR (gsetO le)));
  RCBG_lockG :> lockG Σ;
}.

Definition RCBΣ `{!RCB_events} : gFunctors :=
  #[GFunctor (prodR fracR (agreeR (gsetO ge)));
    GFunctor (authUR (gsetUR ge));
    GFunctor (prodR fracR (agreeR (gsetO le)));
    lockΣ].

Instance subG_RCBΣ `{!RCB_events} {Σ} : subG RCBΣ Σ → RCBG Σ.
Proof. econstructor; solve_inG. Qed.

Class RCB_init_function := { init : val }.

Section Init.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCB_events, !RCBG Σ, !RCB_init_function}.

  Class RCB_init := {
    RCB_init_events :> RCB_events;

    RCB_init_setup E :
        True ⊢ |={E}=> ∃ (RCBRS : RCB_resources Mdl Σ),
      GlobalInv ∗
      ([∗ list] i ↦ _ ∈ RCB_addresses, init_token i) ∗
      (OwnGlobal ∅) ∗
      init_spec init;
  }.

End Init.

Section Helpers.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCB_events, !RCB_resources Mdl Σ}.

  (** Definition and specification of a deliver procedure that actively waits until a message is
      delivered. *)
  Definition wait_deliver : val :=
  λ: "deliver",
    rec: "wd" <> :=
      match: "deliver" #() with
        NONE => "wd" #()
      | SOME "m" => "m"
      end.

  Definition wait_deliver_spec
             (wait_deliver : val) (i: nat) (z : socket_address) : iProp Σ :=
    ⌜RCB_addresses !! i = Some z⌝ -∗
    □ (∀ (Φ : val -> iProp Σ),
          □ (|={⊤, ↑RCB_InvName}=>
           ∃ (s : lstate),
             OwnLocal i s ∗
             ((OwnLocal i s ={↑RCB_InvName, ⊤}=∗ emp) ∧
              (∀ (a : le) (v : val),
                  let s' := s ∪ {[ a ]} in
                  ⌜a ∉ s⌝ -∗
                  ⌜a ∈ compute_maximals LE_vc s'⌝ -∗
                  ⌜is_le v a⌝ -∗
                  OwnLocal i s' -∗
                  OwnGlobalSnapshot {[ erasure a ]} ={↑RCB_InvName, ⊤}=∗
                  Φ v))) -∗
          WP wait_deliver #() @[ip_of_address z] {{ Φ }}
      ).

  Lemma deliver_spec_implies_wait_deliver_spec
    (deliver : val) (i : nat) (z : socket_address) :
  {{{ deliver_spec deliver i z }}}
    wait_deliver deliver @[ip_of_address z]
  {{{ wd, RET wd; wait_deliver_spec wd i z }}}. 
  Proof.
    iIntros (Φ) "#Hdeliver HΦ".
    unfold wait_deliver. wp_pures. iApply "HΦ".
    clear Φ.
    iIntros "#Hi !>" (Φ) "#Hvs".
    iLöb as "IH".
    wp_rec.
    wp_apply "Hdeliver"; [done |].
    iMod "Hvs". iModIntro.
    iDestruct "Hvs" as (s) "[Hloc Hvs]".
    iExists s; iFrame. iModIntro.
    iIntros (s' vo) "[Hloc' [[-> ->] | Hsome]]".
    - iMod ("Hvs" with "Hloc'") as "_".
      iModIntro. wp_match.
      iApply "IH".
    - iDestruct "Hsome" as (a) "(-> & #? & #? & #? & #? & Hv)".
      iDestruct "Hv" as (v) "[-> #?]".
      iDestruct "Hvs" as "[_ Hvs]".
      iMod ("Hvs" with "[] [] [] Hloc' []") as "Hvs"; eauto with iFrame.
      iModIntro. wp_pures. iFrame.
  Qed.

  Definition simplified_wait_deliver_spec
       (deliver : val) (i: nat) (z : socket_address) : iProp Σ :=
    Eval simpl in
    ∀ (s : lstate),
        ⌜RCB_addresses !! i = Some z⌝ -∗
        {{{ OwnLocal i s }}}
          deliver #() @[ip_of_address z]
        {{{ e v, RET v; let s' := s ∪ {[ e ]} in
                        ⌜is_le v e⌝
                      ∗ OwnLocal i s'
                      ∗ ⌜e ∉ s⌝
                      ∗ ⌜(LE_origin e) ≠ i⌝
                      ∗ OwnGlobalSnapshot ({[ erasure e ]})
                      ∗ ⌜e ∈ compute_maximals LE_vc s'⌝
         }}}.

  Lemma deliver_spec_implies_simplified_wait_deliver_spec
    (deliver : val) (i : nat) (z : socket_address) :
  {{{ deliver_spec deliver i z }}}
    wait_deliver deliver @[ip_of_address z]
  {{{ wd, RET wd; simplified_wait_deliver_spec wd i z }}}.
  Proof.
    iIntros (Φ) "Hdeliver HΦ".
    iPoseProof (deliver_spec_implies_simplified_spec with "Hdeliver") as "#Hsimpl".
    unfold wait_deliver. wp_pures. iApply "HΦ".
    clear Φ.
    iIntros (s) "#Hi !>".
    iIntros (Φ) "HLoc HΦ".
    iLöb as "IH".
    wp_rec.
    wp_apply ("Hsimpl" with "Hi HLoc").
    iIntros (vo) "[HNone | HSome]".
    - iDestruct "HNone" as "[-> HLoc]".
      wp_match.
      iApply ("IH" with "HLoc HΦ").
    - iDestruct "HSome" as (v e) "(-> & H)".
      wp_pures.
      iApply "HΦ". iAssumption.
  Qed.
End Helpers.
