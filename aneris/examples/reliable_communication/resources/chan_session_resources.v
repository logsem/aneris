From iris.algebra Require Import agree gmap auth excl numbers frac_auth csum.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import invariants mono_nat.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import resources.
From aneris.examples.reliable_communication.resources Require Export prelude.

Set Default Proof Using "Type".

(** Note that this file does not import user params, i.e.
    the definitions below are independent w.r.t. concrete physical/logical user parameters.  *)


(** Meta tokens tracking connection between physical data and ghost names. *)
Section KnownSessions.
  Context `{!anerisG Mdl Σ, !chanG Σ, !server_ghost_names}.

  (** Meta token tracking for the socket_address of each known client (half or fully connected),
      the ghost name of the corresponding session. *)
  (* TODO: define auth part, update, and alloc lemmas from all resources below. *)

  Definition known_sessions (M : session_names_map) : iProp Σ :=
    own γ_srv_known_sessions_name (● (to_agree <$> M : gmap _ _)).

  Definition session_token (sa : socket_address) (γ : session_name) : iProp Σ :=
    own γ_srv_known_sessions_name (◯ {[ sa := to_agree γ ]}).

  Global Instance session_tokenPersistent sa γ : Persistent (session_token sa γ).
  Proof. apply _. Qed.

  Lemma session_token_agree sa γ1 γ2 :
    session_token sa γ1 -∗ session_token sa γ2 -∗ ⌜γ1 = γ2⌝.
  Proof.
    iIntros "Hγ1 Hγ2".
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
    iPureIntro.
    rewrite -auth_frag_op singleton_op  in Hval.
    apply auth_frag_valid_1 in Hval.
    specialize (Hval sa).
    rewrite lookup_singleton in Hval.
    rewrite Some_op in Hval.
    revert Hval.
    rewrite Some_valid.
    intros Hval.
    by apply (to_agree_op_inv_L (A:=leibnizO _ )) in Hval.
  Qed.

End KnownSessions.

Section OneShot.
  Context `{!anerisG Mdl Σ, !chanG Σ, !server_ghost_names}.

  (** Session mode one shot algebra. *)
  Definition SM := csum (excl unit) (agree unit).

  (** Half-opened connection *)
  Definition SM_opened : SM := Cinl (Excl ()).
  (** Established connection *)
  Definition SM_connected : SM := Cinr (to_agree ()).

  Global Instance SM_opened_excl_instance : Exclusive SM_opened.
  Proof. apply _. Qed.

  Global Instance SM_connected_pers γ : Persistent (own γ SM_connected).
  Proof. apply _. Qed.

  Lemma SM_update : SM_opened ~~> SM_connected.
  Proof. by apply cmra_update_exclusive. Qed.

  Lemma SM_own_update γ : own γ SM_opened ==∗ own γ SM_connected.
  Proof. apply own_update, SM_update. Qed.

  Lemma SM_opened_excl γ (e : oneShotR) : own γ SM_opened ⊢ own γ e -∗ False.
  Proof.
    iIntros "Hun Hother".
    iDestruct (own_valid_2 with "Hun Hother") as "%Hv".
    exfalso.
    apply (exclusive0_l SM_opened e).
    by apply cmra_valid_validN.
  Qed.

  Definition session_half_opened (sa : socket_address) (γs : session_name) : iProp Σ:=
    session_token sa γs ∗ own (session_status_gname γs) SM_opened.

  Definition session_connected (sa : socket_address) (γs : session_name) : iProp Σ :=
    session_token sa γs ∗ own (session_status_gname γs) SM_connected.

End OneShot.

(** Session Protocol invariant and initial resource definitions. *)
Section iProto_sessions.
  Context `{!anerisG Mdl Σ, !chanG Σ, !server_ghost_names}.

  Definition can_init
    (γs : session_name) (clt_addr : socket_address) (p : iProto Σ) (s : side) : iProp Σ :=
    session_token clt_addr γs ∗
    mono_nat_auth_own (side_elim s (session_clt_idx_name γs) (session_srv_idx_name γs)) 1 0 ∗
    mono_nat_lb_own (side_elim s (session_srv_idx_name γs) (session_clt_idx_name γs)) 0 ∗
    ses_own (chan_N (session_chan_name γs))
            (chan_session_escrow_name (session_chan_name γs)) s 0 0 p.

  Definition CookieRes (sa : socket_address) (n : nat) : iProp Σ :=
    ∃ (γs : session_name),
      session_token sa γs ∗
      own (session_srv_cookie_name γs) (◯F n).

  Definition CookieTokenFull (sa : socket_address) (n : nat) : iProp Σ :=
    ∃ (γs : session_name),
      session_token sa γs ∗
        own (session_srv_cookie_name γs) (●F n).

  Lemma CookieRes_excl sa n1 n2: CookieRes sa n1 ⊢  CookieRes sa n2 -∗ False.
  Proof.
    iDestruct 1 as (?) "(Htk1 & Hown1)".
    iDestruct 1 as (?) "(Htk2 & Hown2)".
    iDestruct (session_token_agree with "Htk1 Htk2") as "<-".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hvl.
    by apply frac_auth_frag_op_valid in Hvl as [Hvl _].
  Qed.

  Lemma CookieRes_Full_valid sa n1 n2: CookieTokenFull sa n1 ⊢  CookieRes sa n2 -∗ ⌜n1 = n2⌝.
  Proof.
    iDestruct 1 as (?) "(Htk1 & Hown1)".
    iDestruct 1 as (?) "(Htk2 & Hown2)".
    iDestruct (session_token_agree with "Htk1 Htk2") as "<-".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hvl.
    by apply frac_auth.frac_auth_agree_L in Hvl.
  Qed.

  Lemma session_map_update
        (M : session_names_map) (sa : socket_address) (p : iProto Σ)
        (cookie : nat) (N: namespace) (E : coPset) :
    ⌜sa ∉ dom M⌝ -∗
    known_sessions M -∗
    |~{E}~| ∃ (γ : session_name),
      (known_sessions (<[sa := γ]>M)) ∗
      session_token sa γ ∗
      session_half_opened sa γ ∗
      CookieTokenFull sa cookie ∗
      CookieRes sa cookie ∗
      can_init γ sa p Left ∗
      can_init γ sa (iProto_dual p) Right.
    Proof.
    iIntros (Hfresh) "Hkn".
    iApply step_get_impl; [iApply (step_get_Ses_init (N.@ (socket_address_to_str sa)) _ p)|].
    iDestruct 1 as (γ_s) "(#Hses & Hownl & Hownr)".
    set (γ_chan := ChanName γ_s (N.@ (socket_address_to_str sa))).
    iApply step_get_open.
    iMod (mono_nat_own_alloc 0%nat) as (γ_srv_idx) "(Hsrv_idxA & Hsrv_idxF)".
    iMod (mono_nat_own_alloc 0%nat) as (γ_clt_idx) "(Hclt_idxA & Hclt_idxF)".
    iMod (own_alloc (● (to_agree <$> (∅: session_names_map) : session_names_mapUR)))
      as (γsa) "Hsa".
    { rewrite fmap_empty. by apply auth_auth_valid. }
    iMod (own_alloc (A := frac_authR natR) (●F cookie ⋅ ◯F cookie)) as (γ_ck) "(HckF & Hck)".
    { by apply frac_auth_valid. }
    iMod (own_alloc (SM_opened)) as (γ_mode) "Hmode"; first done.
    set (γ_session := SessionName γ_chan γ_clt_idx γ_srv_idx γ_ck γ_mode).
    iMod (own_update
            _ _ (● (to_agree <$>
            ((<[sa := γ_session]>M)) : session_names_mapUR) ⋅ (◯ {[sa := to_agree γ_session]}))
           with "[$Hkn]") as "[HS #Hs]".
    { rewrite fmap_insert. apply auth_update_alloc, @alloc_local_update; last done.
      apply not_elem_of_dom; rewrite dom_fmap; done. }
    iModIntro. iApply step_get_intro. iModIntro.
    iExists γ_session.
    rewrite /known_sessions /CookieRes /CookieTokenFull.
    iFrame "#∗".
    iSplitL "HckF"; by eauto.
  Qed.

End iProto_sessions.
