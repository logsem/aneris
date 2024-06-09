From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import code_api wrapped_library.
From aneris.examples.transactional_consistency.read_uncommitted.specs Require Import specs resources.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs state_based_model.

Section trace_proof.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params}.

  Definition trace_inv_name := nroot.@"trinv".

  (** Ghost theory for wrapped resources *)

  (* For the OwnLinTrace/OwnLinHist resources and 
     rules we are reusing trace infrastructure *)

  Definition OwnLinHist (γ : gname) (l : list val) : iProp Σ :=
    own γ (◯ (gmap_of_trace 0 l)).

  Definition OwnLinTrace (γ : gname) (l : list val) : iProp Σ := 
    own γ (● gmap_of_trace 0 l) ∗ OwnLinHist γ l.

  Lemma own_lin_hist (γ : gname) (l : list val) :
    OwnLinTrace γ l ==∗ OwnLinTrace γ l ∗ OwnLinHist γ l.
  Proof.
    rewrite /OwnLinTrace.
    iIntros "(H1 & #H2)".
    iModIntro.
    iFrame "#∗".
  Qed.

  Lemma own_lin_prefix (γ : gname) (l h : list val) :
    OwnLinTrace γ l ∗ OwnLinHist γ h -∗
    OwnLinTrace γ l ∗ OwnLinHist γ h ∗ ⌜h `prefix_of` l⌝.
  Proof.
    rewrite /OwnLinTrace /OwnLinHist.
    iIntros "((H1 & H2) & H3)".
    iDestruct (own_op with "[$H1 $H3]") as "H".
    iDestruct (own_valid with "H") as %[Hsub Hvalid]%auth_both_valid_discrete.
    iDestruct "H" as "(H1 & H3)".
    iFrame.
    iPureIntro. 
    eapply gmap_of_trace_hist_valid_prefix; eauto.
  Qed.

  Lemma own_lin_add (γ : gname) (l: list val) (v : val) :
    OwnLinTrace γ l ==∗ OwnLinTrace γ (l ++ [v]).
  Proof.
    rewrite /OwnLinTrace /OwnLinHist.
    iIntros "(H1 & H2)".
    rewrite gmap_of_trace_snoc Nat.add_0_l.
    iMod (own_update_2 with "H1 H2") as "[H1 H2]".
    apply auth_update.
    eapply (alloc_local_update _ _ (length l : nat) (to_agree v)); try done.
    { 
      eapply not_elem_of_dom.
      rewrite gmap_of_trace_dom.
      intro Hfalse. 
      lia. 
    }
    iModIntro. 
    iFrame.
  Qed.

  (** Predicates for wrapped resources *)

  Definition last_commit (c le : val) (ltrace : list val ) : Prop := true.

  Definition open_start (c le : val) (ltrace : list val ) : Prop := true. 

  Definition latest_write (c : val) (k : Key) (ov : option val): Prop := true. 

  Definition tag_eq (e1 e2 : val) : Prop := true.

  (** Extended global invaraint *)

  Definition GlobalInvExt (γm1 γm2 γmk γl : gname) : iProp Σ := 
    ∃ t lt T, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ ⌜extraction_of lt T⌝ ∗
      (∃ (m1 : gmap socket_address (local_state * option val)), ghost_map_auth γm1 (1%Qp) m1 ∗ 
        ((∀ sa s, ⌜m1 !! sa = None ∨ m1 !! sa = Some (s, None)⌝ → ghost_map_auth γmk (1%Qp) ∅) ∨
          (∀ sa s c, ⌜m1 !! sa = Some (s, Some c)⌝ → 
            ∃ (mk : gmap (val * Key) (option val)), ghost_map_auth γmk (1%Qp) mk ∗
            (((⌜s = CanStart⌝ ∗ (∃ e, ⌜last_commit c e lt⌝) ∗ 
              (∀ k, ⌜k ∈ KVS_keys⌝ → ∃ ov, ghost_map_elem γmk (c, k) (DfracOwn 1%Qp) ov)) ∨ 
              (∃ domain, ⌜s = Active domain⌝ ∗ (∃ e, ⌜open_start c e lt⌝) ∗
              (∀ k, ⌜k ∈ KVS_keys ∖ domain⌝ → ∃ ov, ghost_map_elem γmk (c, k) (DfracOwn 1%Qp) ov) ∗
              (∀ k, ⌜k ∈ domain⌝ → ∀ ov, ⌜mk !! (c, k) = Some ov⌝ → ⌜latest_write c k ov⌝ ))))))) ∗
      (∃ (m2 : gmap string bool), ⌜∀ (x : string), x ∈ (dom m2) ↔ x ∈ tags t⌝ ∗ ghost_map_auth γm2 (1%Qp) m2 ∗
        (∀ e_pre tag, ⌜e_pre ∈ t⌝ → ⌜is_pre_event e_pre⌝ → ⌜tagOfEvent e_pre = Some tag⌝ →
          (∃ e_lin, ⌜e_lin ∈ lt⌝ ∧ ⌜tag_eq e_pre e_lin⌝) → 
          ghost_map.ghost_map_elem γm2 tag (DfracOwn 1%Qp) true)).

  (** Wrapped resources *)
  Global Program Instance wrapped_resources (γm1 γm2 γmk γl : gname) `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_ru ∗ inv KVS_InvName (GlobalInvExt γm1 γm2 γmk γl))%I;
      OwnMemKey k V := (OwnMemKey k V  ∗ (∀ v, ⌜v ∈ V⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
                        ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗ ghost_map_elem γmk (c, k) (DfracOwn 1%Qp) ov ∗ ⌜k ∈ KVS_keys⌝)%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ ghost_map_elem γm1 sa (DfracOwn 1%Qp) (s, Some c))%I; 
      IsConnected c sa := IsConnected c sa%I;
      KVS_ru := KVS_ru;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ ghost_map_elem γm1 sa (DfracOwn 1%Qp) (CanStart, None))%I;
      Seen k V := Seen k V%I;
    |}.
  Next Obligation.
    iIntros (????????) "(Hkey & Hghost_elem & %Hin)".
    iDestruct (res.(read_uncommitted.specs.resources.OwnLocalKey_serializable) with "Hkey") as "(Hkey & Hser)".
    by iFrame.
  Qed.
  Next Obligation.
    iIntros.
  Admitted.
  Next Obligation.
    iIntros.
  Admitted.
  Next Obligation.
    iIntros.
  Admitted.

  Lemma library_implication `{!anerisG Mdl Σ} (clients : gset socket_address) 
  (lib : KVS_transaction_api) :
    ((RU_spec clients lib) ∗ trace_is [] ∗ trace_inv trace_inv_name valid_trace_ru) ={⊤}=∗ 
    RU_spec clients (KVS_wrapped_api lib).
  Proof.
    iIntros "([%res (Hkeys & Hkvs_init & Hglob_inv & Hcan_conn & 
      (#Hinit_kvs & #Hinit_cli & #Hread & #Hwrite & #Hstart & #Hcom))] & Htr & #Htr_inv)".
  iModIntro.
  iExists _.
  Admitted.
End trace_proof.