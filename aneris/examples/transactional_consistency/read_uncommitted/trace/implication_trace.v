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

  Definition OwnLinTrace (γ : gname) (l : list val) : iProp Σ := True.

  Definition OwnLinHist (γ : gname) (l : list val) : iProp Σ := True.

  Lemma own_lin_hist (γ : gname) (l h : list val) :
    OwnLinTrace γ l ==∗ OwnLinTrace γ l ∗ OwnLinHist γ h.
  Proof.
  Admitted.

  Lemma own_lin_prefix (γ : gname) (l h : list val) :
    OwnLinTrace γ l -∗ 
    OwnLinHist γ h -∗
    (OwnLinTrace γ l ∗ OwnLinHist γ h ∗ ⌜h `prefix_of` l⌝).
  Proof.
  Admitted.

  Definition OwnTok (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma own_tok_excl (γ : gname) : 
    OwnTok γ -∗ OwnTok γ -∗ False.
  Proof. 
    iIntros "H1 H2". 
    by iDestruct (own_valid_2 with "H1 H2") as %?.
  Qed.

  (** Predicates for wrapped resources *)

  Definition last_commit : Prop := true.

  Definition open_start : Prop := true. 

  Definition latest_write : Prop := true. 

  (** Wrapped resources  *)
  (* Global Program Instance wrapped_resources (γm1 γm2 γl : gname) `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_ru ∗ 
                    ∃ t lt T, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ ⌜extraction_of lin_trace T⌝ ∗
                      (∃ (m : gmap socket_address local_state), ghost_map_auth γm1 (1%Qp) m ∗ 
                        (∀ sa s, m !! sa = Some s → 
                          (((⌜s = CanStart⌝ ∗ (∃ e, ⌜last_commit c e lt⌝) ∗
                             ∀ k, ⌜k ∈ KVS_keys⌝ → OwnWriteHalf c k ov ∗ OwnWriteHalf c k ov) ∨ 
                            (⌜s = Active domain⌝ ∗ (∃ e, ⌜open_start c e lt⌝) ∗
                             (∀ k, ⌜k ∈ domain⌝ → ∃ ov, OwnWriteHalf c k ov ∗ ⌜latest_write c k ov⌝) ∗
                             (∀ k, ⌜k ∈ KVS_keys / domain⌝ → OwnWriteHalf c k ov ∗ OwnWriteHalf c k ov)))))) ∗
                      (∃ (m : gmap string gname), ⌜∀ x, x ∈ dom m ↔ x ∈ tags t⌝ ∗ ghost_map_auth γm2 (1%Qp) m ∗
                        (∀ e_pre tag, ⌜e_pre ∈ t⌝ → ⌜is_pre_event e_pre⌝ → ⌜tagOfEvent e_pre = Some tag⌝ →
                          (∃ e_lin, ⌜e_lin ∈ lt⌝ ∧ ⌜tag_eq e_pre e_lin⌝) → ∃ γ, m !! tag = Some γ ∗ OwnTok γ)))%I;
      OwnMemKey k V := (OwnMemKey k V  ∗ (∀ v, ⌜v ∈ V⌝ → ∃ lt tag c, OwnLinHist t ∗ 
                        ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ t⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗ OwnWriteHalf c k ov)%I;
      ConnectionState c s sa := (ConnectionState c s sa ∗ ghost_map_elem γm1 sa (1%Qp) s)%I; 
      IsConnected c sa := IsConnected c sa%I;
      KVS_ru := KVS_ru;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := KVS_ClientCanConnect sa ∗ ghost_map_elem γm1 sa CanStart%I;
      Seen k V := Seen k V%I;
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted. *)

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