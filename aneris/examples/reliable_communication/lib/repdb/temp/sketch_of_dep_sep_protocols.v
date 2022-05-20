From iris.algebra Require Import excl.
From trillium.prelude Require Import finitary.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import monitor_proof set_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import tactics proofmode.
From actris.channel Require Export proto.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication.spec Require Import resources proofmode api_spec.
From aneris.examples.reliable_communication.lib.repdb.spec Require Import db_params ras time events resources.

Section Proto.
  Context `{!anerisG Mdl Σ}.
  Context (ReqData : Type).
  Context (RepData : Type).
  Context (ReqPre : val → ReqData → iProp Σ).
  Context (ReqPost : val → ReqData → val → RepData → iProp Σ).

  Definition req_prot_aux (rec : iProto Σ)  : iProto Σ :=
    (<! (reqv : val) (reqd : ReqData) >
       MSG reqv {{ ReqPre reqv reqd }} ;
     <? (repv : val) (repd : RepData) >
       MSG repv {{ ReqPost reqv reqd repv repd }};
     rec)%proto.

  Instance req_prot_aux_contractive : Contractive (req_prot_aux).
  Proof. solve_proto_contractive. Qed.
  Definition req_prot : iProto Σ := fixpoint (req_prot_aux).
  Global Instance req_prot_unfold :
    ProtoUnfold req_prot (req_prot_aux req_prot).
  Proof. apply proto_unfold_eq, fixpoint_unfold. Qed.
End Proto.


Section Proto_simplified.
  Context `{!anerisG Mdl Σ}.
  Context `{!DB_params, !DB_time, !DB_events, !DB_resources Mdl Σ }.
  Definition ReqData : Type :=
    (string * val) * (ghst * option we) + string * (Qp * option we).
  Definition RepData : Type := ghst * we + option we.
  Definition ReqPre (reqv : val) (reqd : ReqData) : iProp Σ :=
    (∃ k wo v h,
      ⌜k ∈ DB_keys⌝ ∗ k ↦ₖ wo ∗
     ⌜reqd = inl ((k, v), (h, wo))⌝ ∗
     ⌜reqv = (#(LitString k), v)%V⌝ ∗
      Obs DB_addr h ∗ ⌜at_key k h = wo⌝) ∨
    (∃ k q wo,
      ⌜k ∈ DB_keys⌝ ∗ k ↦ₖ{q} wo ∗
      ⌜reqd = inr (k, (q, wo))⌝ ∗ ⌜reqv = #(LitString k)⌝).

  Definition ReqPost
    (_reqv : val) (reqd : ReqData)
    (repv : val) (repd : RepData) : iProp Σ :=
    (∀ k v h wold,
        ⌜reqd = inl ((k, v), (h, wold))⌝ -∗
        ∃ hf a_new,
        ⌜repd = inl (hf, a_new)⌝ ∗
        ⌜repv = #()⌝ ∗
        ⌜WE_key a_new = k⌝ ∗ ⌜WE_val a_new = v⌝ ∗
        ⌜at_key k hf = None⌝ ∗ Obs DB_addr (h ++ hf ++ [a_new]) ∗ k ↦ₖ Some a_new) ∨
    (∀ k q wo,
        ⌜reqd = inr (k, (q, wo))⌝ -∗
        ⌜repd = inr wo⌝ ∗
        ∃ vo, ⌜repv = vo⌝ ∗
          ((⌜vo = NONEV⌝ ∗ ⌜wo = None⌝) ∨
          (∃ a, ⌜vo = SOMEV (WE_val a)⌝ ∗ ⌜wo = Some a⌝))).

  Definition req_prot_def := @req_prot Σ ReqData RepData ReqPre ReqPost.

End Proto_simplified.

Section Proto_write_hocap.
  Context `{!anerisG Mdl Σ}.
  Context `{!DB_params, !DB_time, !DB_events, !DB_resources Mdl Σ }.
  Definition ReqData' : Type :=
    (coPset * (string * val) * (iProp Σ * (we → ghst → ghst → iProp Σ))) +
    string * (Qp * option we).
  Definition RepData' : Type := we * ghst * ghst + option we.
  Definition ReqPre' (reqv : val) (reqd : ReqData') : iProp Σ :=
    (∃ E k v P Q,
     ⌜reqd = inl (E, (k, v), (P, Q))⌝ ∗
     ⌜reqv = (#(LitString k), v)%V⌝ ∗
     ⌜↑DB_InvName ⊆ E⌝ ∗
     ⌜k ∈ DB_keys⌝ ∗
     P ∗
     □ (P
         ={⊤, E}=∗
         ∃ (h : ghst) (a_old: option we),
           ⌜at_key k h = a_old⌝ ∗
            k ↦ₖ a_old ∗
            Obs DB_addr h ∗
            ▷ (∀ (hf : ghst) (a_new : we),
                  ⌜at_key k hf = None⌝ ∗
                  ⌜WE_key a_new = k⌝ ∗ ⌜WE_val a_new = v⌝ ∗
                  ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
                  k ↦ₖ Some a_new ∗
                  Obs DB_addr (h ++ hf ++ [a_new]) ={E,⊤}=∗ Q a_new h hf))) ∨
    (∃ k wo q, ⌜k ∈ DB_keys⌝ ∗ k ↦ₖ{q} wo ∗ ⌜reqd = inr (k, (q, wo))⌝ ∗ ⌜reqv = #(LitString k)⌝).

  Definition ReqPost'
    (_reqv : val) (reqd : ReqData')
    (repv : val) (repd : RepData') : iProp Σ :=
    (∀ E k v P Q, ⌜reqd = inl (E, (k, v), (P, Q))⌝ -∗
       ∃ a_new h hf, ⌜repd = inl (a_new, h, hf)⌝ ∗ ⌜repv = #()⌝ ∗ Q a_new h hf) ∨
    (∀ k wo q, ⌜reqd = inr (k, (q, wo))⌝ -∗
       ∃ vo, ⌜repd = inr wo⌝ ∗ ⌜repv = vo⌝ ∗  k ↦ₖ{q} wo ∗
       ((⌜vo = NONEV⌝ ∗ ⌜wo = None⌝) ∨
        (∃ a, ⌜vo = SOMEV (WE_val a)⌝ ∗ ⌜wo = Some a⌝))).

  Definition req_prot_def' := @req_prot Σ ReqData' RepData' ReqPre' ReqPost'.

End Proto_write_hocap.
