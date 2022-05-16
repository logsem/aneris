(**  The specs of the mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.examples.rcb.spec Require Import base.
From aneris.prelude Require Import time.
From aneris.examples.rcb.model Require Import events.

Section Model_spec.
    Context `{!anerisG Mdl Σ, !RCB_params}.

     Definition empty_ghst : gset global_event := ∅.
     Definition empty_lhsts : list (gset local_event) :=
       (λ x, ∅) <$> RCB_addresses.

     Record Gst : Type :=
       GST { Gst_ghst : gset global_event;
             Gst_hst : list (gset local_event)}.

     Definition empty_Gst : Gst := GST empty_ghst empty_lhsts.

     Class RCB_global_state_valid :=
      {
        RCBM_GstValid (gs : Gst): Prop;

        RCBM_GstValid_empty : RCBM_GstValid empty_Gst;

        RCBM_GstValid_ghst_ext (gs : Gst)
                              (a a' : global_event):
          RCBM_GstValid gs →
          a ∈ gs.(Gst_ghst) → a' ∈ gs.(Gst_ghst) →
          ge_time a = ge_time a' →
          a = a';

        RCBM_GstValid_lhst_size (gs : Gst) :
          RCBM_GstValid gs →
          length gs.(Gst_hst) = length RCB_addresses;

        RCBM_GstValid_orig (gs : Gst) (a : global_event) :
          RCBM_GstValid gs ->
          a ∈ gs.(Gst_ghst) ->
          a.(ge_orig) < length RCB_addresses;

        RCBM_GstValid_time_length (gs : Gst) (a : global_event) :
          RCBM_GstValid gs ->
          a ∈ gs.(Gst_ghst) ->
          length a.(ge_time) = length RCB_addresses;

        RCBM_GstValid_lhst_ext (gs : Gst) (i i' : nat) (s s' : gset local_event)
                              (e e' : local_event):
          RCBM_GstValid gs →
          gs.(Gst_hst) !! i = Some s →
          gs.(Gst_hst) !! i' = Some s' →
          e ∈ s → e' ∈ s' → le_time e = le_time e' →
          e.(le_payload) = e'.(le_payload) ∧ e.(le_orig) = e'.(le_orig);

        RCBM_GstValid_lhst_strong_ext (gs : Gst) (i : nat) (s : gset local_event)
                                     (e e' : local_event):
          RCBM_GstValid gs →
          gs.(Gst_hst) !! i = Some s → e ∈ s → e' ∈ s →
          le_time e = le_time e' → e = e';

        RCBM_GstValid_le_provenance (gs : Gst) (i : nat) (s : gset local_event)
                                   (e : local_event) :
          RCBM_GstValid gs →
          gs.(Gst_hst) !! i = Some s → e ∈ s →
          erase e ∈ gs.(Gst_ghst);

        RCBM_GstValid_ge_provenance (gs : Gst) (a : global_event) :
          RCBM_GstValid gs ->
          a ∈ gs.(Gst_ghst) ->
          ∃ s e, gs.(Gst_hst) !! a.(ge_orig) = Some s /\
                 e ∈ s /\
                 erase e = a;

        RCBM_GstValid_causality
          (gs : Gst) (i : nat) (s : gset local_event)
          (e : local_event) (a : global_event) :
          RCBM_GstValid gs →
          gs.(Gst_hst) !! i = Some s →
          a ∈ gs.(Gst_ghst) → e ∈ s → vector_clock_lt (ge_time a) (le_time e) →
          ∃ e', e' ∈ s ∧ erase e' = a;
      }.

End Model_spec.
