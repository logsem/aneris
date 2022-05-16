(**  The specs of the mathematical model of the causal memory implementation
     from "Causal memory: definitions, implementation, and programming"
     (https://link.springer.com/article/10.1007/BF01784241).*)

From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.examples.ccddb.spec Require Import base.
From aneris.prelude Require Import time.
From aneris.examples.ccddb.model Require Import events.

Section Model_spec.
    Context `{!anerisG Mdl Σ, !DB_params}.

     Definition empty_gmem : gmap Key (gset write_event) :=
       (gset_to_gmap (∅ : gset write_event) DB_keys).
     Definition empty_lhsts : list (gset apply_event) :=
       (λ x, ∅) <$> DB_addresses.

     Record Gst : Type :=
       GST { Gst_mem : gmap Key (gset write_event);
             Gst_hst : list (gset apply_event)}.

     Definition empty_Gst : Gst := GST empty_gmem empty_lhsts.

     Class DB_global_state_valid :=
      {
        DBM_GstValid (gs : Gst): Prop;
        DBM_GstValid_empty : DBM_GstValid empty_Gst;
        DBM_GstValid_dom gs :
          DBM_GstValid gs →
          dom gs.(Gst_mem) = DB_keys;
        DBM_GstValid_lhst_size (gs : Gst) :
          DBM_GstValid gs →
          length gs.(Gst_hst) = length DB_addresses;
        DBM_GstValid_gmem_ext (gs : Gst) (k k' : Key) (h h' : gset write_event)
                              (a a' : write_event):
          DBM_GstValid gs →
          gs.(Gst_mem) !! k = Some h → gs.(Gst_mem) !! k' = Some h' →
          a ∈ h → a' ∈ h' → we_time a = we_time a' → a = a';
        DBM_GstValid_lhst_ext (gs : Gst) (i i' : nat) (s s' : gset apply_event)
                              (e e' : apply_event):
          DBM_GstValid gs →
          gs.(Gst_hst) !! i = Some s →
          gs.(Gst_hst) !! i' = Some s' →
          e ∈ s → e' ∈ s' → ae_time e = ae_time e' →
          e.(ae_key) = e'.(ae_key) ∧ e.(ae_val) = e'.(ae_val);
        DBM_GstValid_lhst_strong_ext (gs : Gst) (i : nat) (s : gset apply_event)
                                     (e e' : apply_event):
          DBM_GstValid gs →
          gs.(Gst_hst) !! i = Some s → e ∈ s → e' ∈ s →
          ae_time e = ae_time e' → e = e';
        DBM_GstValid_ae_provenance (gs : Gst) (i : nat) (s : gset apply_event)
                                   (e : apply_event) :
          DBM_GstValid gs →
          gs.(Gst_hst) !! i = Some s → e ∈ s →
          ∃ (h : gset write_event),
            gs.(Gst_mem) !! e.(ae_key) = Some h ∧ erase e ∈ h;
        DBM_GstValid_causality
          (gs : Gst) (i : nat) (s : gset apply_event) (k : Key)
          (h: gset write_event) (e : apply_event) (a : write_event) :
          DBM_GstValid gs →
          gs.(Gst_mem) !! k = Some h → gs.(Gst_hst) !! i = Some s →
          a ∈ h → e ∈ s → vector_clock_lt (we_time a) (ae_time e) →
          ∃ e', e' ∈ (restrict_key k s) ∧ erase e' = a;
      }.

End Model_spec.
