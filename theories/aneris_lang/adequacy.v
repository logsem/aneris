From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export lang resources network.
From aneris.aneris_lang.state_interp Require Export state_interp.
Set Default Proof Using "Type".

Import Network.

Definition aneris_model_rel_finitary (Mdl : Model) :=
  ∀ mdl : Mdl, quantifiers.smaller_card {mdl' : Mdl | Mdl mdl mdl'} nat.

Theorem adequacy `{anerisPreG Σ Mdl} IPs A B s e ip σ φ (st0 : Mdl) :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗
     ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] b ∈ B, b ⤳ (∅, ∅)) -∗
     frag_st st0 -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     WP (mkExpr ip e) @ s; ⊤ {{v, ⌜φ v⌝ }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate s (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros HMdlfin Hwp Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
  set (δ := @AnerisAuxState Mdl (∅,∅) st0).
  eapply (wp_adequacy _ (@aneris_AS Mdl) _ _ _ _  (δ  : aux_state aneris_AS)).
  { apply aneris_AS_valid_state_evolution_finitary; auto. }
  iIntros (?) "/=".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (fixed_init A) as (γsif) "#Hsif".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod free_ports_auth_init as (γpiu) "HPiu".
  iMod (messages_ctx_init B) as (γms) "[Hms HB]".
  iMod (model_init st0) as (γm) "[? Hfrag]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_fixed_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           anerisG_model_name := γm;
         |}).
  iMod (Hwp dg) as (f) "Hwp".
  iMod (saved_si_update A with "[$Hsi $Hsi']") as (M HMfs) "[HM #Hsa]".
  assert (dom (gset _) M = A) as Hdmsi.
  { apply set_eq => ?.
    split; intros ?%elem_of_elements;
      apply elem_of_elements; [by rewrite -HMfs|].
    by rewrite HMfs. }
  iAssert ([∗ set] s ∈ A, s ⤇ f s)%I as "#Hsa'".
  { rewrite -Hdmsi -!big_sepM_dom.
    iApply (big_sepM_mono with "[$Hsa]"); simpl; auto.
    iIntros (? ? Hx) "[? ?]"; iExists _; iFrame. }
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  iModIntro.
  iExists  (λ σ δ _, aneris_state_interp σ _ ∗ auth_st _)%I, (λ _, True)%I.
  iSplitR; [iApply config_wp_correct|].
  iSplitR "Hwp HIPs HB Hfrag"; last first.
  { iApply ("Hwp" with "Hsif Hsa' HB Hfrag HIPs Hn"). }
  iPoseProof (@aneris_state_interp_init _ _ dg IPs _ _ _ _ _
                with "[Hmp] [] [Hh] [Hs] [Hms] [] [HM] [] [HIPsCtx] [HPiu] ")
    as "Hsi"; eauto; iFrame.
Qed.

Definition safe e σ := @adequate aneris_lang NotStuck e σ (λ _ _, True).

Theorem adequacy_safe `{anerisPreG Σ Mdl} IPs A B e ip σ (ports : gset port)
        (st0 : Mdl):
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗
     ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] b ∈ B, b ⤳ (∅, ∅)) -∗
     frag_st st0 -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     WP (mkExpr ip e) {{v, True }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  safe (mkExpr ip e) σ.
Proof. by apply adequacy. Qed.

Theorem adequacy_hoare `{anerisPreG Σ Mdl} IPs A B e σ φ ip (st0 : Mdl) :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ ∃ (f : socket_address → socket_interp Σ),
          {{{ fixed A ∗
              ([∗ set] a ∈ A, a ⤇ (f a)) ∗
              ([∗ set] b ∈ B, b ⤳ (∅, ∅)) ∗
              frag_st st0 ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              is_node ip }}}
          (mkExpr ip e)
          {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate NotStuck (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros ? Hwp ???????.
  eapply (adequacy _ _ _ _ _ _ _ _ st0); try eauto.
  intros ?. iModIntro.
  iDestruct Hwp as (f) "#Hwp".
  iExists f. iIntros "??????".
  iApply ("Hwp" with "[$]"); auto.
Qed.

Definition simulation_adequacy Σ Mdl `{!anerisPreG Σ Mdl} (s: stuckness)
           (IPs: gset ip_address)
           (A B: gset socket_address)
           (ξ: execution_trace aneris_lang → auxiliary_trace aneris_AS → Prop)
           ip e1 σ1 st (δ: aux_state (@aneris_AS Mdl)):
  δ = {| aneris_AS_mhist := (∅,∅); aneris_AS_model := st |} ->
  (* The model has finite branching *)
  aneris_model_rel_finitary Mdl →
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ1) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ1 !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a postcondition and a socket interpretation function *)
        ∃ Φ (f : socket_address → socket_interp Σ),
          (* Given resources reflecting initial configuration, we need *)
  (*            to prove two goals *)
          fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
          ([∗ set] b ∈ B, b ⤳ (∅, ∅)) -∗
          ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗ frag_st st ={⊤}=∗
          WP (mkExpr ip e1) @ s; ⊤ {{ Φ }} ∗
          □ (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace aneris_AS)
            δ' c κs,
         ⌜valid_system_trace aneris_AS ex atr⌝ -∗
         ⌜exec_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
         ⌜auxtr_starts_in atr δ⌝ -∗
         ⌜exec_ends_in ex c⌝ -∗
         ⌜auxtr_ends_in atr δ'⌝ -∗
         ⌜∀ ex' atr',
            exec_contract ex ex' → auxtr_contract atr atr' →
            ξ ex' atr' ∧ ∀ δ4 c4 κs4,
             exec_ends_in ex' c4 → auxtr_ends_in atr' δ4 →
             exec_last_obs ex κs4 →
             valid_state_evolution aneris_AS c4.2 δ4 κs4 c.2 δ'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         state_interp c.2 δ' κs (length c.1) -∗
         posts_of c.1 (Φ :: replicate (length c.1 - 1) fork_post) -∗
         |={⊤, ∅}=> ⌜ξ ex atr⌝)) →
  (* The coinductive pure coq proposition given by adequacy *)
  continued_simulation
    ξ
    (singleton_exec ([(mkExpr ip e1)], σ1))
    (singleton_auxtr δ).
Proof.
  intros Hδ Hsc Hips Hdom Hports Hsa Hheaps Hsockets Hms Hwp.
  eapply (wp_strong_adequacy aneris_lang aneris_AS Σ s ξ).
  { apply aneris_AS_valid_state_evolution_finitary; auto. }
  iIntros (?) "".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (fixed_init A) as (γsif) "#Hsif".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod free_ports_auth_init as (γpiu) "HPiu".
  iMod (messages_ctx_init B) as (γms) "[Hms HB]".
  iMod (model_init δ.(aneris_AS_model)) as (γm) "[Hmdl_auth Hmdl_frag]".
  set (distG :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_fixed_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           anerisG_model_name := γm;
         |}).
  iMod (Hwp distG) as "Hwp". iDestruct "Hwp" as (Φ f) "Himpl".
  iMod (saved_si_update A with "[$Hsi $Hsi']") as (M HMfs) "[HM #Hsa]".
  assert (dom (gset _) M = A) as Hdmsi.
  { apply set_eq => ?.
    split; intros ?%elem_of_elements;
      apply elem_of_elements; [by rewrite -HMfs|].
    by rewrite HMfs. }
  iAssert ([∗ set] s ∈ A, s ⤇ f s)%I as "#Hsa'".
  { rewrite -Hdmsi -!big_sepM_dom.
    iApply (big_sepM_mono with "[$Hsa]"); simpl; auto.
    iIntros (? ? Hx) "[? ?]"; iExists _; iFrame. }
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  subst δ.
  iMod ("Himpl" with "[$] [$] [$] [$] [$] [$]") as "[Hwp #Himpl]".
  iModIntro. iExists state_interp, Φ, fork_post.
  iSplitL ""; first by iApply config_wp_correct.
  iFrame "#Hwp".
  iPoseProof (@aneris_state_interp_init _ _ distG IPs _ _ _ _ _
                with "[Hmp] [] [Hh] [Hs] [Hms] [] [HM] [] [HIPsCtx] [HPiu] ")
    as "Hsi"; eauto; iFrame.
Qed.
