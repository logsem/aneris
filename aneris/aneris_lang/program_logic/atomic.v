From stdpp Require Import namespaces.
From iris.bi Require Import telescopes.
From iris.bi.lib Require Export atomic laterable.
From iris.proofmode Require Import tactics classes.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else. *)
Definition atomic_wp `{!anerisG Mdl Σ} {TA TB : tele}
  (e: expr) (* expression *)
  (ip: ip_address) (* ip address of node *)
  (Eo : coPset) (* (outer) mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (f: TA → TB → val) (* Turn the return data into the return value *)
  : iProp Σ :=
    (∀ (Φ : val → iProp Σ),
             atomic_update Eo ∅ α β (λ.. x y, Φ (f x y)) -∗
             WP e @[ip] {{ Φ }})%I.
(* Note: To add a private postcondition, use
   atomic_update α β Eo Ei (λ x y, POST x y -∗ Φ (f x y)) *)

Notation "'<<<' ∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<' ∃ y1 .. yn , β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             ip
             Eo
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. )
                        ) .. )
  )
  (at level 20, Eo, α, β, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  '@[' ip ]  Eo  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' ∀ x1 .. xn , α '>>>' e '@[' ip ] Eo '<<<' β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             e%E
             ip
             Eo
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) β%I
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) v%V
                        ) .. )
  )
  (at level 20, Eo, α, β, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  '@[' ip ]  Eo  '/' '[    ' '<<<'  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e '@[' ip ] Eo '<<<' ∃ y1 .. yn , β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             ip
             Eo
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. ))
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. ))
  )
  (at level 20, Eo, α, β, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<<'  α  '>>>'  '/  ' e  '@[' ip ]  Eo  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e '@[' ip ] Eo '<<<' β , 'RET' v '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             e%E
             ip
             Eo
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) v%V)
  )
  (at level 20, Eo, α, β, v at level 200,
   format "'[hv' '<<<'  α  '>>>'  '/  ' e  '@[' ip ]  Eo  '/' '[    ' '<<<'  β ,  '/' 'RET'  v  '>>>' ']' ']'")
  : bi_scope.

(** Theory *)
Section lemmas.
  Context `{!anerisG Mdl Σ} {TA TB : tele}.
  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (f : TA → TB → val).

  Lemma atomic_wp_mask_weaken e ip Eo1 Eo2 α β f :
    Eo2 ⊆ Eo1 → atomic_wp e ip Eo1 α β f -∗ atomic_wp e ip Eo2 α β f.
  Proof.
    iIntros (HEo) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. done.
  Qed.

  (* Atomic triples imply sequential triples if the precondition is laterable. *)
  Lemma atomic_wp_seq e ip Eo α β f {HL : ∀.. x, Laterable (α x)} :
    atomic_wp e ip Eo α β f -∗
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e @[ip] {{ Φ }}.
  Proof.
    rewrite ->tforall_forall in HL. iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply aneris_wp_frame_wand_l. iSplitL "HΦ"; first iAccu. iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. iIntros "HΦ". iApply "HΦ". done.
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_wp_seq_step e ip Eo α β f {HL : ∀.. x, Laterable (α x)} :
    TCEq (to_val e) None →
    atomic_wp e ip Eo α β f -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e @[ip] {{ Φ }}.
  Proof.
    iIntros (?) "H"; iIntros (Φ x) "Hα HΦ".
    iApply (aneris_wp_step_fupd _ _ ⊤ _ (∀.. y : TB, β x y -∗ Φ (f x y))
      with "[$HΦ //]"); first done.
    iApply (atomic_wp_seq with "H Hα"); first done.
    iIntros (y) "Hβ HΦ". by iApply "HΦ".
  Qed.

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_wp_atomic e ip Eo α β f `{!Atomic WeaklyAtomic (mkExpr ip e)} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e @[ip] ∅ {{ Φ }}) -∗
    atomic_wp e ip Eo α β f.
  Proof.
    iIntros "Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros (y) "Hβ".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iApply "HΦ".
  Qed.

  (* Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_wp_atomic e ip Eo (α : [tele] → iProp) (β : [tele] → TB → iProp)
        (f : [tele] → TB → val) {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ Φ (f [tele_arg] y)) -∗ WP e @[ip] {{ Φ }}) -∗
    atomic_wp e ip Eo α β f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_aneris_wp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply aneris_wp_fupd. iApply ("Hwp" with "Hα"). iIntros "!>" (y) "Hβ".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. done.
  Qed.

  (* We can open invariants around atomic triples.
     (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma wp_atomic_inv e ip Eo α β f N I :
    ↑N ⊆ Eo →
    atomic_wp e ip Eo (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) f -∗
    inv N I -∗ atomic_wp e ip (Eo ∖ ↑N) α β f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first done.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.
