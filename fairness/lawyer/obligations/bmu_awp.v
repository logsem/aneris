(** This file declares notation for logically atomic Hoare triples, and some
generic lemmas about them. To enable the definition of a shared theory applying
to triples with any number of binders, the triples themselves are defined via telescopes, but as a user
you need not be concerned with that. You can just use the following notation:

  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition | z, RET return_value; private_postcondition }>>

Here, [x] (which can be any number of binders, including 0) is bound in all of
the atomic pre- and postcondition and the private (non-atomic) postcondition and
the return value, [y] (which can be any number of binders, including 0) is bound
in both postconditions and the return value, and [z] (which can be any number of
binders, including 0) is bound in the return value and the private
postcondition.

Note that atomic triples are *not* implicitly persistent, unlike Texan triples.
If you need a private (non-atomic) precondition, you can use a magic wand:

  private_precondition -∗
  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition
    | z, RET return_value; private_postcondition }>>

If you don't need a private postcondition, you can leave it away, e.g.:

  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition | RET return_value }>>

Note that due to combinatorial explosion and because Coq does not have a
facility to declare such notation in a compositional way, not *all* variants of
this notation exist: if you have binders before the [RET] (which is very
uncommon), you must have a private postcondition (it can be [True]), and you
must have [∀∀] and [∃∃] binders (they can be [_: ()]).

For an example for how to prove and use logically atomic specifications, see
[iris_heap_lang/lib/increment.v].

*)

From stdpp Require Import namespaces.
From iris.bi Require Import telescopes.
(* From iris.bi.lib Require Export atomic. *)
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic bmu_atomic.
From trillium.fairness.lawyer Require Import sub_action_em.
From iris.proofmode Require Import proofmode classes.
(* From iris.program_logic Require Export weakestpre. *)
From trillium.program_logic Require Export weakestpre.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else.

For the non-atomic post-condition, we use an [option PROP], combined with a
[-∗?]. This is to avoid introducing spurious [True -∗] into proofs that do not
need a non-atomic post-condition (which is most of them). *)
Definition BMU_atomic_wp
  {Σ}             
  {IG: invGS_gen HasNoLc Σ}
  `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
  `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
   (Degree := ofe_car DegO)
   (Level := ofe_car LevelO)
   {LIM_STEPS}
   {OPRE: ObligationsParamsPre Degree Level LIM_STEPS}
   (OP := LocaleOP (Locale := locale heap_lang))
   {oGS: @asem_GS _ _ ObligationsASEM Σ}
    `{EM: ExecutionModel heap_lang M}
    `{hGS: @heapGS Σ _ EM}
  {TA TB TP : tele}
  (τ: locale heap_lang)
  (e: expr heap_lang) (* expression *)
  (c: nat) (* BMU bound *)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (POST: TA → TB → TP → option (iProp Σ)) (* non-atomic post-condition *)
  (f: TA → TB → TP → val heap_lang) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : val heap_lang → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            BMU_atomic_update c (⊤∖E) ∅ α β (λ.. x y, ∀.. z, POST x y z -∗? Φ (f x y z)) (oGS := oGS) -∗
            WP e @ τ {{ Φ }}.

(** We avoid '<<{'/'}>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ τ ; E % c '<<{' ∃∃ y1 .. yn , β '|' z1 .. zn , 'RET' v ; POST '}>>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (BMU_atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
             τ e%E c E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, Some POST%I) ..
                                  ) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, v%V) ..
                                  ) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e @ τ ; E % c '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' z1  ..  zn ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.


(* There are overall 16 of possible variants of this notation:
- with and without ∀∀ binders
- with and without ∃∃ binders
- with and without RET binders
- with and without POST

However we don't support the case where RET binders are present but anything
else is missing. Below we declare the 8 notations that involve no RET binders.
*)

(* No RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ τ ; E % c '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (BMU_atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             τ e%E c E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e @ τ ; E % c  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* (* No ∃∃ binders, no RET binders *) *)
(* Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" := *)
(*   (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) *)
(*              (TB:=TeleO) *)
(*              (TP:=TeleO) *)
(*              e%E *)
(*              E *)
(*              (tele_app $ λ x1, .. (λ xn, α%I) ..) *)
(*              (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. ) *)
(*              (tele_app $ λ x1, .. (λ xn, *)
(*                          tele_app $ tele_app $ Some POST%I *)
(*                         ) .. ) *)
(*              (tele_app $ λ x1, .. (λ xn, *)
(*                          tele_app $ tele_app $ v%V *)
(*                         ) .. ) *)
(*   ) *)
(*   (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, *)
(*    format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e @ τ ; E % c  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'") *)
(*   : bi_scope. *)

(* (* No ∀∀ binders, no RET binders *) *)
(* Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" := *)
(*   (atomic_wp (TA:=TeleO) *)
(*              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. )) *)
(*              (TP:=TeleO) *)
(*              e%E *)
(*              E *)
(*              (tele_app $ α%I) *)
(*              (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. ) *)
(*              (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) .. ) *)
(*              (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ v%V) .. ) *)
(*   ) *)
(*   (at level 20, E, β, α, v, POST at level 200, y1 binder, yn binder, *)
(*    format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'") *)
(*   : bi_scope. *)

(* (* No ∀∀ binders, no ∃∃ binders, no RET binders *) *)
(* Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" := *)
(*   (atomic_wp (TA:=TeleO) *)
(*              (TB:=TeleO) *)
(*              (TP:=TeleO) *)
(*              e%E *)
(*              E *)
(*              (tele_app $ α%I) *)
(*              (tele_app $ tele_app β%I) *)
(*              (tele_app $ tele_app $ tele_app $ Some POST%I) *)
(*              (tele_app $ tele_app $ tele_app $ v%V) *)
(*   ) *)
(*   (at level 20, E, β, α, v, POST at level 200, *)
(*    format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'") *)
(*   : bi_scope. *)

(* (* No RET binders, no POST *) *)
(* Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" := *)
(*   (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) *)
(*              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. )) *)
(*              (TP:=TeleO) *)
(*              e%E *)
(*              E *)
(*              (tele_app $ λ x1, .. (λ xn, α%I) ..) *)
(*              (tele_app $ λ x1, .. (λ xn, *)
(*                          tele_app $ λ y1, .. (λ yn, β%I) .. *)
(*                         ) .. ) *)
(*              (tele_app $ λ x1, .. (λ xn, *)
(*                          tele_app $ λ y1, .. (λ yn, tele_app None) .. *)
(*                         ) .. ) *)
(*              (tele_app $ λ x1, .. (λ xn, *)
(*                          tele_app $ λ y1, .. (λ yn, tele_app v%V) .. *)
(*                         ) .. ) *)
(*   ) *)
(*   (at level 20, E, β, α, v at level 200, x1 binder, xn binder, y1 binder, yn binder, *)
(*    format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'") *)
(*   : bi_scope. *)

(* (* No ∃∃ binders, no RET binders, no POST *) *)
(* Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" := *)
(*   (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) *)
(*              (TB:=TeleO) *)
(*              (TP:=TeleO) *)
(*              e%E *)
(*              E *)
(*              (tele_app $ λ x1, .. (λ xn, α%I) ..) *)
(*              (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. ) *)
(*              (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) .. ) *)
(*              (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) .. ) *)
(*   ) *)
(*   (at level 20, E, β, α, v at level 200, x1 binder, xn binder, *)
(*    format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'") *)
(*   : bi_scope. *)

(* (* No ∀∀ binders, no RET binders, no POST *) *)
(* Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" := *)
(*   (atomic_wp (TA:=TeleO) *)
(*              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. )) *)
(*              (TP:=TeleO) *)
(*              e%E *)
(*              E *)
(*              (tele_app α%I) *)
(*              (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. ) *)
(*              (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app None) .. ) *)
(*              (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app v%V) .. ) *)
(*   ) *)
(*   (at level 20, E, β, α, v at level 200, y1 binder, yn binder, *)
(*    format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'") *)
(*   : bi_scope. *)

(* (* No ∀∀ binders, no ∃∃ binders, no RET binders, no POST *) *)
(* Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" := *)
(*   (atomic_wp (TA:=TeleO) *)
(*              (TB:=TeleO) *)
(*              (TP:=TeleO) *)
(*              e%E *)
(*              E *)
(*              (tele_app α%I) *)
(*              (tele_app $ tele_app β%I) *)
(*              (tele_app $ tele_app $ tele_app None) *)
(*              (tele_app $ tele_app $ tele_app v%V) *)
(*   ) *)
(*   (at level 20, E, β, α, v at level 200, *)
(*    format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'") *)
(*   : bi_scope. *)

(** Theory *)
Section lemmas.
  Context
  `{IG: invGS_gen HasNoLc Σ}
  (* {Σ} *)
    (* {Σ} *)
  `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
  `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
   (Degree := ofe_car DegO)
   (Level := ofe_car LevelO)
   {LIM_STEPS}
   {OPRE: ObligationsParamsPre Degree Level LIM_STEPS}
   (OP := LocaleOP (Locale := locale heap_lang))
   {oGS: @asem_GS _ _ ObligationsASEM Σ}
    `{EM: ExecutionModel heap_lang M}
    `{hGS: @heapGS Σ _ EM}
    {TA TB TP : tele}.

  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (POST : TA → TB → TP → option iProp) (f : TA → TB → TP → val heap_lang).

  (* TODO: move *)
  Lemma wp_frame_wand s E ζ e Q Φ :
    Q -∗ WP e @ s; ζ; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; ζ; E {{ Φ }}.
  Proof.    
    iIntros "HQ HWP".
    iApply wp_wand_l. iFrame. iIntros (?) "P".
    by iApply "P". 
  Qed.

  (* Atomic triples imply sequential triples. *)
  Lemma BMU_atomic_wp_seq τ e E c α β POST f :
    BMU_atomic_wp τ e c E α β POST f (oGS := oGS) -∗
    ∀ Φ, ∀.. x, α x -∗
          (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z))
          (* (∀.. y, β x y ={Ei}=∗ ∀.. z, POST x y z -∗? Φ (f x y z)) *)

          (*         β x y ={Ei}=∗ BMU Ei c (|={Ei, E}=> Φ x y) *)
          -∗ WP e @ τ {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply (wp_frame_wand with "HΦ"). iApply "Hwp".
    BMUiAuIntro.

    iApply BMU_atomic_acc_mask_weaken.
    { apply empty_subseteq. }

    BMUiAaccIntro with "Hα".
    { eauto. }
    iIntros (y) "Hβ".
    iApply BMU_intro. iModIntro. 
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. iIntros (z) "Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_wp_seq_step e τ E c α β POST f :
    TCEq (to_val e) None →
    BMU_atomic_wp τ e E c α β POST f (oGS := oGS) -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ τ {{ Φ }}.
  Proof.
    iIntros (?) "H"; iIntros (Φ x) "Hα HΦ".
    iApply (wp_step_fupd _ _ ⊤ _ _ (∀.. y : TB, _) 
      with "[HΦ]").
    { done. }
    { iFrame. done. }
    iApply (BMU_atomic_wp_seq with "H Hα").
    iIntros "%y Hβ %z Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (* (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *) *)
  (* Lemma BMU_atomic_seq_wp_atomic τ e E c α β POST f `{!Atomic WeaklyAtomic e} : *)
  (*   (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ τ ; ∅ {{ Φ }}) -∗ *)
  (*   BMU_atomic_wp τ e c E α β POST f (oGS := oGS). *)
  (* Proof. *)
  (*   iIntros "Hwp" (Φ) "AU". *)

  (*   (* iApply (wp_mask_mono _ (⊤ ∖ E)); [set_solver| ]. *) *)
  (*   (* iApply (wp_atomic _ _ ∅).  *) *)
  (*   (* (* iApply fupd_wp. *) *) *)

  (*   (* iDestruct (BMU_aupd_aacc with "AU") as "AU". *) *)
  (*   (* rewrite /BMU_atomic_acc. *) *)
  (*   (* iClear "Hwp". *) *)
    
  (*   iMod "AU" as (x) "[Hα [_ Hclose]]". *)
  (*   iApply ("Hwp" with "Hα"). iIntros "%y Hβ %z Hpost". *)
  (*   iMod ("Hclose" with "Hβ") as "HΦ". *)
  (*   rewrite ->!tele_app_bind. iApply "HΦ". done. *)
  (* Qed. *)

  (* (** Sequential triples with a persistent precondition and no initial quantifier *)
  (* are atomic. *) *)
  (* Lemma persistent_seq_wp_atomic e E (α : [tele] → iProp) (β : [tele] → TB → iProp) *)
  (*     (POST : [tele] → TB → TP → option iProp) (f : [tele] → TB → TP → val Λ) *)
  (*     {HP : Persistent (α [tele_arg])} : *)
  (*   (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ ∀.. z, POST [tele_arg] y z -∗? Φ (f [tele_arg] y z)) -∗ WP e {{ Φ }}) -∗ *)
  (*   atomic_wp e E α β POST f. *)
  (* Proof. *)
  (*   simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_wp. *)
  (*   iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ". *)
  (*   iApply wp_fupd. iApply ("Hwp" with "Hα"). iIntros "!> %y Hβ %z Hpost". *)
  (*   iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ". *)
  (*   (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *) *)
  (*   rewrite ->!tele_app_bind. iApply "HΦ". done. *)
  (* Qed. *)

  Lemma atomic_wp_mask_weaken τ e E1 E2 c α β POST f :
    E1 ⊆ E2 → BMU_atomic_wp τ e c E1 α β POST f (oGS := oGS) -∗ BMU_atomic_wp τ e c E2 α β POST f (oGS := oGS).
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply BMU_atomic_update_mask_weaken; last done. set_solver.
  Qed.

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_wp_inv τ e c E α β POST f N I :
    ↑N ⊆ E →
    BMU_atomic_wp τ e c (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f (oGS := oGS) -∗
    inv N I -∗ BMU_atomic_wp τ e c E α β POST f (oGS := oGS).
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". BMUiAuIntro.
    iInv N as "HI".
    replace c with (0 + c) at 2 by lia. 
    iApply (BMU_aacc_aupd with "AU").
    1,2: solve_ndisj.
    iIntros (x) "Hα".
    BMUiAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]".
      iApply BMU_intro. iModIntro. 
      iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.
