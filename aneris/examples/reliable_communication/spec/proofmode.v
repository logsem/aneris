From trillium.prelude Require Import finitary.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.aneris_lang.lib Require Import serialization.serialization_proof lock_proof.
From actris.channel Require Import proto.
From aneris.examples.reliable_communication Require Import user_params client_server_code.
From aneris.examples.reliable_communication.spec Require Import resources api_spec.

(** * Tactics for proving contractiveness of protocols *)
Ltac f_dist_le :=
  match goal with
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end.

Ltac solve_proto_contractive :=
  solve_proper_core ltac:(fun _ =>
    first [f_contractive; simpl in * | f_equiv | f_dist_le]).

(** * Normalization of protocols *)
Class ActionDualIf (d : bool) (a1 a2 : action) :=
  dual_action_if : a2 = if d then action_dual a1 else a1.
Global Hint Mode ActionDualIf ! ! - : typeclass_instances.

Global Instance action_dual_if_false a : ActionDualIf false a a := eq_refl.
Global Instance action_dual_if_true_send : ActionDualIf true Send Recv := eq_refl.
Global Instance action_dual_if_true_recv : ActionDualIf true Recv Send := eq_refl.

Class ProtoNormalize {Σ} (d : bool) (p : iProto Σ)
    (pas : list (bool * iProto Σ)) (q : iProto Σ) :=
  proto_normalize :
    ⊢ iProto_dual_if d p <++>
        foldr (iProto_app ∘ uncurry iProto_dual_if) END%proto pas ⊑ q.
Global Hint Mode ProtoNormalize ! ! ! ! - : typeclass_instances.
Arguments ProtoNormalize {_} _ _%proto _%proto _%proto.

Notation ProtoUnfold p1 p2 := (∀ d pas q,
  ProtoNormalize d p2 pas q → ProtoNormalize d p1 pas q).

Class MsgNormalize {Σ} (d : bool) (m1 : iMsg Σ)
    (pas : list (bool * iProto Σ)) (m2 : iMsg Σ) :=
  msg_normalize a :
    ProtoNormalize d (<a> m1) pas (<(if d then action_dual a else a)> m2).
Global Hint Mode MsgNormalize ! ! ! ! - : typeclass_instances.
Arguments MsgNormalize {_} _ _%msg _%msg _%msg.


Section classes.
  Context `{!anerisG Mdl Σ, !@Chan_mapsto_resource Σ}.
  Implicit Types TT : tele.
  Implicit Types p : iProto Σ.
  Implicit Types m : iMsg Σ.
  Implicit Types P : iProp Σ.

  Lemma proto_unfold_eq p1 p2 : p1 ≡ p2 → ProtoUnfold p1 p2.
  Proof. rewrite /ProtoNormalize=> Hp d pas q. by rewrite Hp. Qed.

  Global Instance proto_normalize_done p : ProtoNormalize false p [] p | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual p :
    ProtoNormalize true p [] (iProto_dual p) | 0.
  Proof. rewrite /ProtoNormalize /= right_id. auto. Qed.
  Global Instance proto_normalize_done_dual_end :
    ProtoNormalize (Σ:=Σ) true END [] END | 0.
  Proof. rewrite /ProtoNormalize /= right_id iProto_dual_end. auto. Qed.

  Global Instance proto_normalize_dual d p pas q :
    ProtoNormalize (negb d) p pas q →
    ProtoNormalize d (iProto_dual p) pas q.
  Proof. rewrite /ProtoNormalize. by destruct d; rewrite /= ?involutive. Qed.

  Global Instance proto_normalize_app_l d p1 p2 pas q :
    ProtoNormalize d p1 ((d,p2) :: pas) q →
    ProtoNormalize d (p1 <++> p2) pas q.
  Proof.
    rewrite /ProtoNormalize /=. rewrite assoc.
    by destruct d; by rewrite /= ?iProto_dual_app.
  Qed.

  Global Instance proto_normalize_end d d' p pas q :
    ProtoNormalize d p pas q →
    ProtoNormalize d' END ((d,p) :: pas) q | 0.
  Proof.
    rewrite /ProtoNormalize /=.
    destruct d'; by rewrite /= ?iProto_dual_end left_id.
  Qed.

  Global Instance proto_normalize_app_r d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize false p1 ((d,p2) :: pas) (p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => Hp. by iApply iProto_le_app. Qed.

  Global Instance proto_normalize_app_r_dual d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize true p1 ((d,p2) :: pas) (iProto_dual p1 <++> q) | 0.
  Proof. rewrite /ProtoNormalize /= => Hp. by iApply iProto_le_app. Qed.

  Global Instance msg_normalize_base d v P p q pas :
    ProtoNormalize d p pas q →
    MsgNormalize d (MSG v {{ P }}; p) pas (MSG v {{ P }}; q).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> Hp a.
    iApply iProto_le_trans; [|by iApply iProto_le_base].
    destruct d; by rewrite /= ?iProto_dual_message ?iMsg_dual_base
      iProto_app_message iMsg_app_base.
  Qed.

  Global Instance msg_normalize_exist {A} d (m1 m2 : A → iMsg Σ) pas :
    (∀ x, MsgNormalize d (m1 x) pas (m2 x)) →
    MsgNormalize d (∃ x, m1 x) pas (∃ x, m2 x).
  Proof.
    rewrite /MsgNormalize /ProtoNormalize=> Hp a.
    destruct d, a; simpl in *; rewrite ?iProto_dual_message ?iMsg_dual_exist
      ?iProto_app_message ?iMsg_app_exist /=; iIntros (x); iExists x; first
      [move: (Hp x Send); by rewrite ?iProto_dual_message ?iProto_app_message
      |move: (Hp x Recv); by rewrite ?iProto_dual_message ?iProto_app_message].
  Qed.

  Global Instance proto_normalize_message d a1 a2 m1 m2 pas :
    ActionDualIf d a1 a2 →
    MsgNormalize d m1 pas m2 →
    ProtoNormalize d (<a1> m1) pas (<a2> m2).
  Proof. by rewrite /ActionDualIf /MsgNormalize /ProtoNormalize=> ->. Qed.

  Global Instance proto_normalize_swap {TT1 TT2} d a m m'
      (tv1 : TT1 -t> val) (tP1 : TT1 -t> iProp Σ) (tm1 : TT1 -t> iMsg Σ)
      (tv2 : TT2 -t> val) (tP2 : TT2 -t> iProp Σ)
      (tp : TT1 -t> TT2 -t> iProto Σ) pas :
    ActionDualIf d a Recv →
    MsgNormalize d m pas m' →
    MsgTele m' tv1 tP1 (tele_bind (λ.. x1, <!> tele_app tm1 x1))%proto →
    (∀.. x1, MsgTele (tele_app tm1 x1) tv2 tP2 (tele_app tp x1)) →
    ProtoNormalize d (<a> m) pas (<!.. x2> MSG tele_app tv2 x2 {{ tele_app tP2 x2 }};
                                  <?.. x1> MSG tele_app tv1 x1 {{ tele_app tP1 x1 }};
                                  tele_app (tele_app tp x1) x2) | 1.
  Proof.
    rewrite /ActionDualIf /MsgNormalize /ProtoNormalize /MsgTele.
    rewrite tforall_forall=> Ha Hm Hm' Hm''.
    iApply iProto_le_trans; [iApply Hm|]. rewrite Hm' -Ha. clear Ha Hm Hm'.
    iApply iProto_le_texist_elim_l; iIntros (x1).
    iApply iProto_le_texist_elim_r; iIntros (x2).
    rewrite !tele_app_bind Hm'' {Hm''}.
    iApply iProto_le_trans;
      [iApply iProto_le_base; iApply (iProto_le_texist_intro_l _ x2)|].
    iApply iProto_le_trans;
      [|iApply iProto_le_base; iApply (iProto_le_texist_intro_r _ x1)]; simpl.
    iApply iProto_le_base_swap.
  Qed.

  (** Automatically perform normalization of protocols in the proof mode when
  using [iAssumption] and [iFrame]. *)
  Global Instance mapsto_proto_from_assumption ip q c p1 p2 ser :
    ProtoNormalize false p1 [] p2 →
    FromAssumption q (c ↣{ip, ser } p1) (c ↣{ip, ser } p2).
  Proof.
    rewrite /FromAssumption /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "H". by iApply (chan_mapsto_le with "H").
  Qed.
  Global Instance mapsto_proto_from_frame ip q c p1 p2 ser:
    ProtoNormalize false p1 [] p2 →
    Frame q (c ↣{ip, ser} p1) (c ↣{ip, ser } p2) True.
  Proof.
    rewrite /Frame /ProtoNormalize /= right_id.
    rewrite bi.intuitionistically_if_elim.
    iIntros (?) "[H _]". by iApply (chan_mapsto_le with "H").
  Qed.
End classes.

(** * Symbolic execution tactics *)
(* TODO: Maybe strip laters from other hypotheses in the future? *)

Lemma tac_wp_recv
      `{ !anerisG Mdl Σ,
         !lockG Σ}
       (chn : @Chan_mapsto_resource Σ)
      `{ Reliable_communication_Specified_API_session }
      {TT : tele} Δ i j K ip ser c p m tv tP tP' tp Φ :
  envs_lookup i Δ = Some (false, c ↣{ip, ser} p)%I →
  ProtoNormalize false p [] (<?> m) →
  MsgTele m tv tP tp →
  (* SerializerOf serzer sertion → *)
  (∀.. x, MaybeIntoLaterN false 1 (tele_app tP x) (tele_app tP' x)) →
  let Δ' := envs_delete false i false Δ in
  (∀.. x : TT,
         match envs_app false
                        (Esnoc (Esnoc Enil j (tele_app tP' x)) i (c ↣{ip, ser} tele_app tp x)) Δ' with
         | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (tele_app tv x)) @[ip] {{ Φ }})
         | None => False
         end) →
  envs_entails Δ (WP fill K (recv c) @[ip] {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /MsgTele /MaybeIntoLaterN /=.
  rewrite !tforall_forall right_id.
  intros ? Hp Hm HP HΦ. rewrite envs_lookup_sound //; simpl.
  assert (c ↣{ip, ser} p ⊢ c ↣{ip, ser} <?.. x>
           MSG tele_app tv x {{ ▷ tele_app tP' x }}; tele_app tp x)%proto as ->.
  { iIntros "Hc". iApply (chan_mapsto_le with "Hc"). iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|rewrite Hm].
    iApply iProto_le_texist_elim_l; iIntros (x).
    iApply iProto_le_trans; [|iApply (iProto_le_texist_intro_r _ x)]; simpl.
    iIntros "H". by iDestruct (HP with "H") as "$". }
  rewrite -aneris_wp_bind.
  eapply bi.wand_apply;
    [by iApply (RCSpec_recv_spec _ c (tele_app tv) (tele_app tP') (tele_app tp) ip)|f_equiv; first done].
  rewrite -bi.later_intro; apply bi.forall_intro=> x.
  specialize (HΦ x). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΦ.
Qed.

Tactic Notation "wp_recv_core" tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣{_, _} _)%I) => c end in
    iAssumptionCore || fail "wp_recv: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (aneris_wp ?ip ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_recv _ _ _ Hnew K))
      |fail 1 "wp_recv: cannot find 'recv' in" e];
    [solve_mapsto ()
       |iSolveTC || fail 1 "wp_recv: protocol not of the shape <?>"
    |iSolveTC || fail 1 "wp_recv: cannot convert to telescope"
    |iSolveTC
    |pm_reduce; simpl; tac_intros;
     tac Hnew;
     wp_finish]
  | _ => fail "wp_recv: not a 'wp'"
  end.

Tactic Notation "wp_recv" "as" constr(pat) :=
  wp_recv_core (idtac) as (fun H => iDestructHyp H as pat).

Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "wp_recv" "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Tactic Notation "wp_recv_core_chan" constr(H) tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣{_, _} _)%I) => c end in
    iAssumptionCore || fail "wp_recv: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (aneris_wp ?ip ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_recv H _ _ Hnew K))
      |fail 1 "wp_recv: cannot find 'recv' in" e];
    [solve_mapsto ()
       |iSolveTC || fail 1 "wp_recv: protocol not of the shape <?>"
    |iSolveTC || fail 1 "wp_recv: cannot convert to telescope"
    |iSolveTC
    |pm_reduce; simpl; tac_intros;
     tac Hnew;
     wp_finish]
  | _ => fail "wp_recv: not a 'wp'"
  end.

Tactic Notation "wp_recv_chan" constr(chn) "as" constr(pat) :=
  wp_recv_core_chan (chn) (idtac) as (fun H => iDestructHyp H as pat).

Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "wp_recv_chan" constr(chn) "(" simple_intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_recv_core_chan (chn) (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).


Lemma tac_wp_send
      `{ !anerisG Mdl Σ,
         !lockG Σ}
        (chn : @Chan_mapsto_resource Σ)
        `{ @Reliable_communication_Specified_API_session _ _ _ chn }
  (* add `{!ChannelTokens}. TODO: add later when stated w.r.t. the API. *)
      {TT : tele} Δ neg i js K ip ser c v p m tv tP tp Φ :
  envs_lookup i Δ = Some (false, c ↣{ip, ser} p)%I →
  ProtoNormalize false p [] (<!> m) →
  MsgTele m tv tP tp →
  Serializable ser v →
  let Δ' := envs_delete false i false Δ in
  (∃.. x : TT,
    match envs_split (if neg is true then base.Right else base.Left) js Δ' with
    | Some (Δ1,Δ2) =>
       match envs_app false (Esnoc Enil i (c ↣{ip, ser} tele_app tp x)) Δ2 with
       | Some Δ2' =>
          v = tele_app tv x ∧
          envs_entails Δ1 (tele_app tP x) ∧
          envs_entails Δ2' (WP fill K (of_val #()) @[ip] {{ Φ }})
       | None => False
       end
    | None => False
    end) →
  envs_entails Δ (WP fill K (send c v) @[ip] {{ Φ }}).
Proof.
  rewrite envs_entails_unseal /ProtoNormalize /MsgTele /= right_id texist_exist.
  intros ? Hp Hm Hser [x HΦ].
  rewrite (envs_lookup_sound _ i) //; simpl.
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_split_sound //. rewrite (envs_app_sound Δ2) //; simpl.
  destruct HΦ as (-> & -> & ->). rewrite right_id assoc.
  assert (c ↣{ip, ser} p ⊢
    c ↣{ip,ser} <!.. (x : TT)> MSG tele_app tv x {{ tele_app tP x }}; tele_app tp x)%proto as ->.
  { iIntros "Hc". iApply (chan_mapsto_le with "Hc"); iIntros "!>".
    iApply iProto_le_trans; [iApply Hp|]. by rewrite Hm. }
  eapply bi.wand_apply.
  { rewrite -aneris_wp_bind. iApply RCSpec_send_spec_tele. }
  rewrite -bi.later_intro. iFrame.
  iIntros "((Hc & Hc') & HΦ)".
  iFrame "#∗". iFrame. done.
Qed.

(* TODO: Handle mismatched values better *)
Tactic Notation "wp_send_core" tactic3(tac_exist) "with" constr(pat) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣{_,_} _)%I) => c end in
    iAssumptionCore || fail "wp_send: cannot find" c "↣ ? @ ?" in
  let solve_serializer _ :=
    let c := match goal with |- _ = Serializable ?c ?v => c end in
    iAssumptionCore || fail "wp_send: cannot solve serializer" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_send: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (aneris_wp ?ip ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ _ neg _ Hs' K))
         |fail 1 "wp_send: cannot find 'send' in" e];
       [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <!>"
       |iSolveTC || fail 1 "wp_send: cannot convert to telescope"
       (* |try solve_serializer ()  *)
       (* |iSolveTC || fail 1 "wp_send: serializer does not match" *)
       |try (simplify_eq; iSolveTC)            (* Serializer happens here *)
       |pm_reduce; simpl; tac_exist;
        repeat lazymatch goal with
        | |- ∃ _, _ => eexists _
        end;
        lazymatch goal with
        | |- False => fail "wp_send:" Hs' "not found"
        | _ => notypeclasses refine (conj _ (conj _ _));
                [try (reflexivity); by simplify_eq /=
                |iFrame Hs_frame; solve_done d
                |wp_finish]
        end || fail 1 "wp_send: value type mismatch (likely)"]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_send" "with" constr(pat) :=
  wp_send_core (idtac) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) ")" "with" constr(pat) :=
  wp_send_core (eexists x1) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) ")"
    "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4)
    uconstr(x5) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) uconstr(x8) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7; eexists x8) with pat.


(* TODO: Handle mismatched values better *)
Tactic Notation "wp_send_core_chan" constr(H) tactic3(tac_exist) "with" constr(pat) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣{_,_} _)%I) => c end in
    iAssumptionCore || fail "wp_send: cannot find" c "↣ ? @ ?" in
  let solve_serializer _ :=
    let c := match goal with |- _ = Serializable ?c ?v => c end in
    iAssumptionCore || fail "wp_send: cannot solve serializer" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_send: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (aneris_wp ?ip ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_send H _ neg _ Hs' K))
         |fail 1 "wp_send: cannot find 'send' in" e];
       [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <!>"
       |iSolveTC || fail 1 "wp_send: cannot convert to telescope"
       (* |try solve_serializer ()  *)
       (* |iSolveTC || fail 1 "wp_send: serializer does not match" *)
       |try (simplify_eq; iSolveTC)            (* Serializer happens here *)
       |pm_reduce; simpl; tac_exist;
        repeat lazymatch goal with
        | |- ∃ _, _ => eexists _
        end;
        lazymatch goal with
        | |- False => fail "wp_send:" Hs' "not found"
        | _ => notypeclasses refine (conj _ (conj _ _));
                [try (reflexivity); by simplify_eq /=
                |iFrame Hs_frame; solve_done d
                |wp_finish]
        end || fail 1 "wp_send: value type mismatch (likely)"]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_send_chan" constr(chn) "with" constr(pat) :=
  wp_send_core_chan (chn) (idtac) with pat.

Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) ")" "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1) with pat.
Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) uconstr(x2) ")" "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1; eexists x2) with pat.
Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) uconstr(x2) uconstr(x3) ")"
    "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1; eexists x2; eexists x3) with pat.
Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1; eexists x2; eexists x3; eexists x4) with pat.
Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4)
    uconstr(x5) ")" "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5) with pat.
Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) ")" "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6) with pat.
Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) ")" "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7) with pat.
Tactic Notation "wp_send_chan" constr(chn) "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) uconstr(x8) ")" "with" constr(pat) :=
  wp_send_core_chan (chn) (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7; eexists x8) with pat.

Definition int_client v : val :=
  λ: "c", send "c" v;; recv "c".

Section test.
  Context `{ !anerisG Mdl Σ,
         !lockG Σ,
         !@Chan_mapsto_resource Σ,
         !Reliable_communication_Specified_API_session _}.


  Definition int_proto : iProto Σ :=
     (<! (x:Z)> MSG #x ; <?> MSG #(x+2) ; END)%proto.

  Lemma int_client_spec ip v c :
    v = #40 →
    {{{ c ↣{ip, int_serialization} int_proto }}}
      int_client v c @[ip]
    {{{ RET #42; True }}}.
  Proof.
    iIntros (Heq Φ) "Hc HΦ".
    wp_lam.
    wp_send with "[//]".
    wp_recv_chan H as "_".
    by iApply "HΦ".
  Qed.

End test.

Definition int_bool_client : val :=
  λ: "c", send "c" (InjLV (#40));; recv "c".

Definition is_zero (x:Z) : bool :=
  match x with
  | Z0 => true
  | _ => false
  end.

Section test.
  Context
    `{ !anerisG Mdl Σ,
       !lockG Σ,
       !@Chan_mapsto_resource Σ,
       !Reliable_communication_Specified_API_session _ }.

  Definition int_bool_sertion :=
    sum_serialization int_serialization bool_serialization.

  Definition int_bool_proto : iProto Σ :=
     (<! (x:Z)> MSG InjLV #(x) ; <?> MSG InjRV #(is_zero x) ; END)%proto.

  Lemma int_bool_client_spec ip c :
    {{{ c ↣{ip, int_bool_sertion} int_bool_proto  }}}
      int_bool_client c @[ip]
    {{{ RET InjRV #false; True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_lam.
    wp_send with "[//]".
    wp_pures. wp_recv as "_".
    by iApply "HΦ".
  Qed.

End test.

Definition int_client_two_channels v : val :=
  λ: "c1" "c2", send "c1" v;; recv "c1";;  send "c2" v;; recv "c2".

Section test.
  Context `{ !anerisG Mdl Σ,
         !lockG Σ,
         !@Chan_mapsto_resource Σ,
         !Reliable_communication_Specified_API_session _}.


  Definition int_proto2 : iProto Σ :=
     (<! (x:Z)> MSG #x ; <?> MSG #(x+2) ; END)%proto.

  Lemma int_client_two_channels_spec ip v c1 c2 :
    v = #40 →
    {{{ c1 ↣{ip, int_serialization} int_proto2 ∗
        c2 ↣{ip, int_serialization} int_proto2 }}}
      int_client_two_channels v c1 c2 @[ip]
    {{{ RET #42; True }}}.
  Proof.
    iIntros (Heq Φ) "(Hc1 & Hc2) HΦ".
    wp_lam.
    wp_send with "[//]".
    wp_recv as "_".
    wp_send with "[//]".
    wp_recv as "_".
    by iApply "HΦ".
  Qed.

End test.


(* Definition int_client_two_channels_two_instances *)
(*            v : val := *)
(*   λ: "c1" "c2",  (send) "c1" v;; (recv) "c1";; (send) "c2" v;; (recv) "c2". *)


(* Section test. *)
(*   Context `{ !anerisG Mdl Σ, *)
(*              !lockG Σ, *)
(*              x: @Chan_mapsto_resource Σ, *)
(*              y : @Chan_mapsto_resource Σ}. *)
(*   Context `{ *)
(*         !Reliable_communication_Specified_API_session x, *)
(*       !Reliable_communication_Specified_API_session y}. *)

(*   Lemma int_client_two_channels_spec_two_instances ip v c1 c2 : *)
(*     v = #40 → *)
(*     {{{ c1 ↣{ip, int_serialization} int_proto2 ∗ *)
(*         c2 ↣{ip, int_serialization} int_proto2 }}} *)
(*       int_client_two_channels_two_instances  v c1 c2 @[ip] *)
(*     {{{ RET #42; True }}}. *)
(*   Proof. *)
(*     Set Printing Implicit. *)
(*     iIntros (Heq Φ) "(Hc1 & Hc2) HΦ". *)
(*     wp_lam. *)
(*     wp_pures. *)
(*     wp_send with "[//]". *)
(*     wp_recv  as "_". *)
(*     wp_pures. *)
(*     wp_send with "[//]". *)
(*     wp_recv as "_". *)
(*     by iApply "HΦ". *)
(*   Qed. *)

(* End test. *)
