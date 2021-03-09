From aneris.aneris_lang Require Import lang tactics proofmode notation.
From aneris.aneris_lang.lib Require Import assert list.
Set Default Proof Using "Type".

Definition unSOME : base_lang.val :=
  λ: "p",
  match: "p" with NONE => assert #false | SOME "p'" => "p'" end.

(* Definition receivefrom_all : base_lang.val := *)
(*   λ: "socket" "nodes", *)
(*   let: "ms" := ref (Map.empty #()) in *)
(*   (rec: "loop" <> := *)
(*      let: "msg" := unSOME (ReceiveFrom "socket") in *)
(*      let: "m" := Fst "msg" in *)
(*      let: "sender" := Snd "msg" in *)
(*      "ms" <- Map.insert "sender" "m" !"ms" *)

(*   ) #();; *)
(*   !"ms".  *)

  (* list_iter (λ "n", *)
  (*            let: "msg" := unSOME (ReceiveFrom "socket") in *)
    (*            let: "m" := Fst "msg" in *)
    (*            let: "sender" := Snd "msg" in *)
    (*            if: "sender" = "n" then *)
    (*              let "ms'" := !"ms" in *)
    (*              "ms" <- list_cons "m" "ms'" *)


Import Network.
Import String.
Import uPred.


Section library.
  Context `{dG : anerisG Mdl Σ}.

  Lemma wp_unSOME ip v v' :
    {{{ ⌜v = SOMEV v'⌝ }}} unSOME (Val v) @[ip] {{{ RET v'; True }}}.
  Proof.
    iIntros (Φ ->) "HΦ".
    wp_lam. wp_match. by iApply "HΦ".
  Qed.

  (* Context (m : gmap socket_address val). *)

  (* Check (map_fold (λ i x, x) m).  *)

  (* Lemma receivefrom_all_spec f (nodes : list socket_address) ns h s a R T : *)
  (*   let ip := ip_of_address a in *)
  (*   {{{ [∗ list] n ∈ nodes, n ⤇ f n *)
  (*       ∗ ⌜List.is_List (map (LitV ∘ LitSocketAddress) nodes) ns⌝ *)
  (*       ∗ h ↪[ip] s *)
  (*       ∗ a ⤳ (R, T) }}} *)
  (*     receivefrom_all #(LitSocket h) ns @[ip] *)
  (*   {{{ vs m, RET vs;  *)
  (*       ⌜Map.is_Map vs (map m⌝ *)

  (*       (* ∗ [∗ map] n↦v ∈ m, n ⤇ f n *) *)
  (*       (* ∗ h ↪[ip_of_address a] s *) *)
  (*       (* ∗ a ⤳ (R, T) *) }}}. *)

End library.
