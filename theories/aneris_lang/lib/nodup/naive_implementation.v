From stdpp Require Export strings list pretty gmap.
From aneris.prelude Require Import quantifiers.
From aneris.aneris_lang Require Import lang network notation tactics proofmode.
From aneris.aneris_lang.lib Require Import
     network_util map lock util list serialization assert.

(* An naive implementation for at-most-once (amo) receive operation. *)
Import Network.

(* TODO: move to the list.v and prove spec. *)
Definition list_mem : base_lang.val :=
  (rec: "find" "x" "l" :=
     match: "l" with
       SOME "a" =>
       let: "head" := Fst "a" in
       let: "tail" := Snd "a" in
       if: "x" = "head" then #true
       else "find" "x" "tail"
     | NONE => #false
      end).

Definition amo_receivefrom : base_lang.val :=
  λ: "rmap" "lk" "sh" <>,
     match: ReceiveFrom "sh" with
       NONE => NONEV
     | SOME "m" =>
       let: "mb" := Fst "m" in
       let: "src" := Snd "m" in
       acquire "lk";;
       let: "res" :=
          match: (map_lookup "src" !"rmap") with
            NONE => "rmap" <- map.map_insert "src" ("mb" :: []) !"rmap" ;;
                   SOME "m"
          | SOME "l" =>
            if: list_mem "mb" "l" then NONEV
            else
              ("rmap" <- map.map_insert "src" ("mb" :: "l") !"rmap" ;; SOME "m")
          end in
       release "lk";; "res"
     end.

Definition amo_install : base_lang.val :=
  λ: "sh",
  let: "rmap" := ref (map.map_empty #()) in
  let: "lk" := newlock #() in
  amo_receivefrom "rmap" "lk" "sh".


Section Proof_of_amo.
  Context `{!anerisG Mdl Σ, !lockG Σ} (N : namespace).

  (* TODO: review and improve this, maybe factor out some definitions. *)
  Definition amo_inv_def (ip: ip_address) (l : loc) (R : gset message) :=
    (∃ (vm: base_lang.val)
      (rmap : gmap socket_address (list string))
      (rmapv : gmap socket_address base_lang.val),
        l ↦[ip] vm ∗ ⌜is_map (λ (a: socket_address), #a) vm rmapv⌝ ∗
        ⌜∀ a sl, rmap !! a = Some sl →
           ∃ vl, rmapv !! a = Some vl ∧
             is_list (map (λ (s : string), #s) sl) vl ∧
             list_to_set sl = gset_map (λ m, m_body m) (messages_sent_from a R) ∧
             NoDup sl⌝)%I.

  Definition amo_inv
             (M : loc) (lk : base_lang.val) (γl : gname) (ip : ip_address)
             (R : gset message) : iProp Σ :=
  is_lock N ip γl lk (amo_inv_def ip M R).

 (* TODO: review and improve this. *)
 Lemma amo_receivefrom_spec (ip : ip_address) a E E' h s R T φ r lk γl P Q :
   let ip := ip_of_address a in
     saddress s = Some a →
     (* TODO: be sure that this does not depend on
        whether sblock s = true or false. *)
    □ (P ={E, E'}=∗
            h ↪[ip] s ∗ a ⤳ (R, T) ∗
           (h ↪[ip] s ∗ a ⤳ (R, T) ={E', E}=∗ P) ∧
      (∀ m, h ↪[ip] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ ⌜m ∉ R⌝ ∗ φ m ={E',E}=∗ Q R T m)) -∗
  {{{ P ∗ a ⤇ φ ∗ amo_inv r lk γl ip R }}}
  amo_receivefrom #r lk (Val $ LitV $ LitSocket h) #() @[ip] E
    {{{ res, RET res;
        (⌜res = NONEV⌝ ∗ P) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜res = SOMEV (PairV (LitV $ LitString (m_body msg))
                       (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          (⌜msg ∉ R⌝ ∗ Q R T msg)
    }}}.
 Proof. Admitted.

(* TODO : state a specification for amo_install in such a way that
   the implementaiton details (lock, rmap) are hidden from the user. *)

End Proof_of_amo.
