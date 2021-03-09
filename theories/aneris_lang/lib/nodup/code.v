From stdpp Require Export strings list pretty gmap.
From aneris.prelude Require Import quantifiers.
From aneris.aneris_lang Require Import lang network notation tactics proofmode.
From aneris.aneris_lang.lib Require Import
     map lock util list serialization assert.

(* An implementation sketch for at-most-once (amo) send and receive operations.

The idea of the implementation below is as follows:
 given a socket handler `sh` that has been already bound to some socket address,
 a call to `amo_install sh`

 - installs two mappings
 `tmap` : socket_address -> list nat
 `rmap` : socket_address -> list nat

 where `tmap` maps to each destination address a list of
 unique identifiers assigned to messages sent to that destination address,
 and `rmap` maps to each sender address a list of
 unique identifiers assigned to messages received from that sender address.

 - returns three operations:

 `amo_receivefrom` : unit -> option (string * socket_address)
 `amo_sendto` : string -> socket_address -> int * int
 `amo_resendto` : string -> int -> socket_address -> int

 where `amo_receivefrom ()` returns (Some (message_body, sender_addr))
 if and only if an underlying call to receiveFrom returned a message
 that is labelled with an identifier that has does not belong to the
 the mapping (rmap sender_addr);
 where `amo_sendto dst m` assigns to the string m a fresh identifier,
 which is added to the mapping `tmap dst`, sends the corresponding
 labelled message and returns the identifier together with the length
 of the string passed as argument;
 and where `amo_resendto dst m id` resends the message m only if
 the number id corresponds indeed to an identifier that has been returned
 by some preceeding `amo_sendto` call.

 Note that the identifiers of received messages are completely hidden from the
 user. However, the identifiers of sent messages are not completely carried
 away. This is because we need to allow resending the same message "for free",
 i.e. without requiring to satisfy the socket protocol of the destination.
 If we would resend a message with an arbitrary (but already existing) identifier
 that could lead to a situation where the first sent copy has not been received
 by the destination address, but the resending copies will be discarded,
 if they carry identifiers of some other messages that have been already
 received, so that a message actually will never arrive to the destination.
 Consequently, we reveail to the user the unique identifier for each sent
 message, so that user can reuse that same identifier for resending copies.

 Finally, note that all operations are non-atomic, and that the access to the
 each of `rmap` and `tmap` mappings is protected by a corresponding lock, to
 ensure that receive and sent messages identifiers are assigned uniquely. *)

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
  λ: "rmap" "rlock" "sh" <>,
     let: "m" := ReceiveFrom "sh" in
     let: "mb" := Fst "m" in
     let: "src" := Snd "m" in
     let: "i" :=
        match: FindFrom "mb" #0 #"_" with
          NONE => assert: #false
        | SOME "i" => "i"
        end in
     let: "cpt" := unSOME (s2i (Substring "mb" #0 "i")) in
     let: "msg" := Substring "mb" ("i" + #1) (strlen "mb" - ("i" + #1)) in
     acquire "rlock";;
     let: "ret" :=
        match: (map_lookup "src" !"rmap") with
           NONE =>
           "rmap" <- map.map_insert "src" ("cpt" :: []) !"rmap" ;;
            InjR ("msg", "src")
         | SOME "l" =>
           if: list_mem "cpt" "l" then NONEV
           else
             let: "hd" := Fst "l" in
             let: "tl" := Snd "l" in
             "rmap" <- map.map_insert "src" ("cpt" :: "tl") !"rmap" ;;
             InjR ("msg", "src")
         end in
     release "rlock";;
     "ret".

Definition amo_sendto : base_lang.val :=
  λ: "tmap" "tlock" "sh" "m" "dst",
    acquire "tlock";;
    let: "id_msg" :=
       match: (map_lookup "dst" !"tmap") with
         NONE =>
         "tmap" <- map.map_insert "dst" (#1 :: []) !"tmap" ;;
          (#1, (int_ser #1) ^^ #"_" ^^ "m")
       | SOME "l" =>
         let: "hd" := Fst "l" in
         let: "tl" := Snd "l" in
         let: "id" := "hd" + #1 in
         "tmap" <- map.map_insert "dst" ("id" :: "tl") !"tmap" ;;
          ("id", (int_ser "id") ^^ #"_" ^^ "m")
        end in
    release "tlock";;
    SendTo "sh" (Snd "id_msg") "dst";;
   ("id", strlen "m").

Definition amo_resendto : base_lang.val :=
  λ: "tmap" "tlock" "sh" "m" "id" "dst",
    acquire "tlock";;
    let: "msg" :=
       match: (map_lookup "dst" !"tmap") with
         NONE => assert: #false
       | SOME "l" =>
         if: list_mem "id" "l" then assert: #false
         else (int_ser "id") ^^ #"_" ^^ "m"
       end in
    release "tlock";;
    SendTo "sh" "msg" "dst";;
    strlen "m".

Definition amo_install : base_lang.val :=
  λ: "sh",
  let: "rmap" := ref (map.map_empty #()) in
  let: "tmap" := ref (map.map_empty #()) in
  let: "rlock" := newlock #() in
  let: "tlock" := newlock #() in
  (amo_receivefrom "rmap" "rlock" "sh",
   amo_sendto "tmap" "tlock" "sh",
   amo_resendto "tmap" "tlock" "sh").
