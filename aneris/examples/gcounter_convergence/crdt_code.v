From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib Require Import list_code network_util_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_code.

Section code.

  Definition mk_udp_socket : val :=
  (λ: <>, NewSocket #PF_INET
                    #SOCK_DGRAM
                    #IPPROTO_UDP)%V.

  Definition gcounter_merge : val :=
    rec: "merge" "m1" "m2" :=
      match: "m1" with
        NONE => match: "m2" with SOME "p" => assert: #false | NONE => NONE end
      | SOME "p1" =>
        match: "m2" with
          NONE => assert: #false
        | SOME "p2" =>
          let: "t1" := Snd "p1" in
          let: "t2" := Snd "p2" in
          let: "h1" := (Fst "p1") in
          let: "h2" := (Fst "p2") in
          let: "rs" := if: "h1" ≤ "h2" then "h2" else "h1" in
          let: "tl" := "merge" "t1" "t2" in
          (list_cons "rs" "tl")
        end
      end.

  Definition perform_merge : val :=
    rec: "pm" "M" "m2" :=
      let: "tmp" := !"M" in
      if: CAS "M" "tmp" (gcounter_merge "tmp" "m2") then
        #()
      else
        "pm" "M" "m2".


  Definition gcounter_apply : val :=
    λ: "M" "sh",
    letrec: "loop" <> :=
      let: "msg" := unSOME (ReceiveFrom "sh") in
      let: "m2" := vect_deserialize (Fst "msg") in
      perform_merge "M" "m2";;
     "loop"#()
    in "loop" #().

  (* TODO: for extraction puroposes,
     add as a primitive to the language. *)
  Definition sleep : val := λ: "n" "m", #().

  (* TODO: move later to network_helpers *)
  Definition sendToAll : val :=
    λ: "sh" "msg" "dstl" "i",
    letrec: "send" "j" :=
      if: "j" < list_length "dstl" then
        if: "i" = "j" then
          "send" ("j" + #1)
        else
          let: "dst" := unSOME (list_nth "dstl" "j") in
          SendTo "sh" "msg" "dst";;
          "send" ("j" + #1)
      else #()
      in "send" #0.

  Definition gcounter_broadcast : val :=
    λ: "M" "sh" "nodes" "i",
    letrec: "loop" <> :=
      sleep #2 #0 ;;
      let: "m" := !"M" in
      let: "msg" := vect_serialize "m" in
      sendToAll "sh" "msg" "nodes" "i";;
      "loop" #()
    in "loop" #().

 Definition gcounter_incr : val :=
   λ: "M" "i",
     rec: "incr" <> :=
     let: "tmp" := !"M" in
     if: CAS "M" "tmp" (vect_inc "tmp" "i") then #() else "incr" #().

  Definition gcounter_sum : val :=
     rec: "sum" "m" :=
      match: "m" with
        SOME "a" =>
        let: "n" := Fst "a" in
        let: "t" := Snd "a" in
        "n" + ("sum" "t")
      | NONE => #0
      end.

  Definition gcounter_query : val := λ: "M" <>, gcounter_sum !"M".

  Definition gcounter_install (name : string) : val :=
    λ: "addrlst" "i",
      let: "len" := list_length "addrlst" in
      let: "M" := ref<<name>> (vect_make "len" #0) in
      let: "addr" := unSOME (list_nth "addrlst" "i") in
      let: "sh" := mk_udp_socket #() in
      SocketBind "sh" "addr";;
      Fork (gcounter_apply "M" "sh");;
      Fork (gcounter_broadcast "M" "sh" "addrlst" "i");;
      (gcounter_query "M", gcounter_incr "M" "i").

End code.
