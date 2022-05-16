From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import serialization_proof.
From aneris.examples.reliable_communication Require Import client_server_code.

Class Reliable_communication_API :=
  {
    (* type ('a, 'b) client_skt; *)
    (* type ('a, 'b) server_skt; *)
    (* type ('a, 'b) chan_descr; *)
    (* val make_client_skt : 'a serializer -> 'b serializer -> saddr -> ('a, 'b) client_skt; *)
    make_client_skt : serializer → serializer → val;
    (* val make_server_skt : 'a serializer -> 'b serializer -> saddr -> ('a, 'b) server_skt; *)
    make_server_skt : serializer → serializer → val;
    (* val server_listen : ('a, 'b) server_skt -> unit; *)
    server_listen : val;
    (* val accept : ('a, 'b) server_skt -> ('a, 'b) chan_descr * saddr; *)
    accept : val;
    (* val connect : ('a, 'b) client_skt -> saddr -> ('a, 'b) chan_descr; *)
    connect : val;
    (* val send : ('a, 'b) chan_descr -> 'a -> unit; *)
    send : val;
    (* val try_recv : ('a, 'b) chan_descr -> 'b option; *)
    try_recv : val;
    (* val recv : ('a, 'b) chan_descr -> 'b; *)
    recv : val;
  }.


Global Instance Reliable_communication_API_instance : Reliable_communication_API :=
 {| make_client_skt := client_server_code.make_client_skt;
    make_server_skt := client_server_code.make_server_skt;
    server_listen := client_server_code.server_listen;
    accept := client_server_code.accept;
    connect := client_server_code.connect;
    send := client_server_code.send;
    try_recv := client_server_code.try_recv;
    recv := client_server_code.recv |}.
