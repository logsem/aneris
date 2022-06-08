From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import inject list_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.

Class DL_params := {
    DL_server_addr : socket_address;
    DL_namespace : namespace;
 }.
