From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From actris.channel Require Import proto.
From aneris.aneris_lang.lib Require Import serialization_proof.
From stdpp Require Import base tactics telescopes.
Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Section Chan_Mapsto_Resources.
  Context `{!anerisG Mdl Σ}.
  Reserved Notation  "c ↣{ ip , ser } p" (at level 20, format "c  ↣{ ip , ser }  p").

  Class Chan_mapsto_resource := {
      chan_mapsto : val → iProto Σ → ip_address → serialization → iProp Σ
      where "c ↣{ ip , ser } p" := (chan_mapsto c p ip ser);
      chan_mapsto_contractive c ip ser :> Contractive (λ p, chan_mapsto c p ip ser);
      chan_mapsto_nonExpansive c ip ser :> NonExpansive (λ p, chan_mapsto c p ip ser);
      chan_mapsto_proper c ip ser :> Proper ((≡) ==> (≡)) (λ p, chan_mapsto c p ip ser);
      chan_mapsto_le c ip ser p1 p2 : c ↣{ ip, ser } p1 -∗ ▷ (p1 ⊑ p2) -∗ c ↣{ ip, ser } p2;
      chan_mapsto_exclusive c ip ser p1 p2 : c ↣{ ip, ser } p1 -∗ c ↣{ ip, ser } p2 -∗ False;
    }.

End Chan_Mapsto_Resources.

Arguments Chan_mapsto_resource {_}.


From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.spec Require Import ras.

Section Session_Resources.
  Context `{!anerisG Mdl Σ}.

  Class SessionResources (UP : Reliable_communication_service_params) := {
      (* Resources. *)
      SrvInit : iProp Σ;
      CltCanConnect : val → socket_address → iProp Σ;
      SrvCanListen : val → iProp Σ;
      SrvListens : val → iProp Σ;
      (* Laws. *)
      (* TODO. *)
      (* CltCanConnect_exclusive skt sa : CltCanConnect skt sa -∗ CltCanConnect skt sa -∗ False; *)
      (* CltCanConnect_agree skt sa1 sa2 : CltCanConnect skt sa1 -∗ CltCanConnect skt sa2 -∗ ⌜sa1 = sa2⌝; *)
      (* SrvInit_exclusive : SrvInit -∗ SrvInit -∗ False; *)
      (* SrvCanListen_exclusive skt : SrvCanListen skt  -∗ SrvCanListen skt -∗ False; *)
      (* SrvListens_exclusive c1 : SrvListens c1 -∗ SrvListens c1 -∗ False; *)
      SrvInitTimeless :> Timeless SrvInit;
      reserved_server_socket_interp : message → iProp Σ;
    }.


End Session_Resources.


Arguments SessionResources {_ _ _}.
Notation "c ↣{ ip , ser } p" := (chan_mapsto c p ip ser) (at level 20, format "c  ↣{ ip , ser }  p").
