From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import network lang resources events.
From aneris.prelude Require Import gset_map time.
From aneris.aneris_lang.state_interp Require Import state_interp.
From aneris.aneris_lang Require Import network resources proofmode adequacy.
From aneris.aneris_lang.lib Require Import inject list_proof vector_clock_proof.
From aneris.examples.gcounter_convergence Require Import
     crdt_model crdt_resources crdt_proof crdt_adequacy crdt_main_rel crdt_runner
     crdt_convergence_lemmas_defs.
From trillium.traces Require Import trace_properties.

Section crdt_convergence.

  (* We assume we are given parameters for network: *)
  (* socket addresses of all crdt nodes and basic facts about them, i.e., *)
  (* io_addresses of sockets are different and that none of the nodes is the "system" node. *)
  Context {gcdata : GCData}.
  (* We assume we are given a cliet for the crdt library to run on each node. *)
  (* These clients get the interface of the library so they can increment and query the counter. *)
  (* These are arbitrary client programs which can also have independent access to the network. *)
  (* We only assume that these clients are verified against the speces of the crdt library, i.e., *)
  (* we assume that have a WP for each client. *)
  (* We have already proven in [crdt_adequacy.v] file that running these clients is safe, i.e., *)
  (* the system will not crash. Here, we show that the system also has eventual consistency. *)
  Context (ps : programs_using_gcounters gcdata).

  Definition initial_state :=
    ([mkExpr "system" (runner gcdata 0 (progs ps) $(gcd_addr_list gcdata))],
     init_state).

  (** The system is eventully consistent if whenever network fairness hodls and there is a *)
  (** stability point in the system, there also is a convergence point. *)
  Theorem gcounters_eventually_consistent iex :
    1 < GClen gcdata →
    valid_inf_exec {tr[initial_state]} iex →
    @network_fairness_always_sending gcdata {tr[initial_state]} iex →
    @network_fairness_always_receiving gcdata {tr[initial_state]} iex →
    @network_sent_received_fairness gcdata {tr[initial_state]} iex →
    ∃ locs imtr,
      length locs = GClen gcdata ∧
      eventually2
        (closed_model_relation gcdata locs)
        {tr[initial_state]} {tr[initial_crdt_state (GClen gcdata)]} iex imtr ∧
      ∀ vc,
         eventually (stability_reached locs vc) {tr[initial_state]} iex →
         eventually (@convergence_point_reached gcdata locs vc) {tr[initial_state]} iex.
  Proof.
    intros Hnnodes Hvl Hnfas Hnfar Hnfsr.
    pose proof (gcounter_adequacy gcdata ps) as Hcsim.
    eapply crdt_main_rel_always_ternary in Hcsim as [imtr Himtr]; last eassumption.
    apply eventually_sent_eventually_locs_resolved in Himtr as (locs & Hlocslen & Hcmr);
      [|by apply network_fairness_always_sending_eventually_sends|done].
    exists locs, imtr; split_and!; [done|done|].
    intros vc Hvc.
    eapply closed_model_relation_convergence_point_transfer; first eassumption.
    apply eventually_consistent.
    - eapply closed_model_relation_valid_model_trace; eassumption.
    - eapply closed_model_relation_network_fair_fair_model; eassumption.
    - eapply closed_model_relation_stability_point_transfer; eassumption.
  Qed.

End crdt_convergence.
