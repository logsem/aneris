# Two phase commit

## Overview

In this example, we implement the two phase commit protocol and show safety as well as that the implementation refines an abstract model.

The model follows the [transactional commit TLA+ specification](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TCommit.tla) originally developed as part of the [Consensus on Transaction Commit](https://www.microsoft.com/en-us/research/uploads/prod/2004/01/twophase-revised.pdf) paper.

The system consists of a central *transaction manager* (coordinator) and several *resource managers* (participants in the protocol) who either want to commit or abort a transaction.


## Contents

The code and proof are separated into the following files:

- [two_phase_code.ml](../../../ml_sources/examples/transaction_commit/two_phase_code.ml) and [two_phase_code](two_phase_code.v): The OCaml implementation of the protocol and the generated AnerisLang code
- [gen_mono_heap:](gen_mono_heap.v) defines the resource algebra used to track the model state
- [tc_model:](tc_model.v) defines a model of the global state of the protocol
  - Proves a consistency theorem for the model (there cannot be resource managers in commit and abort state at the same time)
- [two_phase_prelude:](two_phase_prelude.v) defines
  - the local state transition relation for the resource managers
  - the invariant which links the model state to the local states of the resource managers
- [two_phase_tm:](two_phase_tm.v) specification for the transaction manager
- [two_phase_rm:](two_phase_rm.v) specification for the resource managers
- [two_phase_runner_code](two_phase_runner_code.v) and [two_phase_runner_proof:](two_phase_runner_proof.v) execution of an example with a transaction manager and three resource managers and the corresponding specification
- [two_phase_adequacy:](two_phase_adequacy.v)
  - Safety theorem for the two phase commit protocol
  - Proof that the implementation refines the model (simulation)
  - Proof that the consistency theorem for the model also holds for the simulation (corollary of model correctness and simulation)
