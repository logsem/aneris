# Artifact for the Lawyer paper

This artifact provides the reproducible technical development for the *Lawyer: Modular Obligations-Based Liveness Reasoning in Higher-Order Impredicative Concurrent Separation Logic* accepted to OOPSLA'26.

It consists of:

- Rocq formalization of all the results in the paper, located in `lawyer_suppl.zip`.
- Two virtual machines (LUbuntu based on Ubuntu 24.04 for Virtualbox and Qemu) with pre-built formalization.
  Username/password: `lawyer`.
  All relevant files are located in `/home/lawyer/artifact`.
- Full version of the paper with appendix.

This manual incorporates (a slightly edited version of) `README.md` file (included in `lawyer_suppl.zip`) which describes the Rocq formalization.

## Kick-the-tires: checking the pre-built formalization in the virtual machine

1. Obtain the appropriate VM
   - if you use an x86 system (**we highly recommend following this option if you have access to an x86 machine**):
     1. Install [VirtualBox](https://www.virtualbox.org/) (we used the version 7.2.4)
	 2. Download the `artifact.ova` file.
	 2. Open VirtualBox and navigate to `File/Import Appliance`. Provide the path to the downloaded `artifact.ova` and follow instructions to create a VM.
   - if you use a Mac with an Apple Silicon chip (**we followed [these instructions](https://simo9265.medium.com/convert-ova-to-qcow2-and-start-it-with-utm-13fa3fc4c3db) to obtain `artifact.qcow2` and run the VM on Mac**):
     1. Install [UTM](https://mac.getutm.app/). We used version 4.5.4 (100)
     2. Download the `artifact.qcow2` file.
     3. Open UTM, press `+` button, select `Emulate`, `Other`, choose `Boot Device: None` and follow instructions to create a VM.
     4. Open settings for the new VM, navigate to `QEMU` and uncheck `UEFI Boot` option.
     5. Create a disk to boot from:
	     1. Open settings for the new VM and navigate to `New Drive`.
		 2. Choose IDE interface, set `Size` to be the size of `artifact.qcow2`, click `Import`.
		 3. In the next window, select `artifact.qcow2` and press `Open`.
		 4. Upon completion, drag the new IDE drive to the top of available drives.
3. Run the newly created VM. The rest of the instructions below are to be executed inside the VM.	 
4. Navigate to `/home/lawyer/artifact/lawyer`. 
5. Run `make -j 4`. This will build the proofs of Lawyer and should terminate in a second, as the proofs are already built.
6. Open `check/check.v` with an editor of choice; the VM provides Emacs+Proof General and VSCode+vsrocq.
   This file collects all the theorems we prove for our case studies and examples.
7. Step through every line of this file (`Next` button in Proof General or `Step Forward` button in vsrocq).
8. The last `Print Assumptions` line prints all the axioms that the listed theorems rely on.
   Processing it might take a while, and vsrocq might appear to be stuck; wait for up to a minute for it to complete.
   The used axioms will be listed at the bottom of the output. Check that only the following axioms are used:
   - `RelationalChoice.relational_choice`
   - `ClassicalUniqueChoice.dependent_unique_choice`
   - `Classical_Prop.classic`
   - `classical.PropExt`
   - `classical.FunExt`
   - `classical.Choice`
9. See the sections below for a detailed description of the technical development.

## Full instructions: re-building the formalization manually

- In the VM, you can run `make clean; make -j 4` in `/home/lawyer/artifact/lawyer`.
  This will rebuild the formalization of Lawyer, while keeping the rest of dependencies, including Trillium, untouched.
- Alternatively, you can rebuild the entire development from scratch, either inside VM or locally.
  First, install [opam](https://opam.ocaml.org/) according to the instructions for your operating system. We used the version 2.1.2.
  Then, use the `lawyer_suppl.zip` file (in the VM, it is located in `/home/lawyer/artifact/`) and follow the installation instructions below:
    
        # unpack the files (assuming the supplementary material is in lawyer_suppl.zip)
        unzip -d lawyer_suppl lawyer_suppl.zip
        # move into the working directory
        cd lawyer_suppl
        
        # create a new opam environment
        opam switch create lawyer-env 5.2.0
        # switch into the new environment
        eval $(opam env --switch=lawyer-env)
        
        # set up repository for Rocq packages
        opam repo add coq-released https://coq.inria.fr/opam/released
        # set up the local repository for Trillium
        opam pin add trillium trillium/ --no-action
        
        # move into the Lawyer directory
        cd lawyer/
        # install all dependencies of Lawyer
        opam install . --deps-only
        # build Lawyer; adjust the number of jobs as needed
        make -j 5
	
## Structure of the technical development

- `trillium/` - the Trillium framework
- `lawyer/` - the implementation of the Lawyer project
  - `fairness/` - general definitions of traces and fairness, as well as various utility files
  - `heap_lang/` - definition and reasoning rules for the programming language being used
   - `lawyer/`
     - `examples/` - case studies
	 - `obligations/` - implementation of the obligations-based reasoning
   - `check/` - collection of the end results
- `paper-appendix.pdf` - version of the paper with the technical appendix.
	 
## Correspondence between the paper and Rocq formalization

### Section 2

#### Section 2.1

- No-Obligations Model (Fig. 1)
  It can be viewed simply as a subset of the Obligations Model with restricted state and transitions.
  Namely, No-Obligations Model corresponds to choosing Level to be the empty set (see Appendix C).
  Therefore, we do not provide a separate Rocq definition of No-Obligations Model.

- Example programs
  Each example program from Section 2.1 has a subfolder X in `lawyer/lawyer/examples/`.
  Inside of it, the `X.v` file contains the verification of the program, and `X_adequacy.v` proves the meta-level property about the execution of that program.
  - Statically-known bound (Fig. 2): `const_term/`subfolder.
    The proved property is execution time being linear wrt. the value of N argument.
  - Runtime-determined Bound (Fig. 3): `rt_bound/` subfolder.
    The proved property is termination under fair scheduler (since internally it uses a blocking `nondet` function).
  - Delaying example (Fig. 4): `lf_counter/` subfolder.
    The proved property is termination under any scheduler.

#### Section 2.2

- Definition of Obligations Model (Fig. 5): `lawyer/lawyer/obligations/obligations_model.v`
  - OM parameters:  `ObligationsParams` typeclass
  - OM state: `ProgressState` record.
	Note that "fuel" component of the state is named "ps_cps", and the "barrel" resource in logic is called "cp".
	Well-formedness condition is defined in `lawyer/lawyer/obligations/obligations_wf.v`, record `om_st_wf`.
  - OM transitions: definition `om_trans`
  - OM as a Trillium model: definition `ObligationsModel`
- Example programs
  Similarly to the above, the results are located in the subfolders of `lawyer/lawyer/examples/`.
  The property we prove for these examples is termination under fair scheduler.
  - Blocking example (Fig. 6): `nondet/` subfolder, see specifically `nondet/nondet_adequacy.v`, theorem `nondet_pre_allocated_termination`.
  - Fork example (Fig. 7): `nondet/` subfolder.

#### Section 2.3

- Definition of traces: `lawyer/fairness/inftraces.v`, definition `trace`.
- Definitions of trace state and label lookups: `lawyer/fairness/trace_lookup.v`, definitions `state_lookup` and `label_lookup` correspondingly.
- Definition of trace validity: `lawyer/fairness/inftraces.v`, definition `trace_valid`; also see `lawyer/fairness/trace_lookup.v`, lemma `trace_valid_steps''`.
- Operational semantics of our language (Fig. 8): `lawyer/heap_lang/lang.v`
- Refinement relation (definitions 1, 2 and 3).
  Our implementation of refinement proceeds slightly differently compared to the paper presentation.
  1. The state relation in paper (Definition 1) consists of two parts: _sameThreads_ and _liveThreads_. Contrary, the Rocq version (`lawyer/lawyer/obligations/obligations_adequacy.v`, definition `obls_st_rel`) only includes the latter.
     Indeed, _sameThreads_ is not explicitly used for proving termination, which is the main purpose of the refinement we establish. 
     However, _sameThreads_ is used to _establish_ the refinement (`lawyer/lawyer/obligations/obligations_adequacy.v`, proof of lemma `no_obls_live_tids`) as a part of proving _AlwaysHolds_. Therefore, we keep this condition as a part of trace interpretation (see `lawyer/lawyer/obligations/obligations_em.v`, definition `threads_own_obls`).
  2. The finite trace refinement in paper (Definition 2) is defined by placing restrictions on every transition in both traces.
     Contrary, the Rocq implementation proceeds in two steps.
	 1. We start by defining the notion of "valid evolution step" (`lawyer/lawyer/obligations/obligations_em.v`, definition `obls_valid_evolution_step`) that intuitively captures the "lock-step" relation between physical and model steps.
     2. Then, we show that the proof of weakest precondition implies intensional refinement (see Trillium paper for definition) of the specific relation on pairs of physical and model traces.
	    Namely, the last transitions of such traces must form a valid evolution step.
	 3. Then, we show that this intensional refinement in fact implies the refinement from Definition 3 (minus the _sameThreads_ part discussed above).

	See `lawyer/heap_lang/simulation_adequacy.v`, comment inside of `strong_simulation_adequacy_traces_multiple` lemma that discusses points 2 and 3 above.
- Relative image-finiteness of refinement relation (Lemma 2.1): `lawyer/lawyer/obligations/obligations_adequacy.v`, lemma `obls_sim_rel_FB`.
- General trace fairness (definition 4): `lawyer/fairness/fairness.v`, definition `fair_by'`. Also see the lemma `fair_by'_weakly_fair` in the same file for equivalence with more common notion of weak fairness.
  Then, notion of fair execution is given by `fair_ex`.
  "Obligations-fair" traces are defined in `lawyer/lawyer/obligations/obligations_model.v`, definition `obls_trace_fair`.
- Transporting of execution fairness to the model trace (Lemma 2.2): `lawyer/lawyer/obligations/obligations_adequacy.v`, lemma `exec_om_fairness_preserved`
- Termination of obligations-fair OM traces (Lemma 2.3): `lawyer/lawyer/obligations/obls_termination.v`, theorem `obls_fair_trace_terminate`

### Section 3
- Verification of `nondet` example: `lawyer/lawyer/examples/nondet/nondet.v`
- Definitions of OM resources (Fig. 9), _OU_ (along with its iterated version) and related lemmas (Fig. 10): `lawyer/lawyer/obligations/obligations_resources.v`
- Two-step program logic and model updates: `lawyer/lawyer/program_logic.v`.
  In particular, the rule _trillium-step-nval-simpl_ corresponds to the lemma `sswp_MU_wp`.
- _sswp_ and rules for it: `lawyer/lawyer/program_logic.v` (adapted from Fairneris project): `lawyer/heap_lang/sswp_logic.v`

### Section 4
The case study is located in `lawyer/lawyer/examples/ticketlock/`.
Code for ticketlock implementation and top-level program can be found inn `ticketlock.v` and `client.v` correspondingly.
The final result stating the fair termination of the closed program is located in `closed_adequacy.v`. 

#### Section 4.1
- _BOU_ definition and related lemmas (Fig. 14): see `lawyer/lawyer/obligations/obligations_resources.v`. 
- The rule _MU-OM-nofork_: `lawyer/lawyer/obligations/obligations_logic.v`, lemma `BOU_AMU`.
  Throughout the development, we use the `AMU` modality, which can be thought of as simply `MU`. 
	
#### Section 4.2
- Sequential fair lock specification (Fig. 15): `lawyer/lawyer/examples/ticketlock/releasing_lock.v`, record `ReleasingFairLock`.

#### Section 4.3
- Proof that ticketlock satisfies the sequential lock specification for any choice of spec's parameters satisfying a number of restrictions: `lawyer/lawyer/examples/ticketlock/ticketlock_releasing.v`, definition `RFL_FL_TL'`.
- Verification of ticketlock implementation against the logically atomic specification: `lawyer/lawyer/examples/ticketlock/ticketlock.v`, see in particular `TL_FL`.
- Derivation of the sequential specification for a wrapper over logically atomic implementation: `lawyer/lawyer/examples/ticketlock/releasing_lock.v`, see in particular `RFL_FL`. 
	
#### Section 4.4
Verification of the top-level program on top of the sequential lock specification: `lawyer/lawyer/examples/ticketlock/client.v`, theorem `client_spec`.
	 
### Appendix

#### Appendix A
- Well-formedness of obligations states: `lawyer/lawyer/obligations/obligations_wf.v`, record `om_st_wf`.	 
- OM starting state (definition 6): `lawyer/lawyer/obligations/obligations_em.v`, definition `init_om_state`.
	 
#### Appendix B
- Full adequacy theorem of Lawyer: `lawyer/lawyer/obligations/obligations_adequacy.v`, lemma `obls_terminates_impl_multiple`.
- Specialized adequacy theorem (Theorem B.1): lemma `obls_terminates_impl_paper`.
	 
#### Appendix C
- Termination of all OM traces when _Level_ is the empty set (Corollary C.1): `lawyer/lawyer/obligations/unfair_termination.v`, lemma `always_term_wo_lvls`.
- Termination within constant time when _Level_ is the empty set and _Degree_ is singleton (Corollary C.2): `lawyer/lawyer/obligations/unfair_termination.v`, lemma `always_terminates_within_bound`.


#### Appendix D

Operational semantics of our language (Fig. 8 and 16): `lawyer/heap_lang/lang.v`.
The mechanization mentions prophecy variables, but they are never used throughout the development.


#### Appendix E

Full form of Lawyer rules (Fig. 17) can be found in `lawyer/lawyer/program_logic.v` (rules connecting _wp_ with _sswp_ and _MU_) and `lawyer/lawyer/obligations/obligations_logic.v` (rules connecting _MU_ with _BOU_).


#### Appendix F
- "Total" atomic updates (Definition 7): `lawyer/lawyer/examples/ticketlock/obls_atomic.v`, definition `TAU`.
- "Total" logically atomic triples: `lawyer/lawyer/examples/ticketlock/obls_atomic.v`, definitions `TLAT` and `TLAT_RR` for different kinds of "wait clauses" used in underlying `TAU`
- Logically atomic fair lock specification (Fig. 18): `lawyer/lawyer/examples/ticketlock/fair_lock.v`, record `FairLock`.

#### Appendix G

Verification of the top-level program on top of the sequential lock specification: `lawyer/lawyer/examples/ticketlock/client.v`, theorem `client_spec`.


### Additional case studies
- Two implementations of parallel composition operator and rules for them: `lawyer/lawyer/examples/par.v`, definitions `par` and `par_sym`, along with `par_spec` and `par_sym_spec` lemmas.
  Moreover, the case study in `lawyer/lawyer/examples/nondet/(nondet_par.v, nondet_par_adequacy.v)` is a version of _nondet_ implementation that uses parallel composition. 
- A program consisting of two threads that increment the shared counter in turns, up to a certain bound, waiting for each others' turn: `lawyer/lawyer/examples/eo_fin/(eo_fin.v, eo_fin_adequacy.v)`
- Program illustrating the concurrent use of two locks: `lawyer/lawyer/examples/ticketlock/(two_locks, two_locks_adequacy).v`

