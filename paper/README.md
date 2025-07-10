# Supplementary material for the Lawyer paper

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
	 
## Installation

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
	
## Checking the end results

To check the axioms used in the development, step through the file `check/check.v`. It is a collection of our end results (adequacy statements for the case studies), to which all the used assumptions are printed.
	
Our development relies on the axiom of choice, law of excluded middle, functional and propositional extensionality.
	

## Correspondence between the paper and Rocq formalization

### Section 2

#### Section 2.1

- Definition of Obligations Model (Fig. 6): `lawyer/lawyer/obligations/obligations_model.v`
  - OM parameters:  `ObligationsParams` typeclass
  - OM state: `ProgressState` record.
	Well-formedness condition is defined in `lawyer/lawyer/obligations/obligations_wf.v`, record `om_st_wf`.
	Note that "fuel" component of the state is named "ps_cps", and the corresponding resource in logic is called "cp".
  - OM transitions: definition `om_trans`
  - OM as a Trillium model: definition `ObligationsModel`
- Example programs
  Each example program from Section 2.1 has a subfolder X in `lawyer/lawyer/examples/`.
  Inside of it, the `X.v` file contains the verification of the program, and `X_adequacy.v` proves the meta-level property about the execution of that program.
  Unless said otherwise, the property we prove is termination under fair scheduler.
  - Statically-determined Bound (Fig. 1): `const_term/`subfolder.
	The proved property is execution time being linear wrt. the value of N argument.
  - Runtime-determined Bound (Fig. 2): `rt_bound/` subfolder.
  - Blocking example (Fig. 3): `nondet/` subfolder, see specifically `nondet/nondet_adequacy.v`, theorem `nondet_pre_allocated_termination`.
  - Delaying example (Fig. 4): `lf_counter/` subfolder.
    The proved property is termination under any scheduler.
  - Fork example (Fig. 5): `nondet/` subfolder.
- Finite branching of OM (Lemma 2.1): `lawyer/lawyer/obligations/obligations_fin_branch.v`, lemma `om_trans_locale_approx`.
  Note that it restricts the domain of obligations mapping, instead of phases mapping. For well-formed states, these restrictions are equivalent.

#### Section 2.2

- Definition of traces: `lawyer/fairness/inftraces.v`, definition `trace`.
- Definitions of trace state and label lookups: `lawyer/fairness/trace_lookup.v`, definitions `state_lookup` and `label_lookup` correspondingly.
- Definition of trace validity: `lawyer/fairness/inftraces.v`, definition `trace_valid`; also see `lawyer/fairness/trace_lookup.v`, lemma `trace_valid_steps''`.
- Operational semantics of our language: `lawyer/heap_lang/lang.v`
- Refinement relation (definitions 1, 2 and 4).
  Our implementation of refinement proceeds slightly differently compared to the paper presentation.
  1. The state relation in paper (Definition 1) consists of two parts: _sameThreads_ and _liveThreads_. Contrary, the Rocq version (`lawyer/lawyer/obligations/obligations_adequacy.v`, definition `obls_st_rel`) only includes the latter.
     Indeed, _sameThreads_ is not explicitly used for proving termination, which is the main purpose of the refinement we establish. 
     However, _sameThreads_ is used to _establish_ the refinement (`lawyer/lawyer/obligations/obligations_adequacy.v`, proof of lemma `no_obls_live_tids`) as a part of proving _AlwaysHolds_. Therefore, we keep this condition as a part of trace interpretation (see `lawyer/lawyer/obligations/obligations_em.v`, definition `threads_own_obls`).
  2. The finite trace refinement in paper (Definition 2) is defined by placing restrictions on every transition in both traces.
     Contrary, the Rocq implementation proceeds in two steps.
	 1. We start by defining the notion of "valid evolution step" (`lawyer/lawyer/obligations/obligations_em.v`, definition `obls_valid_evolution_step`) that intuitively captures the "lock-step" relation between physical and model steps.
     2. Then, we show that the proof of weakest precondition implies intensional refinement (see Trillium paper for definition) of the specific relation on pairs of physical and model traces.
	    Namely, the last transitions of such traces must form a valid evolution step.
	 3. Then, we show that this intensional refinement in fact implies the refinement from Definition 4 (minus the sameThreads part discussed above).

	See `lawyer/heap_lang/simulation_adequacy.v`, comment inside of `strong_simulation_adequacy_traces_multiple` lemma that discusses points 2 and 3 above.
- Relative image-finiteness of refinement relation (Lemma 2.2): `lawyer/lawyer/obligations/obligations_adequacy.v`, lemma `obls_sim_rel_FB`.
- OM starting state (definition 3): `lawyer/lawyer/obligations/obligations_em.v`, definition `obls_sim_rel_FB`.
  Note that it applies to physical states with potentially more than one thread, which requires assigning non-initial phases to each of them.
- General trace fairness (definition 5): `lawyer/fairness/fairness.v`, definition `fair_by'`. Also see the lemma `fair_by'_weakly_fair` in the same file for equivalence with more common notion of weak fairness.
  Then, notion of fair execution is given by `fair_ex`.
  "Obligations-fair" traces are defined in `lawyer/lawyer/obligations/obligations_model.v`, definition `obls_trace_fair`.
- Transporting of execution fairness to the model trace (Lemma 2.4): `lawyer/lawyer/obligations/obligations_adequacy.v`, lemma `exec_om_fairness_preserved`
- Termination of obligations-fair OM traces: `lawyer/lawyer/obligations/obls_termination.v`, theorem `obls_fair_trace_terminate`

### Section 3
- Verification of nondet example: `lawyer/lawyer/examples/nondet/nondet.v`
- Definitions of OM resources, _OU_ (along with its iterated version) and related lemmas: `lawyer/lawyer/obligations/obligations_resources.v`
- Two-step program logic and model updates: `lawyer/lawyer/program_logic.v` (adapted from Fairneris project).
  In particular, the rule _trillium-step-nval-simpl_ corresponds to the lemma `sswp_MU_wp`.
- _sswp_ and rules for it: `lawyer/lawyer/program_logic.v` (adapted from Fairneris project): `lawyer/heap_lang/sswp_logic.v`

### Section 4
The case study is located in `lawyer/lawyer/examples/ticketlock/`.
Code for ticketlock implementation and top-level program can be found inn `ticketlock.v` and `client.v` correspondingly.
The final result stating the termination of the closed program is located in `closed_adequacy.v`. 

#### Section 4.1
- _BOU_ definition and related lemmas: see `lawyer/lawyer/obligations/obligations_resources.v`. 
- The rule _MU-OM-nofork_: `lawyer/lawyer/obligations/obligations_logic.v`, lemma `BOU_AMU`.
	
#### Section 4.2
- Sequential fair lock specification (Definition 6): `lawyer/lawyer/examples/ticketlock/releasing_lock.v`, record `ReleasingFairLock`.
- Logically atomic fair lock specification: `lawyer/lawyer/examples/ticketlock/fair_lock.v`, record `FairLock`.
- Verification of ticketlock implementation against the logically atomic specification: `lawyer/lawyer/examples/ticketlock/ticketlock.v`, see in particular `TL_FL`. 
- Derivation of the sequential specification for a wrapper over logically atomic implementation: `lawyer/lawyer/examples/ticketlock/releasing_lock.v`, see in particular `RFL_FL`. 
	
#### Section 4.3
Verification of the top-level program on top of the sequential lock specification: `lawyer/lawyer/examples/ticketlock/client.v`, theorem `client_spec`.
	 
### Appendix

#### Appendix A
Well-formedness of obligations states: `lawyer/lawyer/obligations/obligations_wf.v`, record `om_st_wf`.
	 
#### Appendix B
- Termination of all OM traces when _Level_ is the empty set: `lawyer/lawyer/obligations/unfair_termination.v`, lemma `always_term_wo_lvls`.
- Termination within constant time when _Level_ is the empty set and _Degree_ is singleton: `lawyer/lawyer/obligations/unfair_termination.v`, lemma `always_terminates_within_bound`.
	 
#### Appendix C
Full form of Lawyer rules can be found in `lawyer/lawyer/program_logic.v` (rules connecting _wp_ with _sswp_ and _MU_) and `lawyer/lawyer/obligations/obligations_logic.v` (rules connecting _MU_ with _BOU_).
	 
#### Appendix D
- "Total" atomic updates: `lawyer/lawyer/examples/ticketlock/obls_atomic.v`, definition `TAU`.
- "Total" logically atomic triples: `lawyer/lawyer/examples/ticketlock/obls_atomic.v`, definitions `TLAT` and `TLAT_RR` for different kinds of "wait clauses" used in underlying `TAU`.

### Additional case studies
- Two implementations of parallel composition operator and rules for them: `lawyer/lawyer/examples/par.v`, definitions `par` and `par_sym`, along with `par_spec` and `par_sym_spec` lemmas.
  Moreover, the case study in `lawyer/lawyer/examples/nondet/(nondet_par.v, nondet_par_adequacy.v)` is a version of _nondet_ implementation that uses parallel composition. 
- A program consisting of two threads that increment the shared counter in turns, up to a certain bound, waiting for each others' turn: `lawyer/lawyer/examples/eo_fin/(eo_fin.v, eo_fin_adequacy.v)`
