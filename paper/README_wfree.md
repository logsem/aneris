# Supplementary material for the wait-freedom paper

This document describes the Rocq formalization for the "Verifying wait-freedom for concurrent higher-order programs" paper.

## Structure of the technical development

Most of our development is an extension of the Lawyer project.
However, we also use a fork of Trillium, as we use a generalized adequacy theorem and weakest precondition.
Below, we outline our additions to both projects.

- `trillium/` - our fork of Trillium framework
  - `bi/weakestpre.v` - generalization of weakest precondition parameterized with the bit that allows or prohibits forking
  - `program_logic/adequacy_cond.v` - definition of the progress resource and proof of conditional adequacy theorem
- `lawyer/nonblocking` - wait-freedom extension of Lawyer
  - `.` - most of wait-freedom development, except for restricted wait-freedom and logical relations
  - `tokens/` - adaptation to the restricted wait-freedom
  - `logrel/` - definitions and theorems about logical relations
  - `examples/` - case studies on wait-freedom
- `paper-appendix.pdf` - version of the paper with the technical appendix.
	 
## Installation

First, install [opam](https://opam.ocaml.org/) according to the instructions for your operating system. We used the version 2.1.2. Then execute the following:

    # unpack the files (assuming the supplementary material is in wfree_suppl.zip)
    unzip -d wfree_suppl wfree_suppl.zip
	# move into the working directory
	cd wfree_suppl
	
    # create a new opam environment
    opam switch create wfree-env 5.2.0
	# switch into the new environment
    eval $(opam env --switch=wfree-env)
	
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

To check the axioms used in the development, step through the file `check/check_wfree.v`. It is a collection of our end results (adequacy statements for the case studies on wait-freedom), to which all the used assumptions are printed.
	
Our development relies on the axiom of choice, law of excluded middle, functional and propositional extensionality.
	

## Correspondence between the paper and Rocq formalization

### Section 2

#### Section 2.1

- Operational semantics of our language (Figure 3): `lawyer/heap_lang/lang.v`
- Calls and returns (Definition 1): `lawyer/nonblocking/trace_context.v`, definitions `call_at` and `return_at`. 
  Note that the former explictly mentions the call argument, whereas the definition in the paper existentially quantifies over it.
- General definitions and lemmas about traces: `trillium/traces/*.v`
- Eventual return of calls (Definition 2): `lawyer/nonblocking/wfree_traces.v`, definition `always_returns_strong`.
  Note that it is additionally parameterized with:
  - stuckness bit (thus covering the possibly-stuck definition)
  - predicate on the call argument. *This parameter is always set to an always true predicate and thus can be ignored.*
- Call fairness ("schedUntilRet"): `lawyer/nonblocking/wfree_traces.v`, definition `fair_call_strong`.
- Client validity: `lawyer/nonblocking/logrel/valid_client.v`, definition `valid_client`.
- Wait-freedom (Definition 3): `lawyer/nonblocking/wfree_traces.v`, definition `wait_free_strong`.
  Again, it is parameterized by a stuckness bit and an unused predicate on call arguments.

#### Section 2.2

- Lawyer specification of wait-freedom (Definition 4): `lawyer/nonblocking/om_wfree_inst.v`, record `WaitFreeSpec`.
  Note the following:
  - Parameter `P` can be ignored
  - Instead of fixed amount of fuel, we use a fuel function that returns a necessary amount fuel depending on the argument
  - This specification explicitly mentions an invariant that should be established from any allowed starting configuration and that can be used by both Hoare triples
  - We prohibit the wait-free operation from forking 
- Wait-freedom adequacy theorem (Theorem 5): `lawyer/nonblocking/wfree_adequacy.v`, theorem `wfree_is_wait_free`.
  Again, it is parameterized by a stuckness bit, and the unused predicate on call arguments is set to be always true.
  It also explicitly requires the value representing the wait-free operation to be a lambda-expression.
    
### Section 3

- Verification of the wait-freedom specification for counter example: `lawyer/nonblocking/examples/counter/counter.v`, definition `counter_WF_spec`.
  Note that throughout the development we use the two-step logic of Lawyer directly, i.e. applying separate rules for a physical and a model steps. 
- Wait-freedom of counter example: `lawyer/nonblocking/examples/counter/counter_adequacy.v`.
- The degree parameter of fuel is always set to the lowest degree `d0` of our Obligations Model instantiation.
- The fraction parameter of phase is always set to `1/2`.
- Lawyer triple for wait-freedom: `lawyer/nonblocking/om_wfree_inst.v`, definition `wait_free_method_gen`.
  Ignore the `P` and `Q` parameters. 
- "noMod" triple for wait-freedom: defined directly as value interpretation (see Sec. 5.2)

### Section 4

#### Section 4.1

- Stuckness variations of definitions related to wait-freedom (Definitions 6 and those mentioned below it): they are specific cases of definitions used for Section 2.1 with stuckness bit set to `MaybeStuck`.
- Adequacy theorem for possibly-stuck wait-freedom: instantiation of `lawyer/nonblocking/wfree_adequacy.v`, theorem `wfree_is_wait_free` with stuckness bit set to `MaybeStuck`.
- Modular verification of `list_map`: `lawyer/nonblocking/examples/list_map/list_map.v`, definition `hlm_WF_fix_spec_unsafe`.
- Possibly-stuck wait-fredom of `list_map (incr l)`: `lawyer/nonblocking/examples/list_map/list_map_adequacy.v`.

#### Section 4.2

Note that throughout the restricted wait-freedom development we use multisets of operations and not lists.

- Implementation of the queue algorithm in our language: 
  The methods are scattered across multiple files in `lawyer/nonblocking/examples/queue`:
  - `dequeuer/dequeue.v`, definition `dequeue`
  - `dequeuer/read_head_dequeuer.v`, definition `read_head_dequeuer`
  - `dequeuer/dequeuer_thread.v`, definition `dequeuer_thread`
  - `enqueuer/enqueue.v`, definition `enqueue`
  - `enqueuer/read_head.v`, definition `read_head_enqueuer`
  - `enqueuer/enqueuer_thread.v`, definition `enqueuer_thread`
- Restricted wait-freedom (Definition 7): `lawyer/nonblocking/wfree_traces.v`, definition `wait_free_restr`.
- Exclusion of forks: `lawyer/nonblocking/logrel/valid_client.v`, definition `no_forks`.
- Specification of restricted wait-freedom (Definition 8): `lawyer/nonblocking/tokens/om_wfree_inst_tokens.v`, definition `WaitFreeSpecToken`.
- Definition and lemmas about tokens resource algebra: `lawyer/nonblocking/tokens/tokens_ra.v`
- Adequacy theorem for restricted wait-freedom (Theorem 9): `lawyer/nonblocking/tokens/wfree_adequacy_tokens.v`, theorem `wfree_token_is_wait_free_restr`.
- Restricted wait-freedom of queue: `lawyer/nonblocking/examples/queue/simple_queue_adequacy.v`

### Section 5

#### Section 5.1

- Reduction to proving termination: it is scattered across multiple lemmas used to prove `wfree_is_wait_free` mentioned above.
  In particular, see the lemmas in `WFAdequacy` section which fixes the parameters of an infinite call.
- Definition of progress resource: `trillium/trillium/program_logic/adequacy_cond.v`, record `ProgressResource`. Note that it is additionally parameterized with stuckness and forking bits (and list of postconditions mentioned in the appendix).
- Conditional adequacy theorem of Trillium: `trillium/trillium/program_logic/simulation_adequacy_em_cond.v`, theorem `PR_strong_simulation_adequacy_traces_multiple`.
- Refinement relation for wait-freedom: `lawyer/nonblocking/wfree_adequacy_lib.v`, definition `obls_sim_rel_wfree`

#### Section 5.2
- Expression relation: `lawyer/nonblocking/logrel/logrel.v`, definition `interp_expr`
- Value relation: `lawyer/nonblocking/logrel/logrel.v`, definition `interp`
- Fundamental theorem (Theorem 12): `lawyer/nonblocking/logrel/fundamental.v`, theorem `fundamental`
- Robust safety of the wait-free operation (Theorem 13): `lawyer/nonblocking/wfree_adequacy.v`, definition `init_wptp_wfree`

#### Section 5.3

- Definition of progress resource for wait-fredom: `lawyer/lawyer/nonblocking/pr_wfree.v`, definition `pr_pr_wfree`.
- Definition of the `infCallPrefix` predicate: `lawyer/nonblocking/wfree_traces.v`, definition `fits_inf_call`.
- Proof of the progress resource laws: `lawyer/lawyer/nonblocking/pr_wfree.v`, definition `PR_wfree`.

### Extra
- "Wait-freedom" of a simple sequential program: `lawyer/nonblocking/examples/mk_ref/(mk_ref, mk_ref_adequacy).v`
- Variations of above definitions and theorems for restricted wait-freedom: `lawyer/nonblocking/tokens/*.v`.
  In particular:
  - Extension of trace intepretation for physical WP that keeps track of tokens: `pwp_ext.v`
  - Logical relation and fundamental theorem for token-based specifications: `logrel_tok.v` and `fundamental_tok.v`
  - Lifting of a stronger specification to one required by token-based FTLR: `op_spec_lifting.v`, lemma `lift_spec`
  - Progress resource for wait-freedom: `pr_wfree_tokens.v`
