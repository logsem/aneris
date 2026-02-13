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
- Wait-freedom (Definition 3): `lawyer/nonblocking/wfree_traces.v`, definition `wait_free_strong`.
  Again, it is parameterized by a stuckness bit and an unused predicate on call arguments.
- Lawyer specification of wait-freedom (Definition 4): `lawyer/nonblocking/om_wfree_inst.v`, record `WaitFreeSpec`.
  Note the following:
  - Parameter `P` can be ignored
  - Instead of fixed amount of fuel, we use a fuel function that returns a necessary amount fuel depending on the argument
  - This specification explicitly mentions an invariant that should be established from any allowed starting configuration and that can be used by both Hoare triples
- Wait-freedom adequacy theorem (Theorem 5): `lawyer/nonblocking/wfree_adequacy.v`, theorem `wfree_is_wait_free`.
  Again, it is parameterized by a stuckness bit, and the unused predicate on call arguments is set to be always true.
  It also explicitly requires the value representing the wait-free operation to be a lambda-expression.
  
  
