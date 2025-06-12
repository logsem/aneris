# Lawyer

## Structure of the technical development

trillium/ and lawyer/

## Installation

## Correspondence between the paper and Rocq formalization

### Section 2

#### Section 2.1
     - Definition of Obligations Model
	   - parameters
	   - state
       - transitions
	   - Trillium model
	 - Example programs
	   - Statically-determined Bound (Fig. 1): lawyer/lawyer/examples/const_term/
	     const_term.v contains verification of the program from Fig. 1.
		 const_term_adequacy.v shows that this program execution time is linear wrt. the value of N argument.
	   - Runtime-determined Bound (Fig. 2): lawyer/lawyer/examples/rt_bound/
	     rt_bound.v contains verification of the program from Fig. 2.
		 rt_bound_adequacy.v shows that this program terminates under fair scheduler.
	   - Blocking example (Fig. 3)
	     We don't verify this exact example: it is a simplified version of Fig. 5, which is verified (see below).
	   - Delaying example (Fig. 4)
	     lf_counter.v contains verification of the program from Fig. 4.
		 lf_counter_adequacy.v shows that this program terminates under any scheduler.
	   - Fork example (Fig. 5)
	     nondet.v contains verification of the program from Fig. 5.
		 nondet_adequacy.v shows that this program terminates under fair scheduler.
	 - Finite branching of OM (Lemma 2.1): lawyer/lawyer/obligations/obligations_fin_branch.v, lemma om_trans_locale_approx.
	   Note that it restricts the domain of obligations mapping, instead of phases mapping. For well-formed states, these restrictions are equivalent.

#### Section 2.2
     - Definition of traces: lawyer/fairness/inftraces.v, definition trace.
	 - Definitions of trace state and label lookups: lawyer/fairness/trace_lookup.v, definitions state_lookup and label_lookup correspondingly.
     - Definition of trace validity: lawyer/fairness/inftraces.v, definition trace_valid; also see lawyer/fairness/trace_lookup.v, lemma trace_valid_steps''.
     - Operational semantics of Lambda: lawyer/heap_lang/lang.v
     - Refinement relation (definitions 1 and 2).
	   Our implementation of refinement proceeds slightly differently compared to the paper presentation.
	   1. We maintain, in Iris, the fact that the thread represented on physical and model level are the same (sameThreads in Definition 1): lawyer/lawyer/obligations/obligations_em.v, definition threads_own_obls. 
	   2. We define a notion of "valid evolution step" denoting a pair of physical and model taken by the same thread, ending in pair of states related by sameThreads (Definition 2, the part about states and labels correspondence).
	   *********TODO************** + def 4
	 - Relative image-finiteness of refinement relation (Lemma 2.2): lawyer/lawyer/obligations/obligations_adequacy.v, lemma obls_sim_rel_FB.
	 - OM starting state (definition 3): lawyer/lawyer/obligations/obligations_em.v, definition obls_sim_rel_FB.
	   Note that it applies to physical states with potentially more than one thread and therefore assigns distinct phases to each of them.
     - General trace fairness (definition 5): lawyer/fairness/fairness.v, definition fair_by' (and its legacy equivalent fair_by). Also see the lemma fair_by'_weakly_fair in the same file for equivalence with more common notion of weak fairness.
	   Then, notion of fair execution is given by fair_ex.
	   "Obligations-fair" traces are defined in lawyer/lawyer/obligations/obligations_model.v, definition obls_trace_fair.
	 - Transportation of execution fairness to the model trace (Lemma 2.4): lawyer/lawyer/obligations/obligations_adequacy.v, lemma exec_om_fairness_preserved
	 - Terminationn of obligations-fair OM traces: lawyer/lawyer/obligations/obls_termination.v, theorem obls_fair_trace_terminate

### Section 3
    - Verification of nondet example: lawyer/lawyer/examples/nondet/nondet.v
	- Definitions of OM resources, OU (along with its iterated version) and related lemmas: lawyer/lawyer/obligations/obligations_resources.v
    - Two-step program logic and model updates: lawyer/lawyer/program_logic.v (adapted from Fairneris).
	  In particular, the rule trillium-step-nval-simpl corresponds to the lemma sswp_MU_wp. 
    - sswp and rules for it: lawyer/lawyer/program_logic.v (adapted from Fairneris): lawyer/heap_lang/sswp_logic.v

### Section 4
	The case study is located in lawyer/lawyer/examples/ticketlock/.
	Code for ticketlock implementation and top-level program can be found in ticketlock.v and client.v correspondingly.
	The final result stating the termination of the closed program is located in closed_adequacy.v. 

#### Section 4.1
	- BOU definition and related lemmas: see lawyer/lawyer/obligations/obligations_resources.v. 
	- The rule MU-OM-nofork: lawyer/lawyer/obligations/obligations_logic.v, lemma BOU_AMU (see also BOU_AMU__f applicable to forking steps).
	
#### Section 4.2
	- Sequential fair lock specification (Definition 6): lawyer/lawyer/examples/ticketlock/releasing_lock.v, record ReleasingFairLock.
	- Logically atomic fair lock specification: lawyer/lawyer/examples/ticketlock/fair_lock.v, record FairLock.
    - Verification of ticketlock implementation against the logically atomic specification: lawyer/lawyer/examples/ticketlock/ticketlock.v, see in particular TL_FL. 
	- Derivation of the sequential specification for a wrapper over logically atomic implementation: lawyer/lawyer/examples/ticketlock/releasing_lock.v, see in particular RFL_FL. 
	
#### Section 4.3
	Verification of the top-level program on top of the sequential lock specification: lawyer/lawyer/examples/ticketlock/client.v, theorem client_spec.
	 
## Additional stuff: case studies, appendix
   - par
   - eo_fin
   - full rules
   - tactics		
   - ? remove everything actions-related
   - TAUs
     obls_atomic

   
