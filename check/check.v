From lawyer.examples.ticketlock Require Import closed_adequacy. 
From lawyer.examples.nondet Require Import nondet_adequacy nondet_par_adequacy.
From lawyer.examples.const_term  Require Import const_term_adequacy.
From lawyer.examples.eo_fin  Require Import eo_fin_adequacy.
From lawyer.examples.lf_counter  Require Import lf_counter_adequacy.
From lawyer.examples.rt_bound  Require Import rt_bound_adequacy. 


Definition results := (
  closed_program_terminates, 
  nondet_termination, 
  nondet_par_termination,
  const_term_bound_termination, 
  eofin_terminates, 
  lf_counter_termination,
  rt_bound_termination
). 

Goal True. 
  idtac "-------------------------------------------".
  idtac "The axioms used throughout the development:".
Abort. 


Print Assumptions results.
