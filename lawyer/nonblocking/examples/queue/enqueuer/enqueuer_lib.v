From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.base_logic.lib Require Import invariants.
From lawyer.nonblocking.examples.queue Require Import simple_queue_utils simple_queue.
From heap_lang Require Import heap_lang_defs lang notation.

Close Scope Z.


Section EnqueuerLibViewshifts.
  Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.  
  Context {QL: QueueG Σ}.
  Context {SQT: SimpleQueueTokens Σ}.
  Context {q_sq: SimpleQueue}.

  Context (PE: val -> iProp Σ). 

  Lemma enqueuer_close_vs t br ph:
    queue_inv PE -∗ rop_token -∗ read_head_resources t br ph None -∗
    |={⊤}=> read_head_token.
  Proof using.
    iIntros "#INV RTOK RH". 
    iInv "INV" as "(%hq & %h & %t_ & %br_ & %fl & %rop_ & %od & %hist & inv)" "CLOS".
    iEval (rewrite /queue_inv_inner) in "inv".
    iDestruct "inv" as "(>HQ & >AUTHS & >%ORDER & >QI & >DANGLE & OHV & >RHI & >RH' & >DQ & EI)".
    iDestruct "RH'" as "[(% & RH' & RTOK') | TOK']".
    { by iDestruct (read_head_resources_excl with "RH RH'") as "?". }
    iDestruct (read_head_resources_auth_agree with "[$] [$]") as %[<- <-].
    iMod ("CLOS" with "[-TOK']") as "_".
    2: by iFrame.
    iFrame. iNext. iSplit; [done| ]. iLeft. iFrame.
  Qed.

End EnqueuerLibViewshifts.
