From FA Require Import String DFA NFA NFA2DFA eNFA eNFA2NFA.
From mathcomp Require Import all_ssreflect.

Lemma enfa_dfa_lang_eqi: forall n, enfa_language n =i dfa_language (nfa_dfa (enfa_nfa n)).
Proof. intros.
       unfold enfa_language, nfa_language, dfa_language.
       move => y. apply/idP/idP => /=.
         intro Ha.
         rewrite inE in Ha.
         rewrite inE.
         rewrite <- enfa_nfa_acc_eq in Ha.
         rewrite nfa_dfa_acc_eq in Ha.
         easy.
         
         intro Ha.
         rewrite inE in Ha.
         rewrite inE.
         rewrite <- enfa_nfa_acc_eq.
         rewrite nfa_dfa_acc_eq.
         easy.
Qed.