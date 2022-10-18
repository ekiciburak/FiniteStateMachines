From FA Require Import String DFA NFA NFA2DFA eNFA.
From mathcomp Require Import all_ssreflect.


Definition enfa_nfa (n: enfa): nfa.
Proof. unshelve econstructor.
       - exact (enfa_state n).
(*        - exact (enfa_start n). *)
       - exact (eps_closure_set n (@enfa_start n)).
       - intros p l.
         exact (enfa_multistep n [set p] (glue eps l)).
       - exact ([set q: n | [exists x, (x \in eps_closure n q) && (x \in enfa_finals n)]]).
Defined.

Lemma enfa_nfa_ms1A: forall (e: enfa) (r: (@enfa_state e))  (A: {set (@enfa_state e)}) (x: String),
  r \in nfa_multistep (enfa_nfa e) (eps_closure_set e A) x ->
  r \in enfa_multistep e A x.
Proof. intros e r A x.
       revert e r A.
       induction x; intros.
       - simpl in *.
         unfold eps_closure_set.
         apply/bigcupP.
         unfold eps_closure_set in H.
         move=>/bigcupP in H.
         destruct H as (p, Ha, Hb).
         exists p.
         easy.
         easy.
       - simpl in *.
         move=>/bigcupP in H.
         destruct H as (p, Ha, Hb).
         move=>/bigcupP in Hb.
         destruct Hb as (i, Hb, Hc).
         apply/bigcupP.
         exists p.
         apply IHx.
         easy.
         unfold eps_closure_set in Hc.
         move=>/bigcupP in Hc.
         destruct Hc as (j, Hc, Hd).
         rewrite inE in Hc.
         unfold eps_closure_set in Hb.
         move=>/bigcupP in Hb.
         destruct Hb as (k, Hb, He).
         rewrite inE in Hb.
         move=>/eqP in Hb.
         subst.
         unfold eps_closure_set.
         apply/bigcupP.
         exists j.
         rewrite inE.
         unfold eps_closure in He.
         rewrite inE in He.
         apply enfa_connect_r with (q := i).
         easy.
         easy.
         easy.
(*          split; easy.
         easy. *)
Qed.

Lemma enfa_nfa_ms2A: forall (e: enfa) (r: (@enfa_state e)) (A: {set (@enfa_state e)}) (x: String),
  r \in enfa_multistep e A x ->
  r \in nfa_multistep (enfa_nfa e) (eps_closure_set e A) x.
Proof. intros e r A x.
       revert e r A.
       induction x; intros.
       - easy.
       - simpl in *.
         move=>/bigcupP in H.
           destruct H as (p, Ha, Hb).
           specialize (IHx e p A Ha).
           simpl.
           apply/bigcupP.
           exists p.
           easy.
           apply/bigcupP.
           exists p.
           unfold eps_closure_set.
           apply/bigcupP.
           exists p.
           rewrite inE. easy.
           unfold eps_closure.
           rewrite inE. 
           apply epsa.
(*            apply connect0. *)
           easy.
Qed.

Lemma enfa_nfa_ms_lAS: forall (e: enfa) (A: {set (@enfa_state e)}) (x: String),
  nfa_acceptance (enfa_nfa e) (eps_closure_set e A) x ->
  enfa_acceptance e A x.
Proof. intros.
       revert e A H.
       induction x; intros.
       - unfold enfa_acceptance, nfa_acceptance in *.
         simpl in *.
         move=>/existsP in H.
         destruct H as (q, H).
         move=>/andP in H.
         destruct H as (Ha, Hb).
         rewrite inE in Hb.
         move=>/existsP in Hb.
         destruct Hb as (r, Hb).
         apply/existsP.
         exists q.
         apply/andP.
         split.
         + easy. 
         + rewrite inE.
           apply/existsP.
           exists r.
           easy.
       - unfold enfa_acceptance in H.
         move=>/existsP in H.
         destruct H as (i, Ha).
         move=>/andP in Ha.
         destruct Ha as (Ha, Hb).
         specialize (enfa_nfa_ms1A e i A (glue x s) Ha); intro HH.
         rewrite inE in Hb.
         move=>/existsP in Hb.
         destruct Hb as (m, Hb).
         unfold nfa_acceptance.
         apply/existsP.
         exists i.
         apply/andP.
         split.
         easy.
         simpl.
         rewrite inE.
         apply/existsP.
         exists m.
         easy.
Qed.

Lemma enfa_nfa_ms_rAS: forall (e: enfa) (A: {set (@enfa_state e)}) (x: String),
  enfa_acceptance e A x ->
  nfa_acceptance (enfa_nfa e) (eps_closure_set e A) x.
Proof. intros.
       revert e A H.
       induction x; intros.
       - unfold enfa_acceptance, nfa_acceptance in *.
         simpl in *.
         move=>/existsP in H.
         destruct H as (q, H).
         move=>/andP in H.
         destruct H as (Ha, Hb).
         rewrite inE in Hb.
         move=>/existsP in Hb.
         destruct Hb as (r, Hb).
         apply/existsP.
         exists q.
         apply/andP.
         split.
         + easy.
         + rewrite inE.
           apply/existsP.
           exists r.
           easy.
       - unfold enfa_acceptance in H.
         move=>/existsP in H.
         destruct H as (i, Ha).
         move=>/andP in Ha.
         destruct Ha as (Ha, Hb).
         specialize (enfa_nfa_ms2A e i A (glue x s) Ha); intro HH.
         rewrite inE in Hb.
         move=>/existsP in Hb.
         destruct Hb as (m, Hb).
         unfold nfa_acceptance.
         apply/existsP.
         exists i.
         apply/andP.
         split.
         easy.
         simpl.
         rewrite inE.
         apply/existsP.
         exists m.
         easy.
Qed.

Lemma enfa_nfa_lang_eqi: forall n, enfa_language n =i nfa_language (enfa_nfa n).
Proof. intros.
       unfold enfa_language, nfa_language.
       move => y. apply/idP/idP => /=.
       intro Ha.
       rewrite inE in Ha.
       apply enfa_nfa_ms_rAS in Ha.
       simpl in Ha.
       rewrite inE.
       easy.
       intro Ha.
       rewrite inE in Ha.
       apply enfa_nfa_ms_lAS in Ha.
       rewrite inE.
       easy.
Qed.


Lemma enfa_eps_cl: forall (e: enfa) (p q: e) (A: {set (@enfa_state e)}) (x: String),
    p \in nfa_multistep (enfa_nfa e) (eps_closure_set e A) x ->
    q \in eps_closure e p ->
    q \in nfa_multistep (enfa_nfa e) (eps_closure_set e A) x.
Proof. intros.
       revert e p q A H H0.
       induction x; intros.
       - simpl in *.
         unfold eps_closure_set in *.
         move=>/bigcupP in H.
         destruct H as (i, Ha, Hb).
         apply/bigcupP.
         exists i.
         easy.
         unfold eps_closure in *.
         rewrite inE in H0.
         rewrite inE in Hb.
         rewrite inE.
         apply (enfa_connect_l e i p q None Hb H0).
(*          apply(connect_trans Hb H0). *)
       - simpl in *.
         move=>/bigcupP in H.
         destruct H as (i, Ha, Hb).
         move=>/bigcupP in Hb.
         destruct Hb as (j, Hb, Hc).
         move=>/bigcupP in Hc.
         destruct Hc as (m, Hc, Hd).
         rewrite inE in Hc.
         
         apply/bigcupP.
         exists i.
         easy.
         apply/bigcupP.
         exists j.
         easy.
         apply/bigcupP.
         exists m.
         rewrite inE.
         easy.
         unfold eps_closure in H0, Hd.
         rewrite inE in H0.
         rewrite inE in Hd.
         unfold eps_closure.
         rewrite inE.
         apply (enfa_connect_l e m p q None Hd H0).
(*          apply (connect_trans Hd H0). *)
Qed.

Lemma enfa_nfa_ms_eq: forall (e: enfa) (A: {set (@enfa_state e)}) (x: String),
  enfa_multistep e A x =
  nfa_multistep (enfa_nfa e) (eps_closure_set e A) x.
Proof. intros e A x.
       revert e A.
       induction x; intros.
       - easy.
       - simpl in *.
         specialize (IHx e A).
         apply/setP.
         move => y. apply/idP/idP => /=.
         intro H.
         move=>/bigcupP in H.
         destruct H as (p, Ha, Hb).
         apply/bigcupP.
         exists p.
         rewrite <- IHx.
         easy.
         move=>/bigcupP in Hb.
         destruct Hb as (q, Hb, Hc).
         rewrite inE in Hb.
         apply/bigcupP.
         exists p.
         unfold eps_closure_set.
         apply/bigcupP.
         exists p.
         rewrite inE. easy.
         unfold eps_closure.
         rewrite inE.
         apply epsa.
(*          apply connect0. *)
         
         apply/bigcupP.
         exists q.
         rewrite inE.
         easy.
         easy.

         intro H.
         move=>/bigcupP in H.
         destruct H as (p, Ha, Hb).
         move=>/bigcupP in Hb.
         destruct Hb as (q, Hb, Hc).
         move=>/bigcupP in Hc.
         destruct Hc as (i, Hc, Hd).
         rewrite inE in Hc.
        
         apply/bigcupP.
         exists q.
         rewrite IHx.
        
         unfold eps_closure_set in Hb.
         move=>/bigcupP in Hb.
         destruct Hb as (j, Hb, He).
         apply enfa_eps_cl with (p := p).
         easy.
         rewrite inE in Hb.
         move=>/eqP in Hb.
         subst.
         easy.
         apply/bigcupP.
         exists i.
         rewrite inE.
         easy.
         easy.
Qed.


Lemma enfa_nfa_acc_eq: forall (e: enfa) (A: {set (@enfa_state e)}) (x: String),
  nfa_acceptance (enfa_nfa e) (eps_closure_set e A) x =
  enfa_acceptance e A x.
Proof. intros.
       unfold enfa_acceptance, nfa_acceptance.
       rewrite enfa_nfa_ms_eq.
       apply/existsP.
       case_eq (
       [exists y,
          (y \in nfa_multistep (enfa_nfa e) (eps_closure_set e A) x) &&
          (y \in [set q | [exists x0, (x0 \in eps_closure e q) && (x0 \in enfa_finals e)]])]
       ); intro HH.
       - rewrite HH.
         move=>/existsP in HH.
         destruct HH as (p, Ha).
         move=>/andP in Ha.
         destruct Ha as (Ha, Hb).
         rewrite inE in Hb.
         move=>/existsP in Hb.
         destruct Hb as (q, Hb).
         move=>/andP in Hb.
         destruct Hb as (Hb, Hc).
         exists q.
         apply/andP.
         split.
         - apply enfa_eps_cl with (p := p).
           easy.
           easy.
         - simpl.
           rewrite inE.
           apply/existsP.
           exists q.
           apply/andP.
           split.
           + unfold eps_closure.
             rewrite inE.
             apply epsa.
(*              apply connect0. *)
           + easy.
       - rewrite HH.
         unfold not.
         intro H.
         move=>/existsP in HH.
         unfold not in HH.
         apply HH.
         destruct H as (p, Ha).
         move=>/andP in Ha.
         destruct Ha as (Ha, Hb).
         exists p.
         apply/andP.
         split.
         - easy.
         - rewrite inE.
           apply/existsP.
           simpl in Hb.
           rewrite inE in Hb.
           move/existsP in Hb.
           destruct Hb as (i, Hb).
           exists i.
           easy.
Qed.

Lemma enfa_nfa_lang_eqiA: forall n, enfa_language n =i nfa_language (enfa_nfa n).
Proof. intros.
       unfold enfa_language, nfa_language.
       move => y. apply/idP/idP => /=.
       intro Ha.
       rewrite inE in Ha.
       rewrite inE.
       rewrite enfa_nfa_acc_eq.
       easy.
       intro Ha.
       rewrite inE in Ha.
       rewrite inE.
       rewrite <- enfa_nfa_acc_eq.
       easy.
Qed.
