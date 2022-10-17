From FA Require Import String DFA NFA.
From mathcomp Require Import all_ssreflect.

Lemma ms_dist: forall (n: nfa) (A: {set (@nfa_state n) }) (x y: String), 
  nfa_multistep n A (concat x y) = nfa_multistep n (nfa_multistep n A x) y.
Proof. intros n A x y.
       revert n A x.
       induction y; intros.
       - simpl. reflexivity.
       - simpl. rewrite <- IHy.
         reflexivity.
Qed.

Lemma nfa_dfa: forall n: nfa, dfa.
Proof. intro n.
       unshelve econstructor.
       - exact (set_of_finType (@nfa_state n)).
       - cbn. exact (@nfa_start n).
       - intros A S.
         destruct S.
         + exact (nfa_multistep n A (glue eps a)).
         + exact (nfa_multistep n A (glue eps b)).
       - cbn.
(*          exact [set A: {set n} | A :&: (@nfa_finals n) != set0]. *)
         exact [set A:{set n} | [exists x, (x\in A) && (x\in(@nfa_finals n))]].
Defined.

Lemma nfa_dfa_state (n: nfa) (s: n): (@dfa_state (nfa_dfa n)).
Proof. destruct n as (Q, S, D, F).
       cbn in *.
       exact ([set s]).
Defined.

Lemma nfa_dfa_set_state (n: nfa) (s: {set n}): (@dfa_state (nfa_dfa n)).
Proof. destruct n as (Q, S, D, F).
       cbn in *.
       exact s.
Defined.

Lemma nfa_to_dfa_ms: forall s (A: nfa) (x: {set A}),
  nfa_multistep A x s = dfa_multistep (nfa_dfa A) (nfa_dfa_set_state A x) s.
Proof. intro s.
       induction s; intros.
       - simpl.
         destruct A as (Q, S, delta, F).
         simpl. reflexivity.
       - simpl.
         specialize (IHs A).
         destruct A as (Q, S, delta, F).
         simpl in *.
         specialize (IHs x).
         rewrite IHs.
         destruct s0; easy.
Qed.

Lemma nfa_dfa_set_state_eq: forall n A, (nfa_dfa_set_state n A) = A.
Proof. intros.
       destruct n.
       cbn in *.
       easy.
Qed.

Lemma nfa_dfa_acc_eq: forall (n: nfa) (A: {set (@nfa_state n)}) (x: String),
  nfa_acceptance n A x =
  dfa_acceptance (nfa_dfa n) A x.
Proof. intros.
       unfold nfa_acceptance, dfa_acceptance.
       rewrite nfa_to_dfa_ms.
       unfold dfa_finals.
       simpl in *.
       apply/idP/idP => /=.
       intros Ha.
       move=>/existsP in Ha.
       destruct Ha as (y, Ha).
       apply/existsP.
       simpl.
       exists (dfa_multistep (nfa_dfa n) A x).
       apply/andP.
       split.
         move=>/andP in Ha.
         destruct Ha as (Ha, Hb).
         apply/eqP. easy.
         rewrite inE.
         apply/existsP.
         exists y.
         rewrite nfa_dfa_set_state_eq in Ha.
         easy.
        
         intros Ha.
         move=>/existsP in Ha.
         destruct Ha as (y, Ha).
         simpl in *.
         move=>/andP in Ha.
         destruct Ha as (Ha, Hb).
         rewrite inE in Hb.
         move=>/existsP in Hb.
         destruct Hb as (z, Hb).
         move=>/eqP in Ha.
         apply/existsP.
         exists z.
         subst.
         rewrite nfa_dfa_set_state_eq.
         easy.
Qed.

Lemma nfa_dfa_lang_eqi_l: forall n y,
y \in [pred w | [exists y0, 
           (y0 \in nfa_multistep n (nfa_start n) w) && (y0 \in nfa_finals n)]] ->
y  \in [pred w | [exists y0,
           (y0 == dfa_multistep (nfa_dfa n) (nfa_start n) w) &&
           (y0 \in [set A:{set n} | [exists x, (x \in A) && (x \in nfa_finals n)]])]].
Proof. intros n y Ha.
       move=>/existsP in Ha.
       destruct Ha as (x, Ha).
       move=>/andP in Ha.
       destruct Ha as (Ha, Hb).
       apply/existsP.
       specialize (nfa_to_dfa_ms y n (nfa_start n)); intro H.
       destruct n as (Q, S, delta, F).
       simpl in *.
       rewrite <- H.
       exists(nfa_multistep {| nfa_state := Q; nfa_start := S; nfa_transition := delta; nfa_finals := F |} S y).
       apply/andP.
       split.
       + easy.
       + rewrite !inE.
         apply/existsP.
         exists x.
         apply/andP.
         split; easy.
Qed.

Lemma nfa_dfa_lang_eqi_r: forall n y,
y  \in [pred w | [exists y0,
           (y0 == dfa_multistep (nfa_dfa n) (nfa_start n) w) &&
           (y0 \in [set A:{set n} | [exists x, (x \in A) && (x \in nfa_finals n)]])]] ->
y \in [pred w | [exists y0, 
           (y0 \in nfa_multistep n (nfa_start n) w) && (y0 \in nfa_finals n)]].
Proof. intros n y Ha.
       move=>/existsP in Ha.
       destruct Ha as (a, Ha).
       move=>/andP in Ha.
       destruct Ha as (Ha, Hb).
       rewrite !inE in Hb.
       move=>/existsP in Hb.
       specialize (nfa_to_dfa_ms y n (nfa_start n)); intro H.
       apply/existsP.
       destruct n as (Q, S, delta, F).
       simpl in *.
       rewrite H.
       move=>/eqP in Ha.
       rewrite <- Ha.
       easy.
Qed.


Lemma nfa_dfa_lang_eqi: forall n, nfa_language n =i dfa_language (nfa_dfa n).
Proof. intros.
       unfold nfa_language, dfa_language.
       unfold nfa_acceptance, dfa_acceptance.
       move => y. apply/idP/idP => /=.
       - intro Ha.
         apply nfa_dfa_lang_eqi_l.
         easy.
       - intro Ha.
         apply nfa_dfa_lang_eqi_r.
         easy.
Qed.
