From FA Require Import String DFA NFA NFA2DFA eNFA eNFA2NFA eNFA2DFA.
From mathcomp Require Import all_ssreflect.

Definition dfa_intersection (A B: dfa): dfa.
Proof. destruct A as (Q1, s1, delta1, F1).
       destruct B as (Q2, s2, delta2, F2).
       unshelve econstructor.
       - exact (prod_finType Q1 Q2).
       - exact (s1, s2).
       - cbn. intros (p, q) a.
         exact ((delta1 p a), (delta2 q a)).
       - cbn.
       - exact [set x | ((fst x)\in F1) && ((snd x)\in F2)].
Defined.

Definition dfa_is (d1 d2: dfa) (p: @dfa_state d1) (q: @dfa_state d2): 
  @dfa_state (dfa_intersection d1 d2).
Proof. destruct d1, d2.
       exact (p, q).
Defined.

Lemma pair_in: forall {T1 T2: finType} (A: {set T1}) (B: { set T2 }) (a: T1) (b: T2), 
    (a \in A) = true /\ (b \in B) = true ->
    (a, b) \in [set x | ((fst x) \in A) && ((snd x) \in B)] = true. 
Proof. intros T1 T2 A B a b (H1, H2).
       rewrite !inE.
       cbn.
       rewrite H1.
       rewrite H2.
       easy.
Qed.

Lemma dfa_intersection_ms: forall (s: String) (d1 d2: dfa) 
                                  (p: @dfa_state d1) (q: @dfa_state d2),
      (dfa_multistep (dfa_intersection d1 d2) (dfa_is d1 d2 p q) s) = 
      (dfa_is d1 d2 (dfa_multistep d1 p s) (dfa_multistep d2 q s)).
Proof. intro s.
       induction s; intros.
       - cbn. reflexivity.
       - cbn. rewrite IHs.
         destruct d1, d2. cbn.
         reflexivity.
Qed.

Lemma dfa_closedness_intersection: forall (d1 d2: dfa) (s: String),
  dfa_acceptance d1 (@dfa_start d1) s = true  /\ dfa_acceptance d2 (@dfa_start d2) s = true ->
  dfa_acceptance (dfa_intersection d1 d2) (@dfa_start (dfa_intersection d1 d2)) s = true.
Proof. intros.
       unfold dfa_acceptance in *.
       destruct H as (Ha, Hb).
       specialize (dfa_intersection_ms s d1 d2
       (@dfa_start d1) (@dfa_start d2)); intro C.
       destruct d1 as (Q1, s1, delta1, F1).
       destruct d2 as (Q2, s2, delta2, F2).

       simpl in *.
       apply/existsP.


       unfold dfa_is in C.
       rewrite C. simpl in *.
       move=>/existsP in Ha.
       move=>/existsP in Hb.
       destruct Ha as (x, Ha).
       destruct Hb as (y, Hb).
       exists (x, y). 
       apply/andP. split.

       move=>/andP in Ha.
       move=>/andP in Hb.
       destruct Ha as (Ha1, Ha2).
       destruct Hb as (Hb1, Hb2).
       move=>/eqP in Ha1.
       move=>/eqP in Hb1.
       rewrite <- Ha1, <- Hb1.
       easy.

       rewrite inE. simpl.
       move=>/andP in Ha.
       move=>/andP in Hb.
       destruct Ha as (Ha1, Ha2).
       destruct Hb as (Hb1, Hb2).
       apply/andP.
       easy.
Qed.

Definition dfa_complement (A: dfa): dfa.
Proof. destruct A as (Q, s, delta, F).
       unshelve econstructor.
       - exact Q.
       - exact s.
       - intros p a.
         exact (delta p a).
       - exact ([set x | x \in ~: F]).
Defined.

Definition dfa_cs (d: dfa) (p: @dfa_state d): 
  @dfa_state (dfa_complement d).
Proof. destruct d.
       exact p.
Defined.

Lemma dfa_complmenent_ms: forall (s: String) (d: dfa) (p: @dfa_state d),
  dfa_multistep (dfa_complement d) (dfa_cs d p) s = dfa_cs d (dfa_multistep d p s).
Proof. intro s.
       induction s; intros.
       - cbn. easy.
       - cbn. rewrite IHs.
         destruct d. cbn. easy.
Qed.

Lemma complement_in: forall {T: finType} (A: {set T}) (a: T), 
    a \in A = true ->
    a \in [set x | x \in ~:A] = false. 
Proof. intros T A a H.
       rewrite !inE.
       cbv in H.
       cbv. rewrite H.
       easy.
Qed.

Lemma complement_in2: forall {T: finType} (A: {set T}) (a: T), 
    a \in A = true ->
    a \in ~: [set x | x \in ~:A] = true. 
Proof. intros T A a H.
       rewrite !inE.
       cbv in H.
       cbv. rewrite H.
       easy.
Qed.

Lemma dfa_closedness_complement: forall (s: String) (d: dfa),
  dfa_acceptance d (@dfa_start d) s = true -> 
  dfa_acceptance (dfa_complement d) (@dfa_start (dfa_complement d)) s = false.
Proof. intros.
       unfold dfa_acceptance in *.
       specialize (dfa_complmenent_ms s d (@dfa_start d)); intro C.
       destruct d as (Q, st, delta, F).
       unfold dfa_cs in C.
       rewrite C. simpl in *.
       move=>/existsP in H.
       destruct H as (a, Ha).
       move=>/andP in Ha.
       destruct Ha as (Ha1, Ha2).
       apply/existsP.
       unfold not.
       intro H.
       destruct H as (b, Hb).
       move=>/andP in Hb.
       destruct Hb as (Hb1, Hb2).
       move=>/eqP in Ha1.
       move=>/eqP in Hb1.
       rewrite <- Hb1 in Ha1.
       rewrite <- Ha1 in Hb2.
       move=>/setCP in Hb2.
       apply: Hb2.
       specialize (@complement_in2 Q F a Ha2); intros.
       easy.
Qed.

Definition dfa_union (A B: dfa): dfa.
Proof. destruct A as (Q1, s1, delta1, F1).
       destruct B as (Q2, s2, delta2, F2).
       unshelve econstructor.
       - exact (prod_finType Q1 Q2).
       - exact (s1, s2).
       - cbn. intros (p, q) a.
         exact ((delta1 p a), (delta2 q a)).
       - cbn.
       - exact ([set x | ((fst x)\in F1) && ((snd x)\in [set: Q2] )] :|: 
                [set x | ((fst x)\in [set: Q1]) && ((snd x)\in F2)]).
Defined.

Definition dfa_us (d1 d2: dfa) (p: @dfa_state d1) (q: @dfa_state d2): 
  @dfa_state (dfa_union d1 d2).
Proof. destruct d1, d2.
       exact (p, q).
Defined.

Lemma dfa_union_ms: forall (s: String) (d1 d2: dfa) 
                           (p: @dfa_state d1) (q: @dfa_state d2),
      (dfa_multistep (dfa_union d1 d2) (dfa_us d1 d2 p q) s) = 
      (dfa_us d1 d2 (dfa_multistep d1 p s) (dfa_multistep d2 q s)).
Proof. intro s.
       induction s; intros.
       - cbn. reflexivity.
       - cbn. rewrite IHs.
         destruct d1, d2. cbn. reflexivity.
Qed.

Lemma union_in: forall {T: finType} (A: {set T}) (B: { set T }) a, 
     A \subset B -> 
     a \in A -> a \in B = true.
Proof. intros T A B a Hs H.
       specialize (@eqVproper T A B Hs); intros Ha.
       destruct Ha as [Ha | Ha].
       - subst. easy.
       - rewrite <- sub1set in H.
         specialize (@proper1set T B a); intros Hb.
         apply Hb.
         specialize (@eqVproper T [set a] A H); intros Hc.
         destruct Hc as [Hc | Hc].
         + rewrite Hc. easy.
         + specialize (@proper_trans T [set a] A B Hc Ha); intros Hd.
           easy.
Qed.

Lemma union_in_l: forall {T: finType} (A: {set T}) (B: { set T }), 
     (forall a, a \in A) /\ (forall a, a \in B) -> A =i B.
Proof. intros T A B (Ha, Hb).
       move => y. apply/idP/idP => /=.
       intro H.
       apply Hb.
       intro H.
       apply Ha.
Qed.

Lemma union_in_le: forall {T: finType} (A: {set T}) (B: { set T }), 
     [forall a, a \in A] /\ [forall a, a \in B] -> A =i B.
Proof. intros T A B (Ha, Hb).
       move=>/forallP in Ha.
       move=>/forallP in Hb.
       move => y. apply/idP/idP => /=.
       intro H.
       apply Hb.
       intro H.
       apply Ha.
Qed.


Lemma dfa_closedness_union: forall (s: String) (d1 d2: dfa),
  dfa_acceptance d1 (@dfa_start d1) s = true  /\ dfa_acceptance d2 (@dfa_start d2) s = true ->
  dfa_acceptance (dfa_union d1 d2)  (@dfa_start (dfa_union d1 d2)) s = true.
Proof. intros.
       unfold dfa_acceptance in *.
       destruct H as (Ha, Hb).
       specialize (dfa_union_ms s d1 d2
       (@dfa_start d1) (@dfa_start d2)); intro C.
       destruct d1 as (Q1, s1, delta1, F1).
       destruct d2 as (Q2, s2, delta2, F2).
       unfold dfa_is in C.
       rewrite C. simpl in *.
 
       move=>/existsP in Ha.
       move=>/existsP in Hb.
       destruct Ha as (x, Ha).
       move=>/andP in Ha.
       destruct Ha as (Ha1, Ha2).
       destruct Hb as (y, Hb).
       move=>/andP in Hb.
       destruct Hb as (Hb1, Hb2).
       apply/existsP.
       exists (x,y).
       apply/andP.
       split.
       - apply/eqP.
         move=>/eqP in Ha1.
         move=>/eqP in Hb1.
         rewrite Ha1. rewrite Hb1.
         easy.
       - apply/ setUP.
         left.
         rewrite !inE.
         simpl. rewrite Ha2. easy.
Qed.


(* TODO: Formalize closure under concatenation and Kleene star (asterate) *)











