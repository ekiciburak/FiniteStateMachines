From FA Require Import String DFA NFA NFA2DFA eNFA eNFA2NFA eNFA2DFA Closure.
From mathcomp Require Import all_ssreflect.
Require Import Relations Classes.Equivalence.

Definition Lang := pred String.

Class MNR (L: Lang): Type :=
  mkMNR
  {
    mnr  : relation String;
    rcong: forall (x y: String) (a: Sigma), mnr x y -> mnr (glue x a) (glue y a);
    refin: forall (x y: String), mnr x y -> x \in L <-> y \in L;
    part : finType;
    pmap : String -> part;
    pmapp: forall (x y: String), mnr x y <-> pmap x = pmap y;
    trans: part -> Sigma -> part
  }.

Lemma EquivMNR: forall (L: Lang) (m: MNR L), Equivalence (@mnr L m).
Proof. intros.
       destruct m.
       unshelve econstructor.
       - unfold Reflexive.
         intro x.
         simpl in *.
         apply <- pmapp0.
         reflexivity.
       - unfold Symmetric.
         intros.
         apply <- pmapp0.
         symmetry.
         apply pmapp0.
         simpl in H.
         exact H.
       - unfold Transitive.
         intros.
         apply <- pmapp0.
         pose proof pmapp0 as pmapp.
         simpl in *.
         specialize (pmapp0 x y).
         specialize (pmapp y z).
         edestruct pmapp0.
         rewrite H1.
         edestruct pmapp.
         rewrite H3.
         reflexivity.
         exact H0.
         exact H.
        (*  Unshelve.
         exact a.
         unshelve econstructor. *)
Qed.


Lemma eta {A B C} (f : A -> B -> C) : (fun x y => f x y) = f.
Proof.
cbv. (* I would like to see f = f now *)
reflexivity. (* this proof works in any case, but sometimes syntax matters (rewriting, match...) *)
Defined.

Definition dfa2mnr (d: dfa): MNR (dfa_language d).
Proof. destruct d as (Q, s, delta, F).
       unshelve econstructor.
       - exact (fun x y => dfa_multistep (mkdfa Q s delta F) s x = dfa_multistep (mkdfa Q s delta F) s y).
       - exact Q.
       - intros x.
         exact (dfa_multistep (mkdfa Q s delta F) s x).
       - simpl. intros.
         rewrite H.
         reflexivity.
       - simpl. intros.
         rewrite !inE.
         split.
         unfold dfa_acceptance.
         simpl. intro Ha.
         move=>/existsP in Ha.
         destruct Ha as (z, Ha).
         apply /existsP.
         exists z.
         rewrite <- H.
         exact Ha.

         simpl. intro Ha.
         move=>/existsP in Ha.
         destruct Ha as (z, Ha).
         apply /existsP.
         exists z.
         rewrite H.
         exact Ha.
       - simpl. intros.
         reflexivity.
       - exact delta.
Defined.

Definition mnr2dfa (L: Lang) (R: MNR L): dfa.
Proof. destruct R as (mnr, rcong, refin, part, pmap, pmapp, trans).
       unshelve econstructor.
       - exact part.
       - exact (pmap eps).
       - intros p c.
         exact (trans p c).
       -
Admitted.



