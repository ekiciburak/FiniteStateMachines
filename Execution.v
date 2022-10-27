From FA Require Import String DFA NFA NFA2DFA.
From mathcomp Require Import all_ssreflect.


Inductive nfa1_state: Type :=
  | q1: nfa1_state
  | q2: nfa1_state
  | q3: nfa1_state.

Definition nfa1_state_eq (p q: nfa1_state): bool :=
  match (p, q) with
    | (q1, q1) => true
    | (q2, q2) => true
    | (q3, q3) => true
    | (_, _)   => false
  end.

Definition S_to_ord (e: nfa1_state) : 'I_3.
  by apply Ordinal with (match e with q1 => 0 | q2 => 1 | q3 => 2 end); case e.
Defined.

Definition S_of_ord (i:'I_3) : nfa1_state.
  by case i=>m ltm3; apply(match m with 0 => q1 | 1 => q2 | _ => q3 end).
Defined.

Lemma S_cancel: cancel S_to_ord S_of_ord. by case. Defined.

Definition S_eq s1 s2 := S_to_ord s1 == S_to_ord s2.
Definition S_eqP: Equality.axiom S_eq. by do 2 case; constructor. Defined.
Canonical S_eqType := Eval hnf in EqType nfa1_state (EqMixin S_eqP).
Canonical S_choiceType := Eval hnf in ChoiceType nfa1_state (CanChoiceMixin S_cancel).
Canonical S_countType := Eval hnf in CountType nfa1_state (CanCountMixin S_cancel).
Canonical S_finType := Eval hnf in FinType nfa1_state (CanFinMixin S_cancel).


Definition nfa1State: finType.
Proof. exact S_finType. Defined.


Definition nfa1_transition (q: nfa1_state) (x: Sigma): {set nfa1_state}:=
  match (q, x) with
    | (q1, a) => [set q1; q2]
    | (q1, b) => [set q1]
    | (q2, a) => [set q3]
    | (q2, b) => [set q1; q3]
    | (q3, a) => [set q3]
    | (q3, b) => set0
  end.

Definition ex1: nfa.
Proof. unshelve econstructor.
       exact nfa1State.
       exact [set q1].
       exact nfa1_transition.
       exact [set q3].
Defined.

Print ex1.

(* Eval cbn in (nfa_multistepA ex1 [set q1] (glue (glue eps a) b)). *)

Lemma example: (nfa_multistep ex1 [set q1] (glue (glue eps a) b)) = [set q1; q3].
Proof. apply/setP.
       move => x.
       apply/ bigcupP.
       case_eq(x \in [set q1; q3]); intros.
       
       rewrite H.
       apply/ bigcupP.
       simpl.
       apply/ bigcupP.
       exists q2.
       apply/ bigcupP.
       exists q1.
       rewrite !inE.
       easy.
       unfold nfa1_transition.
       rewrite !inE.
       easy.
       unfold nfa1_transition.
       rewrite H. easy.

       rewrite H.
       apply/ bigcupP.
       simpl.
       apply/ bigcupP.
       unfold not.
       intros (y, Ha, F).
       simpl in *.
       move=>/bigcupP in Ha.
       destruct Ha as (z, G, Ha).
       simpl in *.
       
       rewrite inE in G.
       move=>/eqP in G.
       rewrite G in Ha.
       unfold nfa1_transition in Ha.
       rewrite inE in Ha.
       move=>/orP in Ha.
       destruct Ha as [Ha | Ha].
         rewrite inE in Ha.
         move=>/eqP in Ha.
         rewrite Ha in F.
         unfold nfa1_transition in F.
         rewrite inE in F.
         move=>/eqP in F.
         rewrite F in H.
         rewrite inE in H.
         move=>/orP in H.
         destruct H.
         left.
         rewrite inE.
         easy.
         
         rewrite inE in Ha.
         move=>/eqP in Ha.
         rewrite Ha in F.
         unfold nfa1_transition in F.
         rewrite inE in F.
         move=>/orP in F.
         destruct F as [F | F].
           rewrite inE in F.
           move=>/eqP in F.
           rewrite F in H.
           rewrite inE in H.
           move=>/orP in H.
           destruct H.
           left.
           rewrite inE.
           easy.
           
           rewrite inE in F.
           move=>/eqP in F.
           rewrite F in H.
           rewrite inE in H.
           move=>/orP in H.
           destruct H.
           right.
           rewrite inE.
           easy.
Qed. 



Inductive dfa1_state: Type :=
  | dq1: dfa1_state
  | dq2: dfa1_state
  | dq3: dfa1_state.

Definition dfa1_state_eq (p q: dfa1_state): bool :=
  match (p, q) with
    | (dq1, dq1) => true
    | (dq2, dq2) => true
    | (dq3, dq3) => true
    | (_, _)     => false
  end.

Definition D_to_ord (e: dfa1_state) : 'I_3.
  by apply Ordinal with (match e with dq1 => 0 | dq2 => 1 | dq3 => 2 end); case e.
Defined.

Definition D_of_ord (i:'I_3) : dfa1_state.
  by case i=>m ltm3; apply(match m with 0 => dq1 | 1 => dq2 | _ => dq3 end).
Defined.

Lemma D_cancel: cancel D_to_ord D_of_ord. by case. Defined.

Definition D_eq s1 s2 := D_to_ord s1 == D_to_ord s2.
Definition D_eqP: Equality.axiom D_eq. by do 2 case; constructor. Defined.
Canonical D_eqType := Eval hnf in EqType dfa1_state (EqMixin D_eqP).
Canonical D_choiceType := Eval hnf in ChoiceType dfa1_state (CanChoiceMixin D_cancel).
Canonical D_countType := Eval hnf in CountType dfa1_state (CanCountMixin D_cancel).
Canonical D_finType := Eval hnf in FinType dfa1_state (CanFinMixin D_cancel).


Definition dfa1State: finType.
Proof. exact D_finType. Defined.

Definition dfa1_transition (q: dfa1_state) (x: Sigma): dfa1_state :=
  match (q, x) with
    | (dq1, a) => dq1
    | (dq1, b) => dq2
    | (dq2, a) => dq3
    | (dq2, b) => dq3
    | (dq3, a) => dq3
    | (dq3, b) => dq3
  end.

(* Definition ex2 :=
{| dfa_start := dq1; dfa_transition x a := dfa1_transition x a ; dfa_finals := [set dq2] |}. *)

Definition ex2: dfa.
Proof. unshelve econstructor.
       exact dfa1State.
       exact dq1.
       exact dfa1_transition.
       exact [set dq2].
Defined.

Eval hnf in dfa_multistep (nfa_dfa ex1) (nfa_dfa_state ex1 q1) (glue (glue (glue eps a) b) a).

Compute dfa_multistep ex2 dq1 (glue (glue (glue (glue eps a) a) a) b).
