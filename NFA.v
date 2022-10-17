From FA Require Import String DFA.
From mathcomp Require Import all_ssreflect.

Record nfa: Type :=
  mknfa
  {
     nfa_state     :> finType;
     nfa_start     : {set nfa_state};
     nfa_transition: nfa_state -> Sigma -> {set nfa_state};
     nfa_finals    : {set nfa_state}
  }.

Fixpoint nfa_multistep (n: nfa) (A: {set (@nfa_state n) }) (s: String): { set (@nfa_state n) } :=
  match s with
    | eps => A
    | glue x y => \bigcup_(q in (nfa_multistep n A x)) nfa_transition n q y
  end.

(* Definition nfa_acceptance (n: nfa) (A: {set (@nfa_state n) }) (x: String) :=
  nfa_multistep n A x :&: (@nfa_finals n) != set0. *)

Definition nfa_acceptance (n: nfa) (A: {set (@nfa_state n) }) (x: String) :=
[exists y, (y\in(nfa_multistep n A x)) && (y \in (@nfa_finals n))]. 

Definition nfa_language (n: nfa) := [pred s: String | (nfa_acceptance n (@nfa_start n) s)].