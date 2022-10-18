From FA Require Import String DFA NFA NFA2DFA.
From mathcomp Require Import all_ssreflect.


Record enfa: Type :=
  mkenfa
  {
     enfa_state     :> finType;
     enfa_start     : {set enfa_state};
     enfa_transition: enfa_state -> option Sigma -> {set enfa_state};
     enfa_finals    : {set enfa_state};
     epsa           : forall p: enfa_state, p\in enfa_transition p None;
     enfa_connect_l : forall p q r a, q\in enfa_transition p a ->
                                      r\in enfa_transition q None -> 
                                      r\in enfa_transition p a;
     enfa_connect_r : forall p q r a, q\in enfa_transition p None ->
                                      r\in enfa_transition q a -> 
                                      r\in enfa_transition p a
  }.

Definition eps_closure (n: enfa) (p: n) := [set q | q\in enfa_transition n p None].
Definition eps_closure_set (n: enfa)  (A: {set (@enfa_state n) }) := \bigcup_(p in A) eps_closure n p.

Fixpoint enfa_multistep (n: enfa) (A: {set (@enfa_state n) }) (s: String): { set (@enfa_state n) } :=
  match s with
    | eps      => eps_closure_set n A
    | glue x y => \bigcup_(q in enfa_multistep n A x) (eps_closure_set n [set r | r\in enfa_transition n q (Some y)])
  end.

Definition enfa_acceptance (n: enfa) (A: {set (@enfa_state n)}) (x: String) :=
  [exists y, (y \in (enfa_multistep n A x)) && (y \in [set q: n | [exists x, (x \in eps_closure n q) && (x \in enfa_finals n)]])].

Definition enfa_language (n: enfa) := [pred w: String | (enfa_acceptance n (@enfa_start n) w)].

Lemma le_ec: forall (e: enfa) (A: {set (@enfa_state e) }) (q: (@enfa_state e)),
  q \in (eps_closure_set e A) -> (eps_closure e q) \subset (eps_closure_set e A).
Proof. intros.
       unfold eps_closure_set in H.
       move=>/bigcupP in H.
       destruct H as (i, Ha, Hb).
       unfold eps_closure_set.
       apply/subsetP=>z.
       intro Hc.
       apply/bigcupP.
       exists i.
       easy.
       unfold eps_closure in Hb, Hc.
       rewrite inE in Hb.
       rewrite inE in Hc.
       unfold eps_closure.
       rewrite inE.
       apply (enfa_connect_l e i q z None Hb Hc).
Qed.


(* Record enfa: Type :=
  mkenfa
  {
     enfa_state      :> finType;
     enfa_start      : {set enfa_state};
     enfa_transition : option Sigma -> enfa_state -> enfa_state -> bool;
     enfa_finals     : {set enfa_state};
     enfa_connect_l  : forall p q r y, connect (enfa_transition (Some y)) p q /\
                                       connect (enfa_transition None) q r ->
                                       connect (enfa_transition (Some y)) p r;
     enfa_connect_r  : forall p q r y, connect (enfa_transition None) p q /\
                                       connect (enfa_transition (Some y)) q r ->
                                       connect (enfa_transition (Some y)) p r
  }.

Definition eps_closure (n: enfa) (p: n) := [set q | connect (enfa_transition n None) p q].
Definition eps_closure_set (n: enfa)  (A: {set (@enfa_state n) }) := \bigcup_(p in A) eps_closure n p.


Fixpoint enfa_multistep (n: enfa) (A: {set (@enfa_state n) }) (s: String): { set (@enfa_state n) } :=
  match s with
    | eps      => eps_closure_set n A
    | glue x y => \bigcup_(q in enfa_multistep n A x) (eps_closure_set n [set r | connect (enfa_transition n (Some y)) q r])
  end.

Definition enfa_acceptance (n: enfa) (A: {set (@enfa_state n)}) (x: String) :=
  [exists y, (y \in (enfa_multistep n A x)) && (y \in [set q: n | [exists x, (x \in eps_closure n q) && (x \in enfa_finals n)]])].

Definition enfa_language (n: enfa) := [pred w: String | (enfa_acceptance n (@enfa_start n) w)].

Lemma le_ec: forall (e: enfa) (A: {set (@enfa_state e) }) (q: (@enfa_state e)),
  q \in (eps_closure_set e A) -> (eps_closure e q) \subset (eps_closure_set e A).
Proof. intros.
       unfold eps_closure_set in H.
       move=>/bigcupP in H.
       destruct H as (i, Ha, Hb).
       unfold eps_closure_set.
       apply/subsetP=>z.
       intro Hc.
       apply/bigcupP.
       exists i.
       easy.
       unfold eps_closure in Hb, Hc.
       rewrite inE in Hb.
       rewrite inE in Hc.
       unfold eps_closure.
       rewrite inE.
       apply (connect_trans Hb Hc).
Qed.
 *)
