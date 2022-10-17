From FA Require Import String.
From mathcomp Require Import all_ssreflect.

Record dfa: Type :=
    mkdfa
    {
       dfa_state     :> finType;
       dfa_start     : dfa_state;
       dfa_transition: dfa_state -> Sigma -> dfa_state;
       dfa_finals    : {set dfa_state}
    }.

Fixpoint dfa_multistep (d: dfa) (q: dfa_state d) (s: String): dfa_state d :=
  match s with
    | eps      => q
    | glue x y => dfa_transition d (dfa_multistep d q x) y
  end.

Lemma dfa_ms_ss: forall (d: dfa) (s: d) (c: Sigma),
  dfa_transition d s c = dfa_multistep d s (glue eps c).
Proof. intros. simpl. easy. Qed.

Definition dfa_acceptance (d: dfa) (st: @dfa_state d) (s: String): bool :=
  [exists y, (y == (dfa_multistep d st s)) && (y \in (@dfa_finals d))].

Definition dfa_language (d: dfa) := [pred w | dfa_acceptance d (@dfa_start d) w].
