From FA Require Import String.
From mathcomp Require Import all_ssreflect.


Inductive RegExp: Type :=
  | charE  : Sigma -> RegExp
  | epsE   : RegExp
  | emptyE : RegExp
  | plusE  : RegExp -> RegExp -> RegExp
  | starE  : RegExp -> RegExp
  | concatE: RegExp -> RegExp -> RegExp.

Definition charEq (c1 c2: Sigma): bool :=
  match c1, c2 with
    | a, a => true
    | b, b => true
    | _, _ => false
  end.

Fixpoint ceps (alpha: RegExp): bool :=
  match alpha with
    | charE x       => false
    | epsE          => true
    | emptyE        => false
    | plusE a1 a2   => ceps a1 || ceps a2
    | concatE a1 a2 => ceps a1 && ceps a2
    | starE a1      => true
  end.

Fixpoint derivative (alpha: RegExp) (c: Sigma): RegExp :=
  match alpha with
    | charE x       => if charEq x c then epsE else emptyE
    | epsE          => emptyE
    | emptyE        => emptyE
    | plusE a1 a2   => plusE (derivative a1 c) (derivative a2 c)
    | concatE a1 a2 => if ceps a1 then plusE (concatE (derivative a1 c) a2) (derivative a2 c)
                                  else concatE (derivative a1 c) a2
    | starE a1      => concatE (derivative a1 c) (starE a1)
  end.

Compute (derivative (starE (plusE (charE a) (charE b))) a).
Compute (derivative (starE (plusE (charE a) (charE b))) b).
Compute (derivative (concatE (starE (concatE (starE (charE a)) (charE b))) (starE (charE a))) a).
Compute (derivative (concatE (starE (concatE (starE (charE a)) (charE b))) (starE (charE a))) b).

Fixpoint In (s: String) (alpha: RegExp): bool :=
  match s with
    | eps      => ceps alpha
    | glue x y => In x (derivative alpha y)
  end.

Definition isIn (s: String) (alpha: RegExp): bool :=
  let s := revert s in In s alpha.

Definition regexp_equiv (alpha beta: RegExp) := forall x, isIn x alpha = isIn x beta.

(**-- "aaa" \in a* --*)
Time Compute isIn (glue (glue (glue eps a) a) a) (starE (charE a)).

(**-- "aaa" \in b* --*)
Compute isIn (glue (glue (glue eps a) a) a) (starE (charE b)).

(**-- "abaaa" \in a(a+baa)* --*)
Compute isIn (glue (glue (glue (glue (glue eps a) b) a) a) a)
             (concatE (charE a) 
                      (starE (plusE (charE a) 
                                    (concatE (concatE (charE b) (charE a)) (charE a))))).
                                    
(**-- "aaaba" \in a(a+baa)* --*)
Compute isIn (glue (glue (glue (glue (glue eps a) a) a) b) a)
             (concatE (charE a) 
                      (starE (plusE (charE a) 
                                    (concatE (concatE (charE b) (charE a)) (charE a))))).
                                    
(**-- "aaabaa" \in a(a+baa)* --*)
Compute isIn (glue (glue (glue (glue (glue (glue eps a) a) a) b) a) a)
             (concatE (charE a) 
                      (starE (plusE (charE a) 
                                    (concatE (concatE (charE b) (charE a)) (charE a))))).
                                    
(**-- "aaaba" \in (a*b)*a* --*)
Compute isIn (glue (glue (glue (glue (glue eps a) a) a) b) a)
             (concatE (starE (concatE (starE (charE a)) (charE b))) (starE (charE a))).
