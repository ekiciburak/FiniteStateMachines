From mathcomp Require Import all_ssreflect.

Inductive Sigma: Type :=
  | a: Sigma
  | b: Sigma.

Inductive String :=
  | eps : String
  | glue: String -> Sigma -> String.

Fixpoint concat (s1 s2: String): String :=
  match s2 with
    | eps => s1
    | glue y x => (glue (concat s1 y) x)
  end.

Fixpoint length (s: String): nat :=
  match s with
    | eps => 0
    | glue y x => S (length y)
  end.

Fixpoint revert (s: String): String :=
  match s with
    | eps      => eps
    | glue x y => concat (glue eps y) (revert x)
  end.

Compute revert (glue (glue (glue eps a) b) b).

Lemma len_distr: forall x y, length (concat x y) = (length x + length y)%nat.
Proof. intros x y.
       revert x.
       induction y; intros.
       - simpl.
         rewrite addn0.
         reflexivity.
       - simpl. rewrite IHy.
         rewrite addnS.
         reflexivity.
Qed.

Lemma lenl: forall s, length s = 0 -> s = eps.
Proof. intro s.
       induction s; intros.
       - simpl. easy.
       - simpl in *. easy.
Qed.

Lemma lenr: forall s, s = eps -> length s = 0.
Proof. intro s.
       induction s; intros.
       - simpl. easy.
       - simpl in *. easy.
Qed.
