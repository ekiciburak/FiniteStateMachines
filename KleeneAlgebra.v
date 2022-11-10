From FA Require Import String.
From mathcomp Require Import all_ssreflect.

Class KA (A: Type) (plus: A -> A -> A) (times: A -> A -> A) (star: A -> A) (zero: A) (one: A): Type :=
 { 
   ax1 : forall a b c, plus a (plus b c) = plus (plus a b) c;
   ax2 : forall a b, plus a b = plus b a;
   ax3 : forall a, plus a a = a;
   ax4 : forall a, plus a zero = a;
   ax5 : forall a, times a zero = zero;
   ax6 : forall a, times zero a = zero;
   ax7 : forall a, times one a = a;
   ax8 : forall a, times a one = a;
   ax9 : forall a b c, times a (times b c) = times (times a b) c;
   ax10: forall a b c, times (plus a b) c = plus (times a c) (times b c);
   ax11: forall a b c, times a (plus b c) = plus (times a b) (times a c);
   leq a b := plus a b = b;
   ax12: forall a, plus one (times a (star a)) = star a;
   ax13: forall a, plus one (times (star a) a) = star a;
   ax14: forall a b c, leq (plus b (times a c)) c -> leq (times (star a) b) c;
   ax15: forall a b c, leq (plus b (times c a)) c -> leq (times b (star a)) c
 }.

(* Definition leq {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {zero: A} {one: A} 
               {s: ISR A plus times zero one} (a b: A) := plus a b = b. *)

Lemma leq_refl: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                       {s: KA A plus times star zero one} (a: A), leq a a.
Proof. intros. 
       unfold leq.
       rewrite ax3.
       reflexivity.
Qed.

Lemma leq_trans: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                        {s: KA A plus times star zero one} (a b c: A), leq a b -> leq b c -> leq a c.
Proof. intros A plus times star zero one s a b c Ha Hb.
       unfold leq in *.
       setoid_rewrite <- Hb at 1.
       rewrite <- Ha in Hb.
       rewrite ax1.
       exact Hb.
Qed.

Lemma leq_antisym: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                          {s: KA A plus times star zero one} (a b: A), leq a b -> leq b a -> a = b.
Proof. intros A plus times star zero one s a b Ha Hb.
       unfold leq in *.
       rewrite <- Ha.
       setoid_rewrite <- Hb at 1.
       rewrite ax2.
       reflexivity.
Qed.


Lemma leq_antisym_eq: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                          {s: KA A plus times star zero one} (a b: A), a = b -> leq a b /\ leq b a.
Proof. intros.
       unfold leq in *.
       subst.
       rewrite ax3.
       easy.
Qed.

Lemma leq_mono_pr: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                          {s: KA A plus times star zero one} (a b x: A), leq a b -> leq (plus a x) (plus b x).
Proof. intros.
       unfold leq in *.
       rewrite ax1.
       setoid_rewrite ax2 at 3.
       setoid_rewrite <- ax1 at 2.
       rewrite H.
       setoid_rewrite ax2 at 2.
       rewrite <- ax1.
       rewrite ax3.
       reflexivity.
Qed.

Lemma leq_mono_pl: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                          {s: KA A plus times star zero one} (a b x: A), leq a b -> leq (plus x a) (plus x b).
Proof. intros.
       unfold leq in *.
       rewrite ax1.
       setoid_rewrite ax2 at 3.
       setoid_rewrite <- ax1 at 2.
       rewrite ax3.
       setoid_rewrite <- ax2 at 2.
       rewrite <- ax1.
       rewrite H.
       reflexivity.
Qed.

Lemma leq_mono_tl: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                          {s: KA A plus times star zero one} (a b x: A), leq a b -> leq (times a x) (times b x).
Proof. intros.
       unfold leq in *.
       rewrite <- ax10.
       rewrite H.
       reflexivity.
Qed.

Lemma leq_mono_tr: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                          {s: KA A plus times star zero one} (a b x: A), leq a b -> leq (times x a) (times x b).
Proof. intros.
       unfold leq in *.
       rewrite <- ax11.
       rewrite H.
       reflexivity.
Qed.

Lemma leq_mono_s: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                         {s: KA A plus times star zero one} (a b: A), leq a b -> leq (star a) (star b).
Proof. intros A plus times star zero one s a b H.
       assert (Ha: leq (times a (star b)) (times b (star b))).
       { apply (@leq_mono_tl A plus times star zero one s a b (star b) H). }
       assert (Hb: leq (plus one (times a (star b))) (plus one (times b (star b)))).
       { apply (@leq_mono_pl A plus times star zero one s (times a (star b)) (times b (star b)) one Ha). }
       specialize (ax12 b); intros HH.
       rewrite HH in Hb.
       specialize (ax14 a one (star b) Hb); intros HHH.
       rewrite ax8 in HHH.
       exact HHH.
Qed.

Lemma leq_mono_pr2: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                           {s: KA A plus times star zero one} (a b x y: A), leq a b -> leq x y -> leq (plus a x) (plus b y).
Proof. intros A plus times star zero one s a b x y Ha Hb.
       unfold leq in *.
       setoid_rewrite ax2 at 3.
       setoid_rewrite <- ax1 at 1.
       setoid_rewrite ax1 at 2.
       rewrite Hb.
       setoid_rewrite ax2 at 2.
       rewrite ax1.
       rewrite Ha.
       reflexivity.
Qed.

Lemma leq_mono_pl2: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                           {s: KA A plus times star zero one} (a b x y: A), leq a b -> leq x y -> leq (plus x a) (plus y b).
Proof. intros A plus times star zero one s a b x y Ha Hb.
       unfold leq in *.
       setoid_rewrite ax2 at 3.
       setoid_rewrite <- ax1 at 1.
       setoid_rewrite ax1 at 2.
       rewrite Ha.
       setoid_rewrite ax2 at 2.
       rewrite ax1.
       rewrite Hb.
       reflexivity.
Qed.

Lemma leq_mono_tl2: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                           {s: KA A plus times star zero one} (a b x y: A), leq a b -> leq x y -> leq (times a x) (times b y).
Proof. intros A plus times star zero one s a b x y Ha Hb.
       unfold leq in *.
       assert (times (plus a b) y = times b y).
       { rewrite Ha. reflexivity. }
       rewrite ax10 in H.
       setoid_rewrite <- H at 2.
       rewrite <- H at 1.
       assert (times a (plus x y) = times a y).
       { rewrite Hb. reflexivity. }
       rewrite ax11 in H0.
       setoid_rewrite <- H0 at 2.
       setoid_rewrite <- ax1.
       reflexivity.
Qed.

Lemma leq_mono_tr2: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                           {s: KA A plus times star zero one} (a b x y: A), leq a b -> leq x y -> leq (times x a) (times y b).
Proof. intros A plus times star zero one s a b x y Ha Hb.
       unfold leq in *.
       assert (times y (plus a b) = times y b).
       { rewrite Ha. reflexivity. }
       rewrite ax11 in H.
       setoid_rewrite <- H at 2.
       rewrite <- H at 1.
       assert (times (plus x y) a = times y a).
       { rewrite Hb. reflexivity. }
       rewrite ax10 in H0.
       setoid_rewrite <- H0 at 2.
       setoid_rewrite <- ax1.
       reflexivity.
Qed.


Lemma bisim: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                    {s: KA A plus times star zero one} (a b x: A), 
                    times a x = times x b -> times (star a) x = times x (star b).
Proof. intros A plus times star zero one s a b x Ha.
       apply leq_antisym_eq in Ha.
       destruct Ha as (Ha, Hb).
       apply leq_antisym.
       - assert (Hc: leq (times a (times x (star b))) (times x (times b (star b)))).
         { specialize (@leq_mono_tl A plus times star zero one s (times a x) (times x b) (star b) Ha); intro HH.
           specialize (ax9 a x (star b)); intro HHH.
           rewrite HHH.
           specialize (ax9 x b (star b)); intro HHHH.
           rewrite HHHH.
           exact HH.
         }
       - assert (Hd: leq (plus x (times a (times x (star b)))) (plus x (times x (times b (star b))))).
         { specialize (@leq_mono_pl A plus times star zero one s 
                                   (times a (times x (star b)))
                                   (times x (times b (star b)))
                                   x Hc); intro HH.
           exact HH.
         }
         specialize (ax8 x); intro HH.
         setoid_rewrite <- HH in Hd at 3.
         rewrite <- ax11 in Hd.
         specialize (ax12 b); intros HHH.
         rewrite HHH in Hd.
         apply ax14 in Hd.
         exact Hd.
       - assert (Hc: leq (times (star a) (times x b)) (times (star a) (times a x))).
         { specialize (@leq_mono_tr A plus times star zero one s (times x b) (times a x) (star a) Hb); intro HH.
           exact HH.
         }
         assert (Hd: leq (plus (times (star a) (times x b)) x) (plus (times (star a) (times a x)) x)).
         { specialize (@leq_mono_pr A plus times star zero one s 
                                    (times (star a) (times x b)) 
                                    (times (star a) (times a x)) x Hc); intros HHH.
           exact HHH.
         }
         specialize (ax7 x); intro HH.
         setoid_rewrite <- HH at 4 in Hd.
         setoid_rewrite ax9 at 2 in Hd.
         rewrite <- ax10 in Hd.
         specialize (ax13 a); intros HHH.
         rewrite ax2 in HHH.
         rewrite HHH in Hd.
         rewrite ax2 in Hd.
         rewrite ax9 in Hd.
         apply ax15 in Hd.
         exact Hd.
Qed.

Lemma sliding: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                      {s: KA A plus times star zero one} (a b: A), 
                      times a (star (times b a)) = times (star (times a b)) a.
Proof. intros A plus times star zero one s a b.
       specialize (bisim (times a b) (times b a) a); intro H.
       rewrite H.
       reflexivity.
       rewrite ax9.
       reflexivity.
Qed.

Lemma ts_st: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                    {s: KA A plus times star zero one} (a: A),
                    (times a (star a)) = times (star a) a.
Proof. intros A plus times star zero one s a.
       specialize (bisim a a a); intro H.
       symmetry.
       apply H.
       reflexivity.
Qed.

Lemma ax14eq: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                        {s: KA A plus times star zero one} (a b: A),
                        leq (times a b) b -> leq (times (star a) b) b.
Proof. intros A plus times star zero one s a b Ha.
       specialize (ax14 a b b); intro H.
       apply H.
       unfold leq in Ha.
       unfold leq.
       rewrite ax2 in Ha.
       rewrite Ha.
       rewrite ax3.
       reflexivity.
Qed.

Lemma ax15eq: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                        {s: KA A plus times star zero one} (a b: A),
                        leq (times b a) b -> leq (times b (star a)) b.
Proof. intros A plus times star zero one s a b Ha.
       specialize (ax15 a b b); intro H.
       apply H.
       unfold leq in Ha.
       unfold leq.
       rewrite ax2 in Ha.
       rewrite Ha.
       rewrite ax3.
       reflexivity.
Qed.

Lemma plus_one_star: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                            {s: KA A plus times star zero one} (a: A),
                            plus one (star a) = star a.
Proof. intros A plus times star zero one s a.
       specialize (ax12 a); intro H.
       rewrite <- H.
       rewrite ax1.
       rewrite ax3.
       reflexivity.
Qed.

Lemma star_double: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                          {s: KA A plus times star zero one} (a: A),
                          (times (star a) (star a)) = star a.
Proof. intros A plus times star zero one s a.
       apply leq_antisym.
       - assert (H: leq (times a (star a)) (star a)).
         { unfold leq.
           specialize (ax12 a); intro H.
           setoid_rewrite <- H at 2.
           rewrite ax2.
           rewrite <- ax1.
           rewrite ax3.
           exact H.
         }
         apply ax14eq in H.
         exact H.
       - unfold leq.
         assert (H: star a = times one (star a)).
         { rewrite ax7. reflexivity. }
         setoid_rewrite H at 1.
         rewrite <- ax10.
         rewrite plus_one_star.
         reflexivity.
Qed.

Lemma star_star_star: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                             {s: KA A plus times star zero one} (a: A),
                             times (star a) (star (star a)) = star a.
Proof. intros A plus times star zero one s a.
       specialize (star_double a); intro H.
       apply leq_antisym_eq in H.
       destruct H as (Ha, Hb).
       specialize (ax15eq (star a) (star a) Ha); intro H.
       unfold leq in H.
       assert (Hc: times (star a) one = star a).
       { rewrite ax8. reflexivity. }
       setoid_rewrite <- Hc in H at 3.
       rewrite <- ax11 in H.
       rewrite ax2 in H.
       rewrite plus_one_star in H.
       exact H.
Qed.

Lemma star_star: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                        {s: KA A plus times star zero one} (a: A),
                        (star (star a)) = star a.
Proof. intros A plus times star zero one s a.
       apply leq_antisym.
       - specialize (star_star_star a); intro Ha.
         apply leq_antisym_eq in Ha.
         destruct Ha as (Ha, Hb).
         specialize (leq_mono_pl (times (star a) (star (star a))) (star a) one Ha); intro H.
         rewrite plus_one_star in H.
         specialize (ax12 (star a)); intro HH.
         rewrite HH in H.
         exact H.
       - specialize (star_star_star a); intro Ha.
         apply leq_antisym_eq in Ha.
         destruct Ha as (Ha, Hb).
         specialize (leq_mono_pl (star a) (times (star a) (star (star a))) one Hb); intro H.
         rewrite plus_one_star in H.
         specialize (ax12 (star a)); intro HH.
         rewrite HH in H.
         exact H.
Qed.

Lemma plus_star_star: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                             {s: KA A plus times star zero one} (a: A),
                             (star (plus one a)) = star a.
Proof. intros A plus times star zero one s a.
       apply leq_antisym.
       - assert (leq one (star a)).
         { unfold leq.
           rewrite plus_one_star.
           reflexivity.
         }
         specialize (leq_mono_tr one (star a) a H); intro HH.
         rewrite ax8 in HH.
         specialize (leq_mono_pl a (times a (star a)) one HH); intro HHH.
         specialize (ax12 a); intro HHHH.
         rewrite HHHH in HHH.
         specialize (leq_mono_s (plus one a) (star a) HHH); intro HHHHH.
         rewrite star_star in HHHHH.
         exact HHHHH.
       - assert (leq a (plus one a)).
         { unfold leq.
           rewrite ax2.
           rewrite <- ax1.
           rewrite ax3.
           reflexivity.
         }
         specialize (leq_mono_s a (plus one a) H); intro HH.
         exact HH.
Qed.

Lemma star_times_star: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                              {s: KA A plus times star zero one} (a: A),
                              (star (times a (star a))) = star a.
Proof. intros A plus times star zero one s a.
       apply leq_antisym.
       - assert (leq (times a (star a)) (star a)).
         { unfold leq.
           specialize (ax12 a); intro H.
           setoid_rewrite <- H at 2.
           rewrite ax2.
           rewrite <- ax1.
           rewrite ax3.
           exact H.
         }
         specialize (leq_mono_s (times a (star a)) (star a) H); intro HH.
         rewrite star_star in HH.
         exact HH.
       - assert (leq (star a) (plus one (times a (star a)))).
         { unfold leq.
           specialize (ax12 a); intro H.
           rewrite H.
           rewrite ax3.
           reflexivity.
         }
         specialize (leq_mono_s (star a) (plus one (times a (star a))) H); intro HH.
         rewrite star_star in HH.
         rewrite plus_star_star in HH.
         exact HH.
Qed.

Lemma denesting: forall {A: Type} {plus: A -> A -> A} {times: A -> A -> A} {star: A -> A} {zero: A} {one: A} 
                        {s: KA A plus times star zero one} (a b: A), 
                        star (plus a b) = times (star a) (star (times b (star a))).
Proof. intros A plus times star zero one s a b.
       apply leq_antisym.
       - assert (plus one (times (plus a b) (times (star a) (star (times b (star a))))) =
                 times (star a) (star (times b (star a)))
                ).
         { rewrite ax10.
           setoid_rewrite <- ax2.
           rewrite <- ax1. 
           setoid_rewrite ax2 at 2.
           setoid_rewrite ax9 at 2.
           specialize (ax12 (times b (star a))); intro HH.
           rewrite HH.
           rewrite ax9.
           assert ((star (times b (star a))) = times one ((star (times b (star a))))).
           { rewrite ax7. reflexivity. }
           setoid_rewrite H at 2. 
           rewrite <- ax10.
           rewrite ax2.
           specialize (ax12 a); intro HHH.
           rewrite HHH.
           reflexivity.
         }
         apply leq_antisym_eq in H.
         destruct H as (Ha, Hb).
         specialize (ax14 (plus a b) one (times (star a) (star (times b (star a))))); intro HH.
         apply HH in Ha.
         rewrite ax8 in Ha.
         exact Ha.
       - assert (Ha: leq a (plus a b)).
         { unfold leq.
           rewrite ax1.
           rewrite ax3.
           reflexivity.
         }
         assert (Hb: leq b (plus a b)).
         { unfold leq.
           rewrite ax2.
           rewrite <- ax1.
           rewrite ax3.
           reflexivity.
         }
         assert (Hc: leq (star a) (star (plus a b))).
         { apply leq_mono_s. exact Ha. }
         assert (Hd: leq (times (star a) b) (times (star (plus a b)) (plus a b)) ).
         { apply leq_mono_tl2.
           exact Hc.
           exact Hb.
         }
         assert (He: leq (times (times (star a) b) (star a)) (times (times (star (plus a b)) (plus a b)) (star (plus a b)))).
         { apply leq_mono_tl2.
           exact Hd.
           exact Hc.
         }
         rewrite <- ax9 in He.
         rewrite <- ax9 in He.
         assert(Hf: leq (times (star a) (star (times b (star a))))
                               (times (star (plus a b)) (star (times (plus a b) (star (plus a b)))))
         ).
         { apply leq_mono_tl2.
           exact Hc.
           apply leq_mono_s.
           apply leq_mono_tl2.
           exact Hb.
           exact Hc.
         }
         rewrite star_times_star in Hf.
         rewrite star_double in Hf.
         exact Hf.
Qed.
