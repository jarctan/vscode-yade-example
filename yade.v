(* 

  Some notations / tactis / definitions / lemmas for the 
  coreact-yade extension
*)

Unset Universe Checking.
From Yade Require Import cat.
Require Import ssreflect.
Local Open Scope cat.

    Lemma F1i : forall (C D : precat)
  (s : Functor.type C D) (a : C),
@idmap _ (s a) = s <$> idmap.
symmetry; apply F1.
Qed.




(*

UniMath notations
*)
Notation identity c := (@idmap _ c).
Notation category := cat.
Notation "a --> b" := (a ~> b) (at level 55).
  (* (at level 99, b at level 200, format "a  -->  b") : cat_scope. *)
(* Notation "'ob' C" := (C : cat) (at level 1). *)
Notation compose := @comp.
Notation id_left := comp1o.
Notation "f · g" := (comp f g)  (at level 40, left associativity).
Notation assoc := compoA.

Definition maponpaths {T1 T2 : Type} (f : T1 -> T2) {t1 t2 : T1}
           (e: t1 = t2) : f t1 = f t2.
Proof.
  intros. induction e. reflexivity.
Defined.

Lemma assoc'
      {C : cat} {a b c d : C} (f : a ~> b)
  (g : b ~> c) (h : c ~> d) :
(f \; g) \; h = f \; (g \; h).
  by rewrite compoA //.
Qed.

Ltac etrans := etransitivity.

Lemma cancel_postcomposition {C : cat}{a b c : C}(f f' : a ~> b)(g : b ~> c) :
     f = f' -> f \; g = f' \; g.
by move => -> //.
Qed.
Lemma cancel_precomposition {C : cat}{a b c : C}(f : a ~> b)(g g' : b ~> c) :
     g = g' -> f \; g = f \; g'.
by move => -> //.
Qed.

Notation idpath := eq_refl.


(*

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.


*)


Declare Custom Entry obj.
Declare Custom Entry mor.

Definition Fob {C D : category} (F : C ~> D) (c : C) : D := F c.

(* Lemma Fob' {A B:Type} (F : A -> B) : A -> B.
Admitted. *)
 (* := nosimpl (F c). *)

Notation "{ x = y }" := (x = y) (x custom mor, y custom mor).
  
  Notation "x y" := (Fob x y) (in custom obj at level 1, right associativity).
  Notation "< x >" := (x) (x custom mor).
  Notation "| x |" := (identity x) (x custom obj, in custom mor).
  Notation "{ x }" := (x) (in custom obj, x constr).
  Notation "{ x }" := (x) (in custom mor, x constr).
  Notation "( x )" := (x) (in custom mor).
  (* If I remove the coercion, then obj and mor are not displayed properly *)
  (* Notation "x y" := ((x : PreFunctor.type _ _) y)  (in custom obj at level 1, right associativity). *)
  
  Notation "x y" := (x <$> y)  (in custom mor at level 1, right associativity).
  Notation "f · g" := (comp f g)  (f custom mor, g custom mor, in custom mor at level 40, left associativity).
  (* Infix "·" := (comp)  (in custom mor at level 40, left associativity). *)
  Notation "x" := x (in custom obj at level 0, x global).
  Notation "x" := x (in custom mor at level 0, x global).
  Notation "| x |" := (x) (x custom obj).

(* *************

This section consists of lemmas and tactics and notations to turn
a statement into something that the graph editor can parse.

Usage:
norm_graph.

********* *)
    Coercion identity' {C : category} (c : C) : hom c c := identity c.


Definition comp' {C : category}{a b c : C} : a --> b -> b --> c -> a --> c := @compose C a b c.
    Lemma add_id_left {C : category} {x y : C}(f g : x -->  y) :   comp' (identity _) f  = comp' (identity _) g -> f = g.
      unfold comp'.
      cbn in x, y.    
      rewrite 2!id_left.
      exact.
    Qed.


    Lemma comp'_comp {C : category}{x1 x2 x3 x4 : C}(a : x3 --> x4)
                        (b : x2  --> x3)
                        (c : x1  --> x2):
                         comp' c  (b · a) = comp' (comp' c b) a .
      unfold comp'.
      apply assoc.
    Qed.
    
    
    #[export] Hint Rewrite <- @F1 : grapheditor.
    #[export] Hint Rewrite  @comp'_comp : grapheditor.
    Ltac norm_graph := apply add_id_left;
       rewrite ?(F1i, comp'_comp);
         (* autorewrite with grapheditor; *)
                       change (identity ?x) with (identity' x);
                       repeat (change ((?K : _ ~>_cat _) ?b) with (Fob K b)).


  Notation " f -- g -> z" := (@comp' _ _ _ z f g )  (z custom obj, in custom mor at level 40, left associativity).


  Ltac duplicate_goal :=
    let x := fresh in
    let y := fresh in
    let h := fresh in
    unshelve (eassert (x := _);
     eassert (y := _);
     eassert (h := x = y);
     exact x).

Ltac functor_cancel F :=
  rewrite <- !(Fcomp (s := F));
  repeat eapply (maponpaths (F ^$) ).

Lemma add_id_left_hyp {C' : category} {x y : C'}(f g : x -->  y) : f = g ->  comp' (identity _) f  = comp' (identity _) g.
      unfold comp'.
      rewrite 2!id_left.
      exact.
    Qed.

Ltac norm_graph_partial :=
  try (change (compose ?f ?g = ?e) with (comp' f g = e));
  try (change (?e = compose ?f ?g ) with (e = comp' f g));
  repeat (change (comp' (compose ?f ?g) ?h) with (comp' (comp' f g) h)).

Ltac norm_graph_hyp h := apply add_id_left_hyp in h;  autorewrite with grapheditor in h;
                       change (identity ?x) with (identity' x) in h;
                       cbn in h.
Ltac naturality := apply natural || (symmetry; apply natural). 
