(* 

See example.v first.

This is an example of integrating YADE with the categorical library 
of Hierarchy Builder.
We prove that a distributive law between two monads
induce an associative multiplication on the composition of the functors.

 *)

Require Import ssreflect.
Unset Universe Checking.

(* The categorical library of Hierarchy builder *)
From Yade Require Import cat.
(* These are some convenient tactics for category theory *)
From Yade Require Import cattactic.
Require Yade.yade.
Import yade.notations.
Set Typeclasses Unique Instances.

Generalizable All Variables.
Open Scope cat.


(* Nice right associative notations for functor applications *)
Notation "x y" := (Functor.sort x y) (in custom yade_ob at level 1, right associativity).
Notation "x y" := (x <$> y)  (in custom yade_mor at level 1, right associativity).

Section Distributive.



Context
 {C : cat} (S T : C ~> C)
   (μS : S \; S ~> S)
   (μT : T \; T ~> T).
   (* we omit the units *)

Notation "μ^S x" := (μS x) (x custom yade_ob, in custom yade_mor at level 1).
Notation "μ^T x" := (μT x) (x custom yade_ob, in custom yade_mor at level 1).

Instance yadeCat {C : cat} : yade.preCategory C hom :=
             {| 
                        yade.compose := fun _ _ _ f g => f \; g;
                        yade.assoc := fun a b c d f g h => compoA f g h;
                         |}.
             

Context (muS_assoc : forall x, <YADE> μ^S S x  · μ^S x = S μ^S x · μ^S x </YADE>).
Context (muT_assoc : forall x, <YADE> μ^T T x  · μ^T x = T μ^T x · μ^T x </YADE>).
(*
 YADE DIAGRAM {"fileName":"graph.json","graph":{"latexPreamble":"\\newcommand{\\coqproof}[1]{\\checkmark{}}","tabs":[{"active":true,"edges":[{"from":1,"id":6,"label":{"isPullshout":false,"label":"μ^S S x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":2},{"from":2,"id":7,"label":{"isPullshout":false,"label":"μ^S x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":3},{"from":1,"id":8,"label":{"isPullshout":false,"label":"S μ^S x","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":4},{"from":4,"id":9,"label":{"isPullshout":false,"label":"μ^S x","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":3}],"nodes":[{"id":0,"label":{"isMath":true,"label":"T S x","pos":[1300,700],"zindex":1}},{"id":1,"label":{"isMath":true,"label":"S S S x","pos":[100,100],"zindex":0}},{"id":2,"label":{"isMath":true,"label":"S S x","pos":[300,100],"zindex":-10000}},{"id":3,"label":{"isMath":true,"label":"S x","pos":[300,300],"zindex":-10000}},{"id":4,"label":{"isMath":true,"label":"S S x","pos":[100,300],"zindex":0}},{"id":5,"label":{"isMath":false,"label":"\\verb|muS_assoc|","pos":[155.0066738128662,184.79605674743652],"zindex":0}}],"sizeGrid":200,"title":"1"}]},"version":11}
 *)

Context (delta : T \; S ~> S \; T ).
Notation "'δ' x" := (delta x) (x custom yade_ob, in custom yade_mor at level 1).
(*
 YADE DIAGRAM {"fileName":"graph.json","graph":{"latexPreamble":"\\newcommand{\\coqproof}[1]{\\checkmark{}}","tabs":[{"active":true,"edges":[{"from":1,"id":13,"label":{"isPullshout":false,"label":"δ T x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":5},{"from":5,"id":14,"label":{"isPullshout":false,"label":"T δ x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":3},{"from":1,"id":15,"label":{"isPullshout":false,"label":"S μ^T x","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":4},{"from":3,"id":16,"label":{"isPullshout":false,"label":"μ^T S x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":2},{"from":4,"id":17,"label":{"isPullshout":false,"label":"δ x","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":2},{"from":6,"id":18,"label":{"isPullshout":false,"label":"S δ x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":10},{"from":10,"id":19,"label":{"isPullshout":false,"label":"δ S x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":8},{"from":6,"id":20,"label":{"isPullshout":false,"label":"μ^S T x","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":9},{"from":8,"id":21,"label":{"isPullshout":false,"label":"T μ^S x","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":7},{"from":9,"id":22,"label":{"isPullshout":false,"label":"δ x","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":7}],"nodes":[{"id":0,"label":{"isMath":true,"label":"T S x","pos":[900,700],"zindex":1}},{"id":1,"label":{"isMath":true,"label":"S T T x","pos":[100,500],"zindex":1}},{"id":2,"label":{"isMath":true,"label":"T S x","pos":[500,700],"zindex":1}},{"id":3,"label":{"isMath":true,"label":"T T S x","pos":[500,500],"zindex":1}},{"id":4,"label":{"isMath":true,"label":"S T x","pos":[100,700],"zindex":1}},{"id":5,"label":{"isMath":true,"label":"T S T x","pos":[300,500],"zindex":1}},{"id":6,"label":{"isMath":true,"label":"S S T x","pos":[100,100],"zindex":1}},{"id":7,"label":{"isMath":true,"label":"T S x","pos":[500,300],"zindex":1}},{"id":8,"label":{"isMath":true,"label":"T S S x","pos":[500,100],"zindex":1}},{"id":9,"label":{"isMath":true,"label":"S T x","pos":[100,300],"zindex":1}},{"id":10,"label":{"isMath":true,"label":"S T S x","pos":[300,100],"zindex":1}},{"id":11,"label":{"isMath":false,"label":"\\verb|muS_delta|","pos":[260.0066738128662,189.79605674743652],"zindex":0}},{"id":12,"label":{"isMath":false,"label":"\\verb|muT_delta|","pos":[263.0066738128662,565.9718322753906],"zindex":0}}],"sizeGrid":200,"title":"1"}]},"version":11}
 *)
Context (muT_delta : forall (x : C), 
  <YADE> δ T x · T δ x · μ^T S x = S μ^T x · δ x </YADE>).
Context (muS_delta : forall (x : C), 
   <YADE> S δ x · δ S x · T μ^S x = μ^S T x · δ x </YADE>).


(* Some convenient notations *)

Notation "< t >" := (t) (t custom yade_mor at level 1, only parsing).
Notation "| t |" := (t) (t custom yade_ob at level 1, only parsing).

(* The candidate  *)
Definition μ' (x : C) : |T S T S x| ~> |T S x| .
exact <  T δ S x · μ^T S S x · T μ^S x >.
Defined.



Lemma μ'_assoc (x : C) :
  <YADE> T S {μ'  x} · {μ' x} = {μ' |T S x|} · {μ' x}
   </YADE>.
Proof.
unfold μ'.
cbn.
rewrite !Fcomp.
rewrite !compoA.

 (*
 YADE DIAGRAM {"graph":{"activeTabId":0,"latexPreamble":"\\newcommand{\\coqproof}[1]{\\checkmark}","nextTabId":1,"tabs":[{"edges":[{"from":0,"id":28,"label":{"label":"T S T δ S x","style":[],"zindex":0},"to":4},{"from":4,"id":29,"label":{"label":"T S μ^T S S x","style":[],"zindex":0},"to":5},{"from":5,"id":30,"label":{"label":"T S T μ^S x","style":[],"zindex":0},"to":2},{"from":0,"id":31,"label":{"label":"T δ S T S x","style":["alignment right"],"zindex":0},"to":6},{"from":6,"id":32,"label":{"label":"μ^T S S T S x","style":["alignment right"],"zindex":0},"to":7},{"from":7,"id":33,"label":{"label":"T μ^S T S x","style":["alignment right"],"zindex":0},"to":3},{"from":2,"id":34,"label":{"label":"T δ S x","style":[],"zindex":0},"to":8},{"from":8,"id":35,"label":{"label":"μ^T S S x","style":[],"zindex":0},"to":9},{"from":9,"id":36,"label":{"label":"T μ^S x","style":[],"zindex":0},"to":1},{"from":3,"id":37,"label":{"label":"T δ S x","style":["alignment right"],"zindex":0},"to":10},{"from":10,"id":38,"label":{"label":"μ^T \nS S x","style":["alignment right"],"zindex":0},"to":11},{"from":11,"id":39,"label":{"label":"T μ^S x","style":["alignment right"],"zindex":0},"to":1},{"from":7,"id":40,"label":{"label":"T S δ S x","style":[],"zindex":0},"to":13},{"from":13,"id":41,"label":{"label":"T δ S S x","style":[],"zindex":0},"to":14},{"from":14,"id":42,"label":{"label":"T T μ^S S x","style":[],"zindex":0},"to":10},{"from":14,"id":43,"label":{"label":"μ^T S S S x","style":[],"zindex":0},"to":15},{"from":15,"id":44,"label":{"label":"T μ^S S x","style":[],"zindex":0},"to":11},{"from":15,"id":45,"label":{"label":"T S μ^S x","style":[],"zindex":0},"to":9},{"from":17,"id":46,"label":{"label":"T T S μ^S x","style":[],"zindex":0},"to":8},{"from":17,"id":47,"label":{"label":"μ^T S S S x","style":[],"zindex":0},"to":15},{"from":6,"id":48,"label":{"label":"T T S δ S x","style":[],"zindex":0},"to":19},{"from":19,"id":49,"label":{"label":"μ^T S T S S x","style":[],"zindex":0},"to":13},{"from":4,"id":50,"label":{"label":"T δ T S S x","style":[],"zindex":0},"to":19},{"from":19,"id":51,"label":{"label":"T T δ S S x","style":[],"zindex":0},"to":23},{"from":23,"id":52,"label":{"label":"μ^T \n T S S S x","style":[],"zindex":0},"to":14},{"from":23,"id":53,"label":{"label":"T μ^T S S S x","style":[],"zindex":0},"to":17},{"from":5,"id":54,"label":{"label":"T δ S S x","style":[],"zindex":0},"to":17}],"id":0,"nextGraphId":55,"nodes":[{"id":0,"label":{"flags":[],"label":"T S T S T S x","pos":[98,98],"zindex":0}},{"id":1,"label":{"flags":[],"label":"T S x","pos":[686,686],"zindex":0}},{"id":2,"label":{"flags":[],"label":"T S T S x","pos":[686,98],"zindex":0}},{"id":3,"label":{"flags":[],"label":"T S T S x","pos":[98,686],"zindex":0}},{"id":4,"label":{"flags":[],"label":"T S T T S S x","pos":[294,98],"zindex":0}},{"id":5,"label":{"flags":[],"label":"T S T S S x","pos":[490,98],"zindex":0}},{"id":6,"label":{"flags":[],"label":"T T S S T S x","pos":[98,294],"zindex":0}},{"id":7,"label":{"flags":[],"label":"T S S T S x","pos":[98,490],"zindex":0}},{"id":8,"label":{"flags":[],"label":"T T S S x","pos":[686,294],"zindex":0}},{"id":9,"label":{"flags":[],"label":"T S S x","pos":[686,490],"zindex":0}},{"id":10,"label":{"flags":[],"label":"T T S S x","pos":[294,686],"zindex":0}},{"id":11,"label":{"flags":[],"label":"T S S x","pos":[490,686],"zindex":0}},{"id":12,"label":{"flags":["coqValidated"],"label":"\\coqproof{applyeq muS_delta. }","pos":[134.51692724227905,623.2842712402344],"zindex":0}},{"id":13,"label":{"flags":[],"label":"T S T S S x","pos":[163.33333333333331,555.3333333333334],"zindex":0}},{"id":14,"label":{"flags":[],"label":"T T S S S x","pos":[323.0066738128662,574.0304260253906],"zindex":0}},{"id":15,"label":{"flags":[],"label":"T S S S x","pos":[487.0066738128662,563.9024658203125],"zindex":0}},{"id":16,"label":{"flags":["coqValidated"],"label":"\\coqproof{applyeq muS_assoc. }","pos":[591.0066738128662,621.138916015625],"zindex":0}},{"id":17,"label":{"flags":[],"label":"T T S S S x","pos":[532.0066738128662,365.6550626754761],"zindex":0}},{"id":18,"label":{"flags":["coqValidated"],"label":"\\coqproof{applyeq (natural μT).}","pos":[594.0066738128662,427.91324615478516],"zindex":0}},{"id":19,"label":{"flags":[],"label":"T T S T S S x","pos":[263.0066738128662,295.91324615478516],"zindex":0}},{"id":20,"label":{"flags":["coqValidated"],"label":"\\coqproof{applyeq (natural μT).}","pos":[165.0066738128662,405.0260772705078],"zindex":0}},{"id":21,"label":{"flags":[],"label":"\\coqproof{applyeq (natural delta).}","pos":[191.0066738128662,187.6376724243164],"zindex":0}},{"id":22,"label":{"flags":["coqValidated"],"label":"\\coqproof{apply (natural μT).}","pos":[284.0066738128662,469.9718322753906],"zindex":0}},{"id":23,"label":{"flags":[],"label":"T T T S S S x","pos":[385.0066738128662,388.91324615478516],"zindex":0}},{"id":24,"label":{"flags":["coqValidated"],"label":"\\coqproof{applyeq muT_assoc.}","pos":[420.0066738128662,472.8894348144531],"zindex":0}},{"id":25,"label":{"flags":["coqValidated"],"label":"\\coqproof{applyeq muT_delta.}","pos":[426.0066738128662,243.84595301747322],"zindex":0}},{"id":26,"label":{"flags":["coqValidated"],"label":"\\coqproof{applyeq (natural delta).}","pos":[598.0066738128662,212.79605674743652],"zindex":0}},{"id":27,"label":{"flags":["coqValidated"],"label":"\\coqproof{ applyeq (natural μT).}","pos":[398.5033369064331,627.4832229614258],"zindex":0}}],"sizeGrid":136,"title":"2"}]},"version":17}

 The proof below was generated from the above diagram.
 *)
change (<YADE> T S T δ S x · T S μ^T S S x · T S T μ^S x · T δ S x · μ^T S S x · T μ^S x = T δ S T S x · μ^T S S T S x · T μ^S T S x · T δ S x · μ^T 
S S x · T μ^S x </YADE>).

eapply yade.transitivity.
yade_strip 2 2.
refine (_ :> <YADE> T S T μ^S x · T δ S x = T δ S S x · T T S μ^S x </YADE>).
{
  applyeq (natural delta).
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 1 3.
refine (_ :> <YADE> T S μ^T S S x · T δ S S x = T δ T S S x · T T δ S S x · T μ^T S S S x </YADE>).
{
  applyeq muT_delta.
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 0 5.
refine (_ :> <YADE> T S T δ S x · T δ T S S x = T δ S T S x · T T S δ S x </YADE>).
{
  applyeq (natural delta).
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 4 1.
refine (_ :> <YADE> T T S μ^S x · μ^T S S x = μ^T S S S x · T S μ^S x </YADE>).
{
  applyeq (natural μT).
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 5 0.
refine (_ :> <YADE> T S μ^S x · T μ^S x = T μ^S S x · T μ^S x </YADE>).
{
  applyeq muS_assoc. 
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 3 2.
refine (_ :> <YADE> T μ^T S S S x · μ^T S S S x = μ^T 
 T S S S x · μ^T S S S x </YADE>).
{
  applyeq muT_assoc.
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 4 1.
refine (_ :> <YADE> μ^T S S S x · T μ^S S x = T T μ^S S x · μ^T 
S S x </YADE>).
{
   applyeq (natural μT).
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 2 3.
refine (_ :> <YADE> T T δ S S x · μ^T 
 T S S S x = μ^T S T S S x · T δ S S x </YADE>).
{
  apply (natural μT).
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 1 4.
refine (_ :> <YADE> T T S δ S x · μ^T S T S S x = μ^T S S T S x · T S δ S x </YADE>).
{
  applyeq (natural μT).
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 2 2.
refine (_ :> <YADE> T S δ S x · T δ S S x · T T μ^S S x = T μ^S T S x · T δ S x </YADE>).
{
  applyeq muS_delta. 
}
repeat rewrite -> yade.assoc''.

 reflexivity.
Qed.
 


End Distributive.