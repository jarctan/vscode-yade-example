(* 
This file explains how to use the vscode coreact-yade editor to 
construct diagrammatic proofs of commutation and generate formal proofs of them.
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Do not import the module yade, only require it *)
Require Import Yade.yade.
(* However you must import the notations submodule *)
Import yade.notations.

Section Example.

Context (C : Type)(hom : C -> C -> Type)
    (compose : forall {a b c}, hom a b -> hom b c -> hom a c)
    (assoc : forall {a b c d} (f : hom a b)(g : hom b c)(h : hom c d),
        compose f (compose g h) = compose (compose f g) h).

Infix "\;" := compose (at level 40, left associativity).  

(* 
To turn the goal into something that YADE can parse, the yade module 
relies on typeclass inference.
 *)
Instance category_from_cat : yade.preCategory C hom:=
{
  compose := @compose;
  assoc := @assoc;
}.



Example generateProof 
  (a a' b b' c c' : C)
  (f : hom a b) (g : hom b c)
  (f' : hom a' b') (g' : hom b' c')
  (m : hom a a') (n : hom b b') (p : hom c c')
  (H' : g \; p = n \; g')
  (H : f \; n = m \; f')
   :
  f \; g \; p = m \; f' \; g'.
Proof.
  (*
   If you move your mouse cursor here with the coq-lsp and
  coreact-yade vscode extensions, a YADE tab with the goal 
  displayed as a commutative diagram (to be proven)
  will be shown. 

  If you move your mouse cursor on the line below starting with 
  YADE DIAGRAM, the diagram that follows will be rendered in the 
  first tab of the YADE diagram.

 YADE DIAGRAM {"graph":{"activeTabId":0,"latexPreamble":"\\newcommand{\\coqproof}[1]{\\checkmark}","nextTabId":1,"tabs":[{"edges":[{"from":0,"id":8,"label":{"label":"f","style":[],"zindex":0},"to":4},{"from":4,"id":9,"label":{"label":"g","style":[],"zindex":0},"to":2},{"from":0,"id":10,"label":{"label":"m","style":["alignment right"],"zindex":0},"to":5},{"from":5,"id":11,"label":{"label":"f'","style":["alignment right"],"zindex":0},"to":3},{"from":2,"id":12,"label":{"label":"p","style":[],"zindex":0},"to":1},{"from":3,"id":13,"label":{"label":"g'","style":["alignment right"],"zindex":0},"to":1},{"from":4,"id":14,"label":{"label":"n","style":[],"zindex":0},"to":3}],"id":0,"nextGraphId":15,"nodes":[{"id":0,"label":{"flags":[],"label":"a","pos":[68,68],"zindex":0}},{"id":1,"label":{"flags":[],"label":"c'","pos":[340,204],"zindex":0}},{"id":2,"label":{"flags":[],"label":"c","pos":[340,68],"zindex":0}},{"id":3,"label":{"flags":[],"label":"b'","pos":[204,204],"zindex":0}},{"id":4,"label":{"flags":[],"label":"b","pos":[204,68],"zindex":0}},{"id":5,"label":{"flags":[],"label":"a'","pos":[68,204],"zindex":0}},{"id":6,"label":{"flags":[],"label":"\\coqproof{apply H.}","pos":[134,133.79165649414062],"zindex":0}},{"id":7,"label":{"flags":[],"label":"\\coqproof{apply H'.}","pos":[269,130.79165649414062],"zindex":0}}],"sizeGrid":136,"title":"3"}]},"version":17}

 The Coq script below was generated from the above YADE diagram.
 The proofs of commutation of the two subdiagrams were saved in the check-marked nodes.
 
 To regenerate the proof:
   1. Move the cursor on the above YADE DIAGRAM line
   2. Click on the button "Duplicate the tab" in the YADE tab
   3. Move the cursor where you want the proof to be inserted.
   4. On the YADE tab, select the full diagram (Ctrl+A) and 
   press 'G' on the keyboard.

 The second step is to avoid the diagram to be overwritten during 
 the third step. Indeed, the first tab is always overwritten with the goal 
 as the mouse cursor moves around.
 *)

change (<YADE> f · g · p = m · f' · g' </YADE>).

eapply yade.transitivity.
yade_strip 1 0.
refine (_ :> <YADE> g · p = n · g' </YADE>).
{
  apply H'.
}
repeat rewrite -> yade.assoc''.

eapply yade.transitivity.
yade_strip 0 1.
refine (_ :> <YADE> f · n = m · f' </YADE>).
{
  apply H.
}
repeat rewrite -> yade.assoc''.

 reflexivity.
Qed.

Section LatexVerbatim.
Context 
  (a : C)
  (f : hom a a).
(* 
The custom entries yade_mor and yade_ob are used to render
the labels of the morphisms and objects in the diagram.
They are rendered with LaTeX (KaTeX) by default.
*)
Notation "\mu" := (f) (in custom yade_mor).
Notation "\theta" := (a) (in custom yade_ob).

Example latexExample : f \; f = f.
Proof.
(* When you move the cursor somewhere, the 
coreact-yade extension turns the goal into something parsable by YADE.
The output format is: a -- f -> b -- g -> c = ...
where f is a morphism from a to b, g is a morphism 
from b to c.
If you want to check the output, you can explicitly call 
the below tactic.
*)
yade.to_notation_with_explicit_objects.
(* 
<YADE_EXPLICIT> \theta --
\mu -> \theta -- \mu -> \theta =
\theta -- \mu -> \theta </YADE_EXPLICIT>
*)
(* To render the labels verbatim in the YADE editor, use the following command. *)
Open Scope yade_verbatim.
(* 
<YADE_EXPLICIT_VERB> \theta --
\mu -> \theta -- \mu -> \theta =
\theta -- \mu ->
\theta </YADE_EXPLICIT_VERB>

If you move your mouse here and check the YADE tab,
you will see the labels rendered verbatim.
*)
Close Scope yade_verbatim.
(* Now LaTeX rendering is used for labels again:
<YADE_EXPLICIT> \theta -- \mu -> b = \theta -- \mu -> b </YADE_EXPLICIT>
*)
Abort.

End LatexVerbatim.

Example constructProof 
  (a a' b b' c c' : C)
  (f : hom a b) (g : hom b c)
  (f' : hom a' b') (g' : hom b' c')
  (m : hom a a') (n : hom b b') (p : hom c c')
  (H' : g \; p = n \; g')
  (H : f \; n = m \; f')
   :
  f \; g \; p = m \; f' \; g'.
Proof.

(*
We explain how the diagrammatic proof of [generateProof] above 
was constructed.

1. Move the cursor below this comment 
   so that the goal is displayed in the YADE tab.
2. In YADE, click on the button 'Duplicate the tab'
3. Add an unamed arrow between "b" and "b'":
   - click on "b" 
   - press the key 'a' 
   - move the mouse close to "b'" and press the key 'a' again
4. Select one of the two subdiagrams:
   - move the mouse inside the subdiagram
   - press the key 'S'
5. Enter the proof:
   - press the key 'v'
   - remove everything in the input box and press the key 'Enter'.
      A Coq snipset will be generated for you to prove the commutation 
      of the subdiagram; the unnamed arrow has become a Coq hole to be inferred.
   - Enter the proof (apply H or apply H') of commutation of the subdiagram in the block { }
5. Validate the proof
   - While your mouse is in the block { } with your proof completed
   - Press Ctrl-Shift-P and enter the command "Complete diagram"
      The diagram gets completed: the unnamed arrow gets correctly named,
      and the proof is saved in a check-marked node. The coq snipset is removed.


You can do the same for the other subdiagram.

Here is a trick to do it faster:
1 select the proof node by clicking on it
2 copy and paste it in the other subdiagram (Ctrl-C, Ctrl-V)
3 rename the new proof node
  - click on the new proof node
  - press the key 'r'
  - enter the new proof (apply H' instead of apply H, or conversely)
4 validate the proof
  - click on the new proof node
  - press the key 'v'
    The check-marked proof node should become green.
  

Remark: For the first proof, we constructed an unnamed arrow manually.
It is not necessary to build the unnamed arrow if the Coq hole is the full 
left hand-side or right hand-side of the equation: in that case,
just select the arrows of the other hand-side and press the key 'v'.

*)

Abort.
End Example.