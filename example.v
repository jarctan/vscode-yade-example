Require Import ssreflect.
Unset Universe Checking.
From Yade Require Import cat yade.

Open Scope cat.




Lemma natural_comp_natural {C D : cat} (F G H : C ~> D)
   (m : F ~> G) (n : G ~> H) a b (f : a ~> b):
   {F f · {m b}  · {n b} = {m a} ·  {n a}  · H f}.
   
   cbn.
   
   (* 
      When the cursor is on the below line, the YADE editor should launch and displays it.
      YADE DIAGRAM {"fileName":"graph.json","graph":{"latexPreamble":"\\newcommand{\\coqproof}[1]{\\checkmark{}}","tabs":[{"active":true,"edges":[{"from":0,"id":8,"label":{"isPullshout":false,"label":"F f","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":4},{"from":4,"id":9,"label":{"isPullshout":false,"label":"{m b}","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":2},{"from":0,"id":10,"label":{"isPullshout":false,"label":"{m a}","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":5},{"from":5,"id":11,"label":{"isPullshout":false,"label":"{n a}","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":3},{"from":2,"id":12,"label":{"isPullshout":false,"label":"{n b}","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":1},{"from":3,"id":13,"label":{"isPullshout":false,"label":"H f","style":{"alignment":"right","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":1},{"from":5,"id":14,"label":{"isPullshout":false,"label":"G f","style":{"alignment":"left","bend":0,"color":"black","dashed":false,"double":false,"head":"default","position":0.5,"tail":"none"},"zindex":0},"to":2}],"nodes":[{"id":0,"label":{"isMath":true,"label":"F a","pos":[103,103]}},{"id":1,"label":{"isMath":true,"label":"H b","pos":[309,515]}},{"id":2,"label":{"isMath":true,"label":"G b","pos":[309,309]}},{"id":3,"label":{"isMath":true,"label":"H a","pos":[103,515]}},{"id":4,"label":{"isMath":true,"label":"F b","pos":[309,103]}},{"id":5,"label":{"isMath":true,"label":"G a","pos":[103,309]}},{"id":6,"label":{"isMath":true,"label":"\\coqproof{ apply natural.}","pos":[206,412]}},{"id":7,"label":{"isMath":true,"label":"\\coqproof{ apply natural.}","pos":[206,206]}}],"sizeGrid":206,"title":""}]},"version":10} 
      *)
(* Coq script generated from the above YADE diagram *)
(* Goal { F f · {m b} · {n b} = {m a} · {n a} · H f }. *)

assert(eq : { F f · {m b} = {m a} · G f }).
{
   apply natural.
}
etrans.
{
  apply cancel_postcomposition.
  apply eq.
}
clear eq.
assert(eq : { G f · {n b} = {n a} · H f }).
{
   apply natural.
}
etrans.
{
  repeat rewrite assoc'.
  apply cancel_precomposition.
  repeat rewrite assoc.
  apply eq.
}
repeat rewrite assoc.
clear eq.
 apply idpath.     
Qed.