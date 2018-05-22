Require Import ssreflect.

Variables A B C D E:Prop.

Theorem bk: (C->D->E)->A->B->(A->B->C)->(A->B->D)->E.
Proof.
  (* moving the top elements of the stack to the context is reversible *)
  move => h0 h1 h2 h3 h4.
  move: h0 h1 h2 h3 h4.
  (* you can change the order of the stack by unstacking are restacking *)
  move => h0 h1 h2 h3 h4.
  move : h0 h2 h1 h3 h4.
  (* the order of the context doesn't matter at this level: you have labels *)
  move => i0 i1 i2 i3 i4.
  (* Combining restacking and unstacking allows renaming of labels;
     it can even be done in one command: *)
  move: i0 i1 i2 i3 i4 => h0 h1 h2 h3 h4.
  (* ok, let's actually do something *)
  apply:h0.
  apply:h3.
  done.
  done.
  (* ok, now writing 'done' is getting boring.
     I use => // to finish off as many generated subgoals as possible *)
  apply:h4 => //.
Qed.

Theorem bk2: A->(A->B)->B.
Proof.
(* I can group commands together by writing command1 ; command2
   as long as command1 has generated exactly 1 subgoal. *)
  move => h; apply => //.
Qed.

Theorem bk3: A->(A->B/\C)->C/\B.
Proof.
  move => h0 h1; split.
  (* Look, 'case' works 
     even if the conjunction is hidden beneath a series of implications
     a subgoal is generated accordingly, but killed by '=> //' *)
  case:h1 => //.
  (* Alternatively, I can also do some forward reasoning
     and decide to reach my goal by proving the lemma B/\C *)
  have h2: B/\C.
  (* I first have to prove my lemma, 
     while my original goal is saved as subgoal number 2 *)
  apply:h1=>//.
  (* Back to my original goal, my context now features, as a new hypothesis,
     the lemma I've just proved, with the label I've specified *)
  case:h2=>//.
Qed.

Theorem bk4: (A->B)->(B->C)->(C->D)->(D->E)->A->E.
Proof.
move=> i1 i2 i3 i4 h1.
  move: h1 i1 i2 i3 i4.
  move => h0 h1 h2 h3 h4.
  apply:h4.
  apply:h3.
  apply:h2.
  apply:h1.
  apply:h0.
  (* Exercise *)
Qed.

