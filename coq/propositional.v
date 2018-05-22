Require Import ssreflect.

(* This is a comment line *)

(* This is how we declare propositional variables *)

Variables A B C:Prop.

Theorem A1: A -> (B -> A).
Proof.
  done.
Qed.

Theorem A2: (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  move => h1.
  move => h2.
  move => h3.
  apply:h1.
  done.
  apply:h2.
  done.
Qed.

Theorem A3: A -> ~~ A.
Proof.
  move => h1.
  move => h2.
  apply:h2.
  done.
Qed.

Theorem A4: False -> A.
Proof.
  move => h1.
  case:h1.
  (* what's this? *)
Qed.

Theorem A5: (A -> B)->(~ B -> ~ A).
Proof.
  move => h1.
  move => h2.
  move => h3.
  apply:h2.
  apply:h1.
  done.
Qed.
(* Exercise *)
(* Abort. *)


Theorem A6: A -> B -> (A /\ B).
Proof.
  move => h0 h1.
  split.
  done.
  done.
Qed.

Theorem A7: (A /\ B) -> A.
Proof.
  move => h0. 
  case:h0.    (* use A6 *)
  done.       (* use A1 *)
Qed.

Theorem A8: (A /\ B) -> B.
Proof.
  move => h0.
  case:h0.
  move => h0 h1.
  done.
Qed.
(* Exercise *)
(* Abort. *)

Theorem A9: A -> (A \/ B).
Proof.
  move => h0.
  left.
  done.
Qed.

Theorem A10: B -> (A \/ B).
Proof.
  move => h0.
  right.
  done.
Qed.
(* Exercise *)
(* Abort. *)

Theorem A11: (A \/ B)->(A -> C)->(B -> C) -> C.
Proof.
  move => h0 h1 h2.
  case:h0.
  done.
  done.
Qed.


(* Exercises *)

Lemma trans : (A -> B) -> (B -> C) -> A -> C.
Proof.
  move => h0 h1 h2.
  apply:h1.
  apply:h0.
  done.
Qed.

(* P <-> Q is a shortcut for (P -> Q) /\ (Q -> P): manipulate it like a
   "/\" *)

Lemma and_sym : A /\ B <-> B /\ A.
Proof.
  split.

  move => h0.
  case:h0.
  move => h0 h1.
  split.
  apply:h1.
  apply:h0.
  
  move => h0.
  case:h0.
  move => h0 h1.
  split.
  apply:h1.
  apply:h0.
Qed.


Lemma or_sym : A \/ B <-> B \/ A.
Proof.
  split.
  move => h0.
  case:h0.
  move => h0.
  right.
  done.
  move => h0.
  left.
  done.

  move => h0.
  case:h0.
  move => h0.
  right.
  done.
  move => h0.
  left.
  done.
 Qed.

Lemma or_not : ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  move => h0.
  case:h0.

  move => h0.
  move => h1.
  case:h0.
  case:h1.
  done.

  move => h0.
  move => h1.
  case:h0.
  case:h1.
  done.
Qed.

Lemma forall_and_not : forall A B, ~ A /\ ~ B <-> ~ (A \/ B).
Proof.
  split.
  move => h0 h1.
  case:h0.
  case:h1.

  move => h0 h1 h2.
  apply:h1.
  done.

  move => h0 h1 h2.
  apply:h2.
  done.

  move => h0.
  split.
  move => h1.
  case:h0.
  left.
  done.

  move => h1.
  case:h0.
  right.
  done.
Qed.

Lemma and_not : ~ A /\ ~ B <-> ~ (A \/ B).
Proof.
  split.
  move => h0 h1.
  case:h0.
  case:h1.

  move => h0 h1 h2.
  apply:h1.
  done.

  move => h0 h1 h2.
  apply:h2.
  done.

  move => h0.
  split.
  move => h1.
  case:h0.
  left.
  done.

  move => h1.
  case:h0.
  right.
  done.
Qed.

Lemma curry : (A /\ B -> C) <-> (A -> B -> C).
Proof.
  split.
  move => h0 h1 h2.
  apply:h0.
  split.
  done.
  done.

  move => h0 h1.
  apply:h0.
  case:(h1).
  done.
  case:h1.
  done.
Qed.

(* More difficult - remember that ":(h)" (instead of ":h") places hypothesis h on the stack, but leaves a copy in the context, to be re-used later *)

Lemma forall_em : forall A, ~~ (A \/ ~A).
Proof.
  move => h0 h1.
  apply forall_and_not in h1.
  destruct h1.
  apply:H0.
  done.
Qed.

Lemma absurd : ~~ (~~ A -> A).
Proof.
  move => h0.
  case:(h0).
  move => h1.
  apply:(h0).
  
  done.
Qed.

Lemma peirce : ~~ (((A -> B) -> A) -> A).
Proof.
  move => h0.
  case:h0.
  move => h0.
  apply:(h0).

Qed.



Lemma em: ~~ (A \/ ~A).
Proof.
  move => h0.
  case:h0.
  destruct.

Qed.