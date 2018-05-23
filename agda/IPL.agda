-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Lecture 2: Representing Logics and Programming Languages in Agda
--
-- File 1: Intuitionistic Propositional Logic (IPL)

{-# OPTIONS --allow-unsolved-metas #-}

-- In this file, we define formulas of intuitionistic propositional logic
-- and proof terms for the derivability judgement.

-- Note: the comments contain hints how to input unicode characters
-- by the Agda input method.  For instance (don't type the spaces):
--
--   →   -- \ to
--   ∀   -- \ forall
--   Γ   -- \ GG
--   \   -- \ \
--
-- If you know the TeX command, often this works in the Agda input mode
-- as well.

module IPL where

-- We assume a set of propositional variables aka atomic propositions.
-- We have no knowledge about the truth of specific propositions
-- like it is raining.

postulate
  Base : Set

-- Propositional formulas

data Form : Set where
  Atom  : (P : Base) → Form    -- Atomic proposition
  True  : Form                 -- Truth
  False : Form                 -- Absurdity
  _∧_   : (A B : Form) → Form  -- Conjunction   -- \ wedge
  _∨_   : (A B : Form) → Form  -- Disjunction   -- \ vee
  _⇒_   : (A B : Form) → Form  -- Implication   -- \ r 2

-- Negation is defined as "implies absurdity".

¬_ : (A : Form) → Form   -- \ neg
¬ A = A ⇒ False

-- Binding strength of connective in decreasing order

infixr 9 ¬_
infixl 8 _∧_
infixl 7 _∨_
infixr 6 _⇒_

-- The propositional calculus defines how we can derive the truth
-- of a proposition C from a list of hypotheses Γ.
-- C is called the conclusion and Γ is also called the context
-- or the list of assumptions.
--
-- The propositional calculus allows us to make judgments
--
--   Γ ⊢ C
--
-- meaning "if all the assumptions in Γ are true, then C must be true as well".
-- To define this judgement and formal derivations of it, we first
-- formalize hypotheses.

-- Hypotheses are snoc-lists of formulas: most recent assumption is last.
-- ("snoc" is the reversal of "cons" which is the LISP constructor for lists.
-- "cons" adds the new element to the front of the list, where "snoc"
-- adds it to the end.)
--
-- We can also consider hypotheses as stacks of formulas.
-- (However, we use horizontal notation only.)

data Cxt : Set where
  ε : Cxt                           -- Empty list  -- \ G e  ALT: \ epsilon
  _∙_ : (Γ : Cxt) (A : Form) → Cxt  -- Extension   -- \ .   and  \ G G for Γ

infixl 4 _∙_

-- The indexed type Hyp Γ A gives evidence that formula A is element
-- of the list of hypotheses Γ

data Hyp : (Γ : Cxt) (A : Form) → Set where
  top : ∀{Γ A}                 → Hyp (Γ ∙ A) A  -- Found A as the top element.
  pop : ∀{Γ A B} (x : Hyp Γ A) → Hyp (Γ ∙ B) A  -- Remove the top element, search on.

-- Derivations for the judgement Γ ⊢ C

-- These are the proof rules of intuitionistic propositional logic.
-- In type theory, we can define Γ ⊢ C as a set whose inhabitants
-- are the derivations of Γ ⊢ C.

-- Each element of the following list of constructors of Γ ⊢ C
-- represents one proof rule for IPL.  Each rule has a number of premises
-- (in our case, between 0 and 3), and a consequence.
-- For instance, the rule
--
--   Γ ⊢ A    Γ ⊢ B
--   -------------- andI
--   Γ ⊢ A ∧ B
--
-- has two premises, that A is derivable from Γ and B as well, and allows us
-- to conclude that A ∧ B is derivable as well.

-- We distinguish introduction rules, postfixed I, from elimination rules, postfixed E.
-- Introduction rules introduce a logical connective in the consequence, while
-- elimination rules eliminate a logical connective in one of the premises.
--
-- Above rule "andI" is an instance of an introduction rule, it constructs
-- evidence for a conjunction from evidence for each of the conjuncts.
-- An example for an elimination rule is:
--
--   Γ ⊢ A ∧ B
--   --------- andE₁
--   Γ ⊢ A
--
-- It allows us to conclude the derivability of the first conjunct, A, from
-- the derivability of the conjunction A ∧ B.
--
-- If an elimination rule has several premises, we call the one with
-- the eliminated connective the principal premise or main premise,
-- and its formula the principal or main formula, and the connective
-- the principal connective.
--
-- For example:
--
--   Γ ⊢ A ⇒ B    Γ ⊢ A
--   ------------------- impE
--   Γ ⊢ B
--
-- This rule, traditionally called "modus ponens", has principle connective ⇒,
-- principle formula A ⇒ B, and principal premise Γ ⊢ A ⇒ B.
-- The other premise, here, Γ ⊢ A, is called "side premise".
--
-- Some rules add a hypothesis to the context of a premise, for example,
-- the implication introduction rule:
--
--   Γ ∙ A ⊢ B
--   ---------- impI
--   Γ ⊢ A ⇒ B
--
-- This rule states that an implication A ⇒ B is derivable from hypotheses Γ,
-- if its conclusion B is derivable from the extended context Γ ∙ A.
--
-- Let's look at the Agda representation, and get explanations of
-- the remaining rules then.

infix 2 _⊢_  -- \ vdash

data _⊢_ (Γ : Cxt) : (A : Form) → Set where
  hyp    : ∀{A}     (x : Hyp Γ A)               → Γ ⊢ A
  trueI  : Γ ⊢ True
  andI   : ∀{A B}   (t : Γ ⊢ A)     (u : Γ ⊢ B) → Γ ⊢ A ∧ B
  andE₁  : ∀{A B}   (t : Γ ⊢ A ∧ B)             → Γ ⊢ A
  andE₂  : ∀{A B}   (t : Γ ⊢ A ∧ B)             → Γ ⊢ B
  impI   : ∀{A B}   (t : Γ ∙ A ⊢ B)             → Γ ⊢ A ⇒ B
  impE   : ∀{A B}   (t : Γ ⊢ A ⇒ B) (u : Γ ⊢ A) → Γ ⊢ B
  orI₁   : ∀{A B}   (t : Γ ⊢ A)                 → Γ ⊢ A ∨ B
  orI₂   : ∀{A B}   (t : Γ ⊢ B)                 → Γ ⊢ A ∨ B
  orE    : ∀{A B C} (t : Γ ⊢ A ∨ B) (u : Γ ∙ A ⊢ C) (v : Γ ∙ B ⊢ C) → Γ ⊢ C
  falseE : ∀{C}     (t : Γ ⊢ False) → Γ ⊢ C

-- Explanation:
--
-- hyp:    Γ ⊢ A is derivable since A ∈ Γ.
-- trueI:  Truth is trivially derivable (empty conjunction).
-- orI:    If one of the disjuncts is derivable, so is the disjunction.
-- orE:    If a disjunction A ∨ B is derivable, we can use it to derive
--         an arbitrary formula C if we can derive C both from A and from B.
-- falseE: The empty disjunction.  Once we have derived False, everything
--         is true (ex falsum quod libet).

-- Example derivations

-- Conjunction is commutative, i.e., A ∧ B ⇒ B ∧ A
-- holds without assumptions.

andComm : ∀ A B → ε ⊢ A ∧ B ⇒ B ∧ A
andComm A B = {!!}

-- Disjunction is commutative.

orComm : ∀ A B → ε ⊢ A ∨ B ⇒ B ∨ A
orComm A B = {!!}

-- The classical implication implies the constructive one.

impDef : ∀ A B → ε ⊢ (¬ A ∨ B) ⇒ (A ⇒ B)
impDef A B = {!!}


-- -}
-- -}
