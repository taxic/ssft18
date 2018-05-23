-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Lecture 2: Representing Logics and Programming Languages in Agda
--
-- File 2: Functional interpretation and consistency of IPL

{-# OPTIONS --allow-unsolved-metas #-}

module Interpretation where

open import Library
open import IPL

-- Interpretation of formulas as sets (types)

-- We assume an interpretation of the atomic propositions.

postulate
  B⦅_⦆ : Base → Set  -- \ ((  codepoint 10629 #x2985  and \ )) codepoint 10630 #x2986

-- Formulas are interpreted recursively according to the
-- Curry-Howard-isomorphism (CHI).

T⦅_⦆ : (A : Form) → Set
T⦅ Atom P ⦆ = B⦅ P ⦆
T⦅ True ⦆   = ⊤                -- Unit (one-element) set.           -- \ top
T⦅ False ⦆  = ⊥                -- Empty set.                        -- \ bot
T⦅ A ∨ B ⦆  = T⦅ A ⦆ ⊎ T⦅ B ⦆    -- Tagged (disjoint) union of sets.  -- \ uplus
T⦅ A ∧ B ⦆  = T⦅ A ⦆ × T⦅ B ⦆    -- Cartesian product.                -- \ times
T⦅ A ⇒ B ⦆  = T⦅ A ⦆ → T⦅ B ⦆   -- Function space.                   -- \ to

-- This translation embodies the CHI.  It explains a formula as set of its proofs.
-- For instance, the conjunction is translated as Cartesian product, thus, a proof
-- of a conjunction is a pair of proofs for each of the conjuncts.
--
-- The disjunction is translated as tagged union.  The tag says which of the
-- disjuncts is proven by the element.
--
-- The implication is translated as the function space.  Proofs of an implication A ⇒ B
-- are functions mapping proofs of A to proofs of B.
--
-- Since True needs no evidence, it is interpreted as the unit set which is
-- inhabited without condition (and the inhabitant is uninteresting).
--
-- False is interpreted as the empty set, since it has no closed proof
-- (i.e. if there are no assumptions).  Under contradictory assumptions,
-- a proof of False is still constructible.

-- Contexts stand for the conjunction of propositions,
-- thus, are interpreted as products of sets.

C⦅_⦆ : (Γ : Cxt) → Set
C⦅ ε ⦆     = ⊤
C⦅ Γ ∙ A ⦆ = C⦅ Γ ⦆ × T⦅ A ⦆

-- Evidence for the presence of a hypothesis in the context
-- are interpreted as projections from the product.

H⦅_⦆ : ∀{Γ A} (x : Hyp Γ A) (γ : C⦅ Γ ⦆) → T⦅ A ⦆
H⦅ x ⦆ = {!!}

-- Derivations of Γ ⊢ C are interpreted as functions from ⦅Γ⦆ to ⦅C⦆.
-- A derivation of Γ ⊢ C transforms proofs for each of the assumptions in Γ
-- to a proof of C.  In the sense of the Curry-Howard isomorphism, where
-- propositions correspond to sets and their proofs to elements of these
-- sets, the (meta-)implication Γ ⊢ C becomes a function.

D⦅_⦆ : ∀{Γ A} (t : Γ ⊢ A) → C⦅ Γ ⦆ → T⦅ A ⦆
D⦅ t ⦆ = {!!}

-- It is now trivial to prove consistency of IPL.
--
-- Consistency of a logic or theory means that the absurdity is not
-- derivable without assumptions.
--
-- A derivation of ε ⊢ False translates to a function of type ⊤ → ⊥
-- which does not exist.

consistency : (t : ε ⊢ False) → ⊥
consistency t = {!!}

-- This arguments derives consistency of the object logic
-- (i.e., the logic which we study, IPL) directly from the consistency of the
-- meta logic (i.e., the logic in which we perform our study, Agda).

-- By the Gödel imcompleteness proofs, no better method exists;
-- mathematics cannot prove its own consistency (contrary to what Hilbert hoped to prove).

-- However, there are other methods than the functional interpretation which could
-- be regarded more elementary.  For instance, normalization:
--
-- A normal derivation is one constructed by introductions rules and
-- elimination of hypotheses only.  If we can show that every derivable judgement
-- Γ ⊢ C has also a normal derivation, then we have shown consistency,
-- since ε ⊢ False cannot be derived by introductions (False has no introduction rule)
-- nor by elimination of hypotheses (there are no hypotheses).
