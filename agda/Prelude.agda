-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Lecture 1: Introduction to Agda
--
-- File 1: The Curry-Howard Isomorphism

{-# OPTIONS --allow-unsolved-metas #-}

module Prelude where

-- Natural numbers as our first example of
-- an inductive data type.

data ℕ : Set where -- set-input-method \bN
  zero : ℕ
  suc  : (n : ℕ) → ℕ

-- To use decimal notation for numerals, like
-- 2 instead of (suc (suc zero)), connect it
-- to the built-in natural numbers.

{-# BUILTIN NATURAL ℕ #-}

-- Lists are a parameterized inductive data type.

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A   -- C-\ : :

infixr 6 _∷_

-- C-c C-l   load

-- Disjoint sum type.

data _⊎_ (S T : Set) : Set where  -- \uplus
  inl : S → S ⊎ T
  inr : T → S ⊎ T

infixr 4 _⊎_

-- The empty sum is the type with 0 alternatives,
-- which is the empty type.
-- By the Curry-Howard-Isomorphism,
-- which views a proposition as the set/type of its proofs,
-- it is also the absurd proposition.

data False : Set where

⊥-elim : False → {A : Set} → A
⊥-elim ()


-- C-c C-SPC give
-- C-c C-, show hypotheses and goal
-- C-c C-. show hypotheses and infers type

-- Tuple types

-- The generic record type with two fields
-- where the type of the second depends on the value of the first
-- is called Sigma-type (or dependent sum), in analogy to
--
--   Σ ℕ A =  Σ   A(n) = A(0) + A(1) + ...
--           n ∈ ℕ

record Σ (A : Set) (B : A → Set) : Set where  -- \GS  \Sigma
  constructor _,_
  field  fst : A
         snd : B fst
open Σ

infixr 5 _,_

-- The non-dependent version is the ordinary Cartesian product.

_×_ : (S T : Set) → Set
S × T = Σ S λ _ → T

infixr 5 _×_

-- The record type with no fields has exactly one inhabitant
-- namely the empty tuple record{}
-- By Curry-Howard, it corresponds to Truth, as
-- no evidence is needed to construct this proposition.

record True : Set where

test : True
test = record {}

-- example: distributivity  a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c)

dist : ∀{a b c : Set} → a × (b ⊎ c) → (a × b) ⊎ (a × c)
dist (a , inl b) = inl (a , b)
dist (a , inr c) = inr (a , c)

-- Relations

-- Type-theoretically, the type of relations 𝓟(A×A) is
--
--   A × A → Prop
--
-- which is
--
--   A × A → Set
--
-- by the Curry-Howard-Isomorphism
-- and
--
--   A → A → Set
--
-- by currying.

Rel : (A : Set) → Set₁
Rel A = A → A → Set

-- Less-or-equal on natural numbers

_≤_ : Rel ℕ
zero ≤ zero = True
zero ≤ suc y = True
suc x ≤ zero = False
suc x ≤ suc y = x ≤ y

-- C-c C-l load
-- C-c C-c case split
-- C-c C-, show goal and assumptions
-- C-c C-. show goal and assumptions and current term
-- C-c C-SPC give
