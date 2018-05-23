module HelloWorld where

open import Agda.Builtin.Nat

module Indexed where

  data Vec (A : Set) : Nat → Set where
    vnil : Vec A 0
    vcons : (n : Nat) (x : A) (xs : Vec A n) → Vec A (suc n)

  data Fin : Nat → Set where
    fzero : (n : Nat)             → Fin (suc n)
    fsuc  : (n : Nat) (i : Fin n) → Fin (suc n)

  lookup : (A : Set) (m : Nat) (xs : Vec A m) (i : Fin m) → A
  lookup = ?

{-
module EqualityProofs where

  open import Agda.Builtin.Equality

  data Vec (A : Set) (m : Nat) : Set where
    vnil'  : (p : m ≡ 0) → Vec A m
    vcons' : (n : Nat) (p : m ≡ suc n) (x : A) (xs : Vec A n) →  Vec A m

  data Fin (m : Nat) : Set where
    fzero' : (n : Nat) (p : m ≡ suc n) → Fin m
    fsuc'  : (n : Nat) (p : m ≡ suc n) (i : Fin n) → Fin m

  module MatchRefl where

    lookup : (A : Set) (m : Nat) (xs : Vec A m) (i : Fin m) → A
    lookup = {!!}

{-
  module PatternSynonyms where

    pattern vnil         = vnil'  refl
    pattern vcons n x xs = vcons' n refl x xs
    pattern fzero n      = fzero' n refl
    pattern fsuc  n i    = fsuc'  n refl i

    lookup : (A : Set) (m : Nat) (xs : Vec A m) (i : Fin m) → A

-- -}
-- -}
-- -}
-- -}
