-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Exercise session 1: First definitions and proofs in Agda


-- Cartesian product

infixl 6 _×_  -- \ times

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B
open _×_

-- Swap

swap : ∀{A B : Set} → A × B → B × A
swap = {!!}

-- Function pairing

<_,_> : ∀{A B C : Set} (f : C → A) (g : C → B) → (C → A × B)
<_,_> = {!!}

_×̇_ : ∀{A B C D : Set} (f : A → C) (g : B → D) → (A × B → C × D)  -- \ times \ ^ .
_×̇_ = {!!}

-- Currying and uncurrying

curry : ∀{A B C : Set} (f : A × B → C) → (A → B → C)
curry = {!!}

uncurry : ∀{A B C : Set} (f : A → B → C) → (A × B → C)
uncurry = {!!}


-- Disjoint sums

data _⊎_ (A B : Set) : Set where  -- \ uplus
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Case

[_,_] : ∀{A B C : Set} (f : A → C) (g : B → C) → A ⊎ B → C
[_,_] = {!!}


-- Equality

open import Agda.Builtin.Equality using (_≡_; refl)

-- Symmetry

sym : ∀{A : Set} {x y : A} (eq : x ≡ y) → y ≡ x
sym = {!!}

-- Transitivity

trans : ∀{A : Set} {x y z : A} (eq : x ≡ y) (eq' : y ≡ z) → x ≡ z
trans = {!!}

-- Substitutivity

subst : ∀{A : Set} (P : A → Set) {x y : A} (eq : x ≡ y) (p : P x) → P y
subst = {!!}

-- Congruence

cong : ∀{A B : Set} (f : A → B) {x y : A} (eq : x ≡ y) → f x ≡ f y
cong = {!!}

-- Unicity of identity proofs

UIP : ∀{A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
UIP = {!!}


-- Booleans

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : ∀{A : Set} (b : Bool) (t e : A) → A
if_then_else_ = {!!}

-- Lists

infixr 8 _∷_ _++_

module Lists where

  data List (A : Set) : Set where
    [] : List A
    _∷_ : (x : A) (xs : List A) → List A

  -- append

  _++_ : ∀{A} (xs ys : List A) → List A
  _++_ = {!!}

  -- Monoid laws

  idl : ∀{A} (xs : List A) → [] ++ xs ≡ xs
  idl = {!!}

  idr : ∀{A} (xs : List A) → xs ++ [] ≡ xs
  idr = {!!}

  assoc : ∀{A} (xs {ys zs} : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc = {!!}

  -- Sublists

  data Sublist {A} : (xs : List A) → Set where
    [] : Sublist []
    •∷_ : ∀{xs x} (ys : Sublist xs) → Sublist (x ∷ xs)
    _∷_ : ∀{xs} (y : A) (ys : Sublist xs) → Sublist (y ∷ xs)

  -- Define a function that extras the list, forgetting the sublist property.

  toList : ∀{A} {xs : List A} (ys : Sublist xs) → List A
  toList = {!!}

  -- List filtering

  filter : ∀{A} (f : A → Bool) (xs : List A) → Sublist xs
  filter f xs = {!!}

  -- Sublist concatenation

  append : ∀{A} {xs ys : List A} → Sublist xs → Sublist ys → Sublist (xs ++ ys)
  append = {!!}

-- Natural numbers

open import Agda.Builtin.Nat

-- Show that Nat forms a commutative monoid under addition.

plus-assoc : ∀ x {y z} → (x + y) + z ≡ x + (y + z)
plus-assoc = {!!}

plus-zero : ∀ x → x + 0 ≡ x
plus-zero = {!!}

plus-suc : ∀ x {y} → x + suc y ≡ suc (x + y)
plus-suc = {!!}

plus-comm : ∀ x {y} → x + y ≡ y + x
plus-comm = {!!}


-- Empty type

data ⊥ : Set where

-- Negation

¬_ : (P : Set) → Set  -- \ neg
¬ P = P → ⊥

-- Decidability

data Dec (P : Set) : Set where
  yes : (p  :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

-- Equality of natural numbers is decidable

_≟_ : (n m : Nat) → Dec (n ≡ m)  -- \ ? =
n ≟ m = {!!}


-- Vectors

module Vectors where

  -- Vectors are lists indexed by their length.

  data Vec (A : Set) : Nat → Set where
    [] : Vec A 0
    _∷_ : ∀{n} (x : A) (xs : Vec A n) → Vec A (suc n)

  -- append

  _++_ : ∀{A n m} (xs : Vec A n) (ys : Vec A m) → Vec A (n + m)
  xs ++ ys = {!!}

  -- Associativity of append (already tricky!)

  -- A simple-minded statement of associativity is not well-formed, because the types of
  -- the sides of the equality are formally different.
  --
  --   assoc-++ : ∀{A n m l} (xs : Vec A n) {ys : Vec A m} {zs : Vec A l} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  --
  -- The lhs speaks about Vectors of length ((n + m) + l) while the rhs has (n + (m + l)).
  -- These expressions are not definitionally equal, only provably equal.
  -- We need to convert the type of the lhs using the associativity for Nat.

  -- Congruence lemma for vector-cons:

  cong-∷ : ∀{A n m x} (eqn : n ≡ m) {xs : Vec A n} {ys : Vec A m}
    → subst (Vec A) eqn xs ≡ ys
    → subst (Vec A) (cong suc eqn) (x ∷ xs) ≡ x ∷ ys
  cong-∷ = {!!}

  -- Associativity

  assoc-++ : ∀{A n m l} (xs : Vec A n) {ys : Vec A m} {zs : Vec A l} →
    subst (Vec A) (plus-assoc n) ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  assoc-++ = {!!}

  -- Formulate and prove the identity law  xs ++ [] ≡ xs  for vectors!
  -- (You will need a similar trick than for associativity.)

  -- Can you define a suitable concept of vector equality that
  -- encapsulates the "subst" reasoning here?


-- Advanced exercises:

-- Define an indexed data type of red-black trees that expresses the balancing invariant.
-- This means that by virtue of dependent typing you can never construct an unbalanced tree.

-- Define the rotations for red-black trees.
-- Define an inserting function into red-black trees.

-- Reference:
--   Chris Okasaki:
--   Red-Black Trees in a Functional Setting. J. Funct. Program. 9(4): 471-477 (1999)

-- Further advancing the exercise:
--
-- Add the ordering invariant (as seen in the lecture) to your red-black trees.
