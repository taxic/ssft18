-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Lecture 2: Representing Logics and Programming Languages in Agda
--
-- File 0: Extraction from Agda's standard library

module Library where

-- open import Data.Unit    public using (⊤)

record ⊤ : Set where

-- open import Data.Empty   public using (⊥; ⊥-elim)

data ⊥ : Set where

⊥-elim : ⊥ → ∀{A : Set} → A
⊥-elim ()

-- open import Data.Product public using (_×_; _,_; proj₁; proj₂; curry; uncurry; <_,_>; ∃; Σ)

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field proj₁ : A
        proj₂ : B proj₁
open Σ public

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

∃ : {A : Set} (B : A → Set) → Set
∃ B = Σ _ B

<_,_> : ∀{A B C : Set} (f : C → A) (g : C → B) → (C → A × B)
< f , g > c = f c , g c

curry : ∀{A B C : Set} (f : A × B → C) → (A → B → C)
curry f a b = f (a , b)

uncurry : ∀{A B C : Set} (f : A → B → C) → (A × B → C)
uncurry f (a , b) = f a b

-- open import Data.Sum     public using (_⊎_; inj₁; inj₂; [_,_]) renaming (map to map-⊎)

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

[_,_] : ∀{A B C : Set} (f : A → C) (g : B → C) → A ⊎ B → C
[ f , g ] (inj₁ a) = f a
[ f , g ] (inj₂ b) = g b

-- open import Function     public using (_∘_; id)

id : ∀{A : Set} → A → A
id x = x

_∘_ : ∀{A B C : Set} (f : B → C) (g : A → B) → A → C
f ∘ g = λ x → f (g x)

-- open import Relation.Binary.PropositionalEquality public using (_≡_; refl; cong; cong₂)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : ∀{A B : Set} (f : A → B) {x y : A} (eq : x ≡ y) → f x ≡ f y
cong f refl = refl

cong₂ : ∀{A B C : Set} (f : A → B → C)
  {a a' : A} (ea : a ≡ a')
  {b b' : B} (eb : b ≡ b') → f a b ≡ f a' b'
cong₂ f refl refl = refl


-- Own auxiliary definitions.

-- This application operation for function is also known as the "S-combinator".

apply : ∀{A B Γ : Set} (f : Γ → A → B) (g : Γ → A) → Γ → B
apply f g = λ x → f x (g x)

cases : ∀{A B C Γ : Set} (f : Γ → A ⊎ B) (g : Γ × A → C) (h : Γ × B → C) → Γ → C
cases f g h = λ x → [ g ∘ (x ,_) , h ∘ (x ,_) ] (f x)

lift-fun : ∀{C D A : Set} (f : C → D) → C × A → D × A
lift-fun f (c , a) = f c , a
