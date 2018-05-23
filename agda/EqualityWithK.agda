{-# OPTIONS --with-K #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : ∀ (A B : Set) (f : A → B) (x y : A) (eq : x ≡ y) → f x ≡ f y
cong = {!!}

UIP : ∀ (A : Set) (x y : A) (p q : x ≡ y) → p ≡ q
UIP = {!!}
