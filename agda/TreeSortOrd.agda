-- 8th Summer School on Formal Techniques
-- Menlo College, Atherton, California, US
--
-- 21-25 May 2018
--
-- Lecture 1: Introduction to Agda
--
-- File 2: How to Keep Your Neighbours in Order (Conor McBride)

module TreeSortOrd where

open import Prelude

-- Comparing natural numbers

Total : ∀{A} (R : Rel A) → Set
Total R = ∀ x y → R x y ⊎ R y x

pattern le z = inl z
pattern ge z = inr z

compare : Total _≤_
compare = {!!}

-- Extension by a least and a greatest element

data Ext (A : Set) : Set where
  ⊤ : Ext A
  # : A → Ext A
  ⊥ : Ext A

ext : ∀{A} → Rel A → Rel (Ext A)
ext R x y = {!!}

module _ {A : Set} (R : Rel A) (compare : Total R) (let _≤_ = ext R) where

  -- Binary search trees

  data BST (l u : Ext A) : Set where
    leaf : l ≤ u → BST l u
    node : (p : A)
           (lt : BST l (# p))
           (rt : BST (# p) u) → BST l u

  insert : ∀{l u : Ext A} (p : A) (l≤p : l ≤ # p) (p≤u : # p ≤ u)
           (t : BST l u) → BST l u
  insert p l≤p p≤u (leaf l≤u)     = {!!}
  insert p l≤p p≤u (node q lt rt) = {!!}

  -- Building a BST

  tree : (xs : List A) → BST ⊥ ⊤
  tree = {!!}

  -- Ordered lists

  data OList (l u : Ext A) : Set where
    onil  : l ≤ u → OList l u
    ocons : (p : A)
            (l≤p : l ≤ # p)
            (ps : OList (# p) u) → OList l u

  -- Flattening a BST

  _++_ : ∀{l m u}
         (xs : OList l m)
         (ys : ∀{k} (k≤m : k ≤ m) → OList k u) → OList l u
  ocons x l≤x xs ++ ys = {!!}
  onil l≤m       ++ ys = {!!}

  infixr 1 _++_

  flatten : ∀{l u} (t : BST l u) → OList l u
  flatten (leaf l≤u)     = {!!}
  flatten (node p lt rt) = {!!}

  -- Sorting is flatten ∘ tree

  sort : (xs : List A) → OList ⊥ ⊤
  sort xs = flatten (tree xs)
