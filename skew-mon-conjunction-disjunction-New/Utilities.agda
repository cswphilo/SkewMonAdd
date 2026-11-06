{-# OPTIONS --safe #-}

module Utilities where

open import Data.List
open import Relation.Binary.PropositionalEquality

empty++1 : {A : Set} (xs : List A) {ys : List A} → xs ++ ys ≡ [] → xs ≡ []
empty++1 [] eq = refl

-- Nonempty binary trees preserve the branching of iterated conjunction-right.
data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

-- A family of witnesses with the same shape as the underlying tree.
data All {A : Set} (P : A → Set) : Tree A → Set where
  leaf  : {x : A} → P x → All P (leaf x)
  node : ∀ {t u} (pt : All P t) (pu : All P u) → All P (node t u)

mapAll : {A : Set} {P Q : A → Set}
  → (∀ {x} → P x → Q x)
  → ∀ {xs} → All P xs → All Q xs
mapAll fs (leaf p) = leaf (fs p)
mapAll fs (node pxs pys) = node (mapAll fs pxs) (mapAll fs pys)

map2All : {A : Set} {P Q R : A → Set}
  → (∀ {x} → P x → Q x → R x)
  → ∀ {xs} → All P xs → All Q xs → All R xs
map2All fs (leaf p) (leaf q) = leaf (fs p q)
map2All fs (node pxs pys) (node qxs qys) = node (map2All fs pxs qxs) (map2All fs pys qys)

-- Composition and equality laws for operations on trees of premises.
mapAll-comp : {A : Set} {P Q R : A → Set}
  → {fs : ∀ {x} → P x → Q x} {gs : ∀ {x} → Q x → R x}
  → ∀ {xs} (pxs : All P xs) 
  → mapAll gs (mapAll fs pxs) ≡ mapAll (λ p → gs (fs p)) pxs 
mapAll-comp (leaf x) = refl
mapAll-comp (node pxs pys) = cong₂ node (mapAll-comp pxs) (mapAll-comp pys)

map2All-comp : {A : Set} {P P' Q Q' R : A → Set}
  → {fs : ∀ {x} → P' x → P x} {gs : ∀ {x} → Q' x → Q x} {hs : ∀ {x} → P x → Q x → R x}
  → ∀ {xs} (pxs : All P' xs) (qxs : All Q' xs)
  → map2All hs (mapAll fs pxs) (mapAll gs qxs) ≡ map2All (λ p q → hs (fs p) (gs q)) pxs qxs
map2All-comp (leaf x) (leaf y) = refl
map2All-comp (node pxs pys) (node qxs qys) =
  cong₂ node (map2All-comp pxs qxs) (map2All-comp pys qys)

map2All-Δ : {A : Set} {P R : A → Set}
  → {fs : ∀ {x} → P x → P x → R x}
  → ∀ {xs} (pxs : All P xs)
  → map2All fs pxs pxs ≡ mapAll (λ p → fs p p) pxs
map2All-Δ (leaf x) = refl
map2All-Δ (node pxs pys) =
  cong₂ node (map2All-Δ pxs) (map2All-Δ pys)

map2All-eq1 : {A : Set} {P Q R : A → Set}
  → {f g : ∀ {x} → P x → Q x → R x}
  → (∀ {x} (p : P x) (q : Q x) → f p q ≡ g p q)
  → ∀ {xs} (pxs : All P xs) (qxs : All Q xs)
  → map2All f pxs qxs ≡ map2All g pxs qxs
map2All-eq1 eqs (leaf x) (leaf y) = cong leaf (eqs x y)
map2All-eq1 eqs (node pxs pys) (node qxs qys) =
  cong₂ node (map2All-eq1 eqs pxs qxs) (map2All-eq1 eqs pys qys)

mapAll-eq1 : {A : Set} {P Q : A → Set}
  → {f g : ∀ {x} → P x → Q x}
  → (∀ {x} (p : P x) → f p ≡ g p)
  → ∀ {xs} (pxs : All P xs) 
  → mapAll f pxs ≡ mapAll g pxs
mapAll-eq1 eqs (leaf x) = cong leaf (eqs x)
mapAll-eq1 eqs (node pxs pys) = cong₂ node (mapAll-eq1 eqs pxs) (mapAll-eq1 eqs pys)

-- Context equalities remain propositional.
++ru : {X : Set} (xs : List X) → xs ++ [] ≡ xs
++ru [] = refl
++ru (x ∷ xs) = cong (x ∷_) (++ru xs)

++ass : {X : Set} (xs : List X) {ys zs : List X} → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++ass [] = refl
++ass (x ∷ xs) = cong (x ∷_) (++ass xs)
