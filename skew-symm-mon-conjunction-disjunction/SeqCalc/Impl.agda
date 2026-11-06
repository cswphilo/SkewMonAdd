{-# OPTIONS --safe #-}

module SeqCalc.Impl (At : Set) where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open ≡-Reasoning
open import Utilities hiding (ex-pickR)
open import Formulae At

-- Unfocused calculus with implicit exchange through Pick and Part.

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  pass : ∀ {A Γ Δ C} → Pick A Γ Δ → just A ∣ Δ ⊢ C → - ∣ Γ ⊢ C
  Ir : - ∣ [] ⊢ I
  Il : {Γ : Cxt} → {C : Fma} → 
              - ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗r : ∀ {S Γ Δ Ξ A B} → Part Γ Δ Ξ
    → S ∣ Γ ⊢ A → - ∣ Δ ⊢ B → S ∣ Ξ ⊢ A ⊗ B
  ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C
  ∧r : {S : Stp} → {Γ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → S ∣ Γ ⊢ B → 
              S ∣ Γ ⊢ A ∧ B
  ∧l₁ : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ Γ ⊢ C → 
              just (A ∧ B) ∣ Γ ⊢ C
  ∧l₂ : {Γ : Cxt} → {A B C : Fma} → 
              just B ∣ Γ ⊢ C → 
              just (A ∧ B) ∣ Γ ⊢ C
  ∨r₁ : {S : Stp} → {Γ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → 
              S ∣ Γ ⊢ A ∨ B
  ∨r₂ : {S : Stp} → {Γ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ B → 
              S ∣ Γ ⊢ A ∨ B
  ∨l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ Γ ⊢ C → just B ∣ Γ ⊢ C → 
              just (A ∨ B) ∣ Γ ⊢ C

subst-cxt : ∀ {S Γ Δ C} → Γ ≡ Δ → S ∣ Γ ⊢ C → S ∣ Δ ⊢ C
subst-cxt refl f = f

subst-cxt-cancel : ∀ {S Γ Δ C} (p : Γ ≡ Δ) (f : S ∣ Δ ⊢ C)
  → subst-cxt p (subst-cxt (sym p) f) ≡ f
subst-cxt-cancel refl f = refl

⊗r-subst : ∀ {S Γ Γ' Δ Θ Θ' A B} (e : Γ ≡ Γ') (d : Θ ≡ Θ')
  (p : Part Γ Δ Θ) (f : S ∣ Γ ⊢ A) (g : - ∣ Δ ⊢ B)
  → subst-cxt d (⊗r p f g)
    ≡ ⊗r (subst₂ (λ Γ Θ → Part Γ Δ Θ) e d p) (subst-cxt e f) g
⊗r-subst refl refl p f g = refl

-- The helpers traverse the selected occurrence or partition directly.
-- Their prefixes are accumulated in reverse order, so each recursive
-- step extends the prefix without any context transports.
ex : ∀ {S Γ Δ C} → Swap Γ Δ → S ∣ Γ ⊢ C → S ∣ Δ ⊢ C
ex-pass : ∀ (Λ : Cxt) {A Γ Δ Ω C} → Swap Γ Δ → Pick A Γ Ω
  → just A ∣ Λ ᴿ++ Ω ⊢ C → - ∣ Λ ᴿ++ Δ ⊢ C
ex-⊗r : ∀ {S Λ Ω Ξ Γ Δ Θ Θ' A B} → Part Λ Ω Ξ → Swap Θ Θ' → Part Γ Δ Θ
  → S ∣ Λ ᴿ++ Γ ⊢ A → - ∣ Ω ᴿ++ Δ ⊢ B → S ∣ Ξ ᴿ++ Θ' ⊢ A ⊗ B

ex σ (Il f) = Il (ex σ f)
ex σ (⊗l f) = ⊗l (ex (keep σ) f)
ex σ (∧r f g) = ∧r (ex σ f) (ex σ g)
ex σ (∧l₁ f) = ∧l₁ (ex σ f)
ex σ (∧l₂ f) = ∧l₂ (ex σ f)
ex σ (∨r₁ f) = ∨r₁ (ex σ f)
ex σ (∨r₂ f) = ∨r₂ (ex σ f)
ex σ (∨l f g) = ∨l (ex σ f) (ex σ g)
ex σ (pass p f) = ex-pass [] σ p f
ex σ (⊗r p f g) = ex-⊗r done σ p f g

ex-pass Λ sw here f = pass (pickᴿ++ Λ (there here)) f
ex-pass Λ sw (there here) f = pass (pickᴿ++ Λ here) f
ex-pass Λ sw (there (there p)) f = pass (pickᴿ++ Λ (there (there p))) (ex (swapᴿ++ Λ sw) f)
ex-pass Λ (keep σ) here f = pass (pickᴿ++ Λ here) (ex (swapᴿ++ Λ σ) f)
ex-pass Λ (keep {A = B} σ) (there p) f = ex-pass (B ∷ Λ) σ p f

ex-⊗r {Λ = Λ} r sw (left (left p)) f g =
  ⊗r (partᴿ++ r (left (left p))) (ex (swapᴿ++ Λ sw) f) g
ex-⊗r {Ω = Ω} r sw (right (right p)) f g =
  ⊗r (partᴿ++ r (right (right p))) f (ex (swapᴿ++ Ω sw) g)
ex-⊗r r sw (left (right p)) f g = ⊗r (partᴿ++ r (right (left p))) f g
ex-⊗r r sw (right (left p)) f g = ⊗r (partᴿ++ r (left (right p))) f g
ex-⊗r r (keep σ) (left p) f g = ex-⊗r (left r) σ p f g
ex-⊗r r (keep σ) (right p) f g = ex-⊗r (right r) σ p f g

ex-subst : ∀ {S Γ Γ' Δ Δ' C} (p : Γ ≡ Γ') (q : Δ ≡ Δ') (σ : Swap Γ Δ) (f : S ∣ Γ ⊢ C)
  → ex (subst₂ Swap p q σ) (subst-cxt p f) ≡ subst-cxt q (ex σ f)
ex-subst refl refl σ f = refl

-- Realize selections and partitions using admissible adjacent exchange.
-- The accumulated prefix is stored in reverse order.
ex-pickR : ∀ {S X Γ Δ C} → Pick X Γ Δ → (Λ : Cxt)
  → S ∣ Λ ᴿ++ Γ ⊢ C → S ∣ Λ ᴿ++ (X ∷ Δ) ⊢ C
ex-pickR here Λ f = f
ex-pickR (there {b = Y} q) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR q (Y ∷ Λ) f)

ex-pickL : ∀ {S X Γ Δ C} → Pick X Γ Δ → (Λ : Cxt)
  → S ∣ Λ ᴿ++ (X ∷ Δ) ⊢ C → S ∣ Λ ᴿ++ Γ ⊢ C
ex-pickL here Λ f = f
ex-pickL (there {b = Y} q) Λ f =
  ex-pickL q (Y ∷ Λ) (ex (swapᴿ++ Λ sw) f)

ex-part : ∀ {S Γ Δ Θ C} → Part Γ Δ Θ → (Λ : Cxt)
  → S ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C → S ∣ Λ ᴿ++ Θ ⊢ C
ex-part done Λ f = f
ex-part (left {x = X} p) Λ f = ex-part p (X ∷ Λ) f
ex-part (right {x = X} {xs = Γ} p) Λ f =
  ex-part p (X ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f)
