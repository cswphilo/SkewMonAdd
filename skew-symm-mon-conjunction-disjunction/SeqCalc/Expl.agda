{-# OPTIONS --safe #-}

module SeqCalc.Expl (At : Set) where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open ≡-Reasoning
open import Utilities hiding (ex-pickR)
open import Formulae At

-- =======================================================================

-- Sequent calculus
-- Pass and tensor-right carry their conclusion-context equalities.

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  pass : ∀ {Γ Λ A C} → Λ ≡ A ∷ Γ
    → just A ∣ Γ ⊢ C → - ∣ Λ ⊢ C
  Ir : - ∣ [] ⊢ I
  Il : {Γ : Cxt} → {C : Fma} → 
              - ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗r : ∀ {S Γ Δ Ξ A B} → Ξ ≡ Γ ++ Δ
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
  ex : {S : Stp} {Γ Δ : Cxt} {C : Fma}
    → Swap Γ Δ → S ∣ Γ ⊢ C → S ∣ Δ ⊢ C

-- ====================================================================

-- Transport context equalities explicitly; no list equations are rewrite rules.
subst-cxt : ∀ {S Γ Γ' C} → Γ ≡ Γ' → S ∣ Γ ⊢ C → S ∣ Γ' ⊢ C
subst-cxt refl f = f

subst-cxt-coherent : ∀ {S Γ Δ Ξ C} (p : Γ ≡ Δ) (q : Δ ≡ Ξ) (r : Γ ≡ Ξ)
  (f : S ∣ Γ ⊢ C) → subst-cxt q (subst-cxt p f) ≡ subst-cxt r f
subst-cxt-coherent refl refl refl f = refl

subst-cxt-ex : ∀ {S Γ Γ' Δ Δ' C} (p : Γ ≡ Γ') (q : Δ ≡ Δ')
  (σ : Swap Γ Δ) (τ : Swap Γ' Δ') → subst₂ Swap p q σ ≡ τ
  → (f : S ∣ Γ ⊢ C) → subst-cxt q (ex σ f) ≡ ex τ (subst-cxt p f)
subst-cxt-ex refl refl σ .σ refl f = refl

-- Realize selections and partitions with a reversed accumulated prefix.
-- Extending this prefix requires no associativity transports.
ex-pickR : ∀ {S A Γ Δ C} → Pick A Γ Δ → (Λ : Cxt)
  → S ∣ Λ ᴿ++ Γ ⊢ C → S ∣ Λ ᴿ++ (A ∷ Δ) ⊢ C
ex-pickR here Λ f = f
ex-pickR (there {b = B} p) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR p (B ∷ Λ) f)

ex-pickL : ∀ {S A Γ Δ C} → Pick A Γ Δ → (Λ : Cxt)
  → S ∣ Λ ᴿ++ (A ∷ Δ) ⊢ C → S ∣ Λ ᴿ++ Γ ⊢ C
ex-pickL here Λ f = f
ex-pickL (there {b = B} p) Λ f =
  ex-pickL p (B ∷ Λ) (ex (swapᴿ++ Λ sw) f)

ex-part : ∀ {S Γ Δ Ξ C} → Part Γ Δ Ξ → (Λ : Cxt)
  → S ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C → S ∣ Λ ᴿ++ Ξ ⊢ C
ex-part done Λ f = f
ex-part (left {x = A} p) Λ f = ex-part p (A ∷ Λ) f
ex-part (right {x = B} {xs = Γ} p) Λ f =
  ex-part p (B ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f)
