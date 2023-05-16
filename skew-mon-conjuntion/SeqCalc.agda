{-# OPTIONS --rewriting #-}

module SeqCalc where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae

-- =======================================================================

-- Sequent calculus

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  pass : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → - ∣ A ∷ Γ ⊢ C
  Ir : - ∣ [] ⊢ I
  Il : {Γ : Cxt} → {C : Fma} → 
              - ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗r : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → - ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B 
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
-- ====================================================================

-- Equality of proofs 

infixl 15 _∙_

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where

-- -- equivalence relation
  refl : ∀{S Γ A} {f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S Γ A} {f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S Γ A} {f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h

-- -- congruence
  pass : ∀{Γ A C} {f g : just A ∣ Γ ⊢ C} → f ≗ g → pass f ≗ pass g
  Il : ∀{Γ C} {f g : - ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗l : ∀{Γ A B C} {f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
  ⊗r : ∀{S Γ Δ A B} {f g : S ∣ Γ ⊢ A} {f' g' : - ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r f f' ≗ ⊗r g g'
  ∧r : ∀{S Γ A B} {f g : S ∣ Γ ⊢ A} {f' g' : S ∣ Γ ⊢ B} 
    → f ≗ g → f' ≗ g' → ∧r f f' ≗ ∧r g g'
  ∧l₁ : ∀{Γ A B C} {f g : just A ∣ Γ ⊢ C} → 
    f ≗ g → (∧l₁ {B = B} f) ≗ ∧l₁ g
  ∧l₂ : ∀{Γ A B C} {f g : just B ∣ Γ ⊢ C} → 
    f ≗ g → (∧l₂ {A = A} f) ≗ ∧l₂ g
-- -- η-conversions
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r ax (pass ax))
  ax∧ : {A B : Fma} → ax {A ∧ B} ≗ ∧r (∧l₁ ax) (∧l₂ ax)

-- -- permutative conversions
  ⊗rpass : {Γ Δ : Cxt} {A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r (pass f) g ≗ pass (⊗r f g)
  ⊗rIl : {Γ Δ : Cxt} {A B : Fma}
    → {f : - ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≗ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≗ ⊗l (⊗r f g)
  ⊗r∧l₁ : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r (∧l₁ {B = B'} f) g ≗ ∧l₁ (⊗r f g)
  ⊗r∧l₂ : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just B' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r (∧l₂ {A = A'} f) g ≗ ∧l₂ (⊗r f g)
  ∧rpass : {Γ : Cxt} {A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : just A' ∣ Γ ⊢ B}
    → ∧r (pass f) (pass g) ≗ pass (∧r f g)
  ∧rIl : {Γ : Cxt} {A B : Fma}
    → {f : - ∣ Γ ⊢ A} {g : - ∣ Γ ⊢ B}
    → ∧r (Il f) (Il g) ≗ Il (∧r f g) 
  ∧r⊗l : {Γ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A} {g : just A' ∣ B' ∷ Γ ⊢ B}
    → ∧r (⊗l f) (⊗l g) ≗ ⊗l (∧r f g)
  ∧r∧l₁ : {Γ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : just A' ∣ Γ ⊢ B}
    → ∧r (∧l₁ {B = B'} f) (∧l₁ g) ≗ ∧l₁ (∧r f g)
  ∧r∧l₂ : {Γ : Cxt} {A A' B B' : Fma}
    → {f : just B' ∣ Γ ⊢ A} {g : just B' ∣ Γ ⊢ B}
    → ∧r (∧l₂ {A = A'} f) (∧l₂ g) ≗ ∧l₂ (∧r f g)

≡to≗ : {S : Stp} {Γ : Cxt} {C : Fma}
  → {f g : S ∣ Γ ⊢ C}
  → f ≡ g
  → f ≗ g
≡to≗ refl = refl