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
  ∨r₁ : {S : Stp} → {Γ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → 
              S ∣ Γ ⊢ A ∨ B
  ∨r₂ : {S : Stp} → {Γ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ B → 
              S ∣ Γ ⊢ A ∨ B
  ∨l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ Γ ⊢ C → just B ∣ Γ ⊢ C → 
              just (A ∨ B) ∣ Γ ⊢ C
  -- ⊥l : {Γ : Cxt} → {C : Fma} → just bot ∣ Γ ⊢ C 
  -- ⊤r : {S : Stp} → {Γ : Cxt} → S ∣ Γ ⊢ top
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
  ∧l₁ : ∀{Γ A B C} {f g : just A ∣ Γ ⊢ C}
     → f ≗ g → (∧l₁ {B = B} f) ≗ ∧l₁ g
  ∧l₂ : ∀{Γ A B C} {f g : just B ∣ Γ ⊢ C} 
    → f ≗ g → (∧l₂ {A = A} f) ≗ ∧l₂ g
  ∨r₁ : ∀ {S Γ A B} {f g : S ∣ Γ ⊢ A} 
    → f ≗ g → ∨r₁ {B = B} f ≗ ∨r₁ g
  ∨r₂ : ∀ {S Γ A B} {f g : S ∣ Γ ⊢ B} 
    → f ≗ g → ∨r₂ {A = A} f ≗ ∨r₂ g
  ∨l : ∀ {Γ A B C} {f g : just A ∣ Γ ⊢ C} {f' g' : just B ∣ Γ ⊢ C}
    → f ≗ g → f' ≗ g'
    → ∨l f f' ≗ ∨l g g'
-- -- η-conversions
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r ax (pass ax))
  ax∧ : {A B : Fma} → ax {A ∧ B} ≗ ∧r (∧l₁ ax) (∧l₂ ax)
  ax∨ : {A B : Fma} → ax {A ∨ B} ≗ ∨l (∨r₁ ax) (∨r₂ ax)
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
  ⊗r∨l : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ Γ ⊢ A} {f' : just B' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r (∨l f f') g ≗ ∨l (⊗r f g) (⊗r f' g)
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
  ∧r∨l : {Γ : Cxt} {A A' B B' : Fma} 
    → {f : just A' ∣ Γ ⊢ A} {f' : just A' ∣ Γ ⊢ B} {g : just B' ∣ Γ ⊢ A} {g' : just B' ∣ Γ ⊢ B}
    → ∧r (∨l f g) (∨l f' g') ≗ ∨l (∧r f f') (∧r g g')
  ∨r₁pass : {Γ : Cxt} {A A' B : Fma} 
    → {f : just A' ∣ Γ ⊢ A}
    → ∨r₁ {B = B} (pass f) ≗ pass (∨r₁ f)
  ∨r₁Il : {Γ : Cxt} {A B : Fma}
    → {f : - ∣ Γ ⊢ A}
    → ∨r₁ {B = B} (Il f) ≗ Il (∨r₁ f)
  ∨r₁⊗l : {Γ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}
    → ∨r₁ {B = B} (⊗l f) ≗ ⊗l (∨r₁ f)
  ∨r₁∧l₁ : {Γ : Cxt} {A A' B B' : Fma} 
    → {f : just A' ∣ Γ ⊢ A}
    → ∨r₁ {B = B} (∧l₁ {B = B'} f) ≗ ∧l₁ (∨r₁ f)
  ∨r₁∧l₂ : {Γ : Cxt} {A A' B B' : Fma} 
    → {f : just B' ∣ Γ ⊢ A}
    → ∨r₁ {B = B} (∧l₂ {A = A'} f) ≗ ∧l₂ (∨r₁ f)
  ∨r₁∨l : {Γ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : just B' ∣ Γ ⊢ A}
    → ∨r₁ {B = B} (∨l f g) ≗ ∨l (∨r₁ f) (∨r₁ g)
  ∨r₂pass : {Γ : Cxt} {A A' B : Fma} 
    → {f : just A' ∣ Γ ⊢ B}
    → ∨r₂ {A = A} (pass f) ≗ pass (∨r₂ f)
  ∨r₂Il : {Γ : Cxt} {A B : Fma}
    → {f : - ∣ Γ ⊢ B}
    → ∨r₂ {A = A} (Il f) ≗ Il (∨r₂ f)
  ∨r₂⊗l : {Γ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ B}
    → ∨r₂ {A = A} (⊗l f) ≗ ⊗l (∨r₂ f)
  ∨r₂∧l₁ : {Γ : Cxt} {A A' B B' : Fma} 
    → {f : just A' ∣ Γ ⊢ B}
    → ∨r₂ {A = A} (∧l₁ {B = B'} f) ≗ ∧l₁ (∨r₂ f)
  ∨r₂∧l₂ : {Γ : Cxt} {A A' B B' : Fma} 
    → {f : just B' ∣ Γ ⊢ B}
    → ∨r₂ {A = A} (∧l₂ {A = A'} f) ≗ ∧l₂ (∨r₂ f)
  ∨r₂∨l : {Γ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ Γ ⊢ B} {g : just B' ∣ Γ ⊢ B}
    → ∨r₂ {A = A} (∨l f g) ≗ ∨l (∨r₂ f) (∨r₂ g)
≡to≗ : {S : Stp} {Γ : Cxt} {C : Fma}
  → {f g : S ∣ Γ ⊢ C}
  → f ≡ g
  → f ≗ g
≡to≗ refl = refl

-- ⊥lᶜ : {S : Stp} {Γ Δ Γ' : Cxt} {C : Fma} 
--   → Γ' ≡ Γ ++ bot ∷ Δ
--   → S ∣ Γ' ⊢ C
-- ⊥lᶜ {C = ` x} refl = {!   !}
-- ⊥lᶜ {C = I} refl = {!   !}
-- ⊥lᶜ {C = top} refl = ⊤r
-- ⊥lᶜ {C = bot} refl = ⊥lᶜ refl
-- ⊥lᶜ {C = C ⊗ C₁} refl = {!   !}
-- ⊥lᶜ {C = C ∧ C₁} refl = {!   !}
-- ⊥lᶜ {C = C ∨ C₁} refl = {!   !}
-- ∧l₁ᶜ : {S : Stp} {Γ Δ Γ' : Cxt} {A B C : Fma}
--   → (f : S ∣ Γ' ⊢ C)
--   → (eq : Γ' ≡ Γ ++ A ∷ Δ)
--   → S ∣ Γ ++ A ∧ B ∷ Δ ⊢ C
-- ∧l₁ᶜ ax eq = ⊥-elim ([]disj∷ _ eq)
-- ∧l₁ᶜ {Γ = []} (pass f) refl = pass (∧l₁ f)
-- ∧l₁ᶜ {Γ = x ∷ Γ} (pass f) refl = pass (∧l₁ᶜ f refl)
-- ∧l₁ᶜ Ir eq = ⊥-elim ([]disj∷ _ eq)
-- ∧l₁ᶜ (Il f) eq = Il (∧l₁ᶜ f eq)
-- ∧l₁ᶜ {Γ = Γ₁} {Δ₁} (⊗r {Γ = Γ} {Δ} f f₁) eq with cases++ Γ₁ Γ Δ₁ Δ eq
-- ∧l₁ᶜ {Γ = Γ₁} {.(Ω ++ Δ)} (⊗r {Γ = .(Γ₁ ++ _ ∷ Ω)} {Δ} f f₁) refl | inj₁ (Ω , refl , refl) = ⊗r (∧l₁ᶜ f refl) f₁
-- ∧l₁ᶜ {Γ = .(Γ ++ Ω)} {Δ₁} (⊗r {Γ = Γ} {.(Ω ++ _ ∷ Δ₁)} f f₁) refl | inj₂ (Ω , refl , refl) = ⊗r f (∧l₁ᶜ f₁ refl)
-- ∧l₁ᶜ {Γ = Γ} (⊗l f) refl = ⊗l (∧l₁ᶜ {Γ = _ ∷ Γ} f refl) -- ⊗l (∧l₁ᶜ f refl)
-- ∧l₁ᶜ (∧r f f₁) eq = ∧r (∧l₁ᶜ f eq) (∧l₁ᶜ f₁ eq)
-- ∧l₁ᶜ (∧l₁ f) refl = ∧l₁ (∧l₁ᶜ f refl)
-- ∧l₁ᶜ (∧l₂ f) eq = ∧l₂ (∧l₁ᶜ f eq)
-- ∧l₁ᶜ (∨r₁ f) refl = ∨r₁ (∧l₁ᶜ f refl)
-- ∧l₁ᶜ (∨r₂ f) eq = ∨r₂ (∧l₁ᶜ f eq)
-- ∧l₁ᶜ (∨l f f₁) refl = ∨l (∧l₁ᶜ f refl) (∧l₁ᶜ f₁ refl)
-- ∧l₁ᶜ ⊥l refl = ⊥l