{-# OPTIONS --safe #-}

module SeqCalc.ExplEq (At : Set) where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open ≡-Reasoning
open import Utilities hiding (ex-pickR)
open import Formulae At
open import SeqCalc.Expl At public

-- Equality of proofs 

infixl 15 _∙_

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where

-- -- equivalence relation
  refl : ∀{S Γ A} {f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S Γ A} {f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S Γ A} {f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h

-- -- congruence
  pass : ∀ {Γ Λ A C} (e : Λ ≡ A ∷ Γ) {f g : just A ∣ Γ ⊢ C}
    → f ≗ g → pass e f ≗ pass e g
  Il : ∀{Γ C} {f g : - ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗l : ∀{Γ A B C} {f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
  ⊗r : ∀ {S Γ Δ Ξ A B} (e : Ξ ≡ Γ ++ Δ)
    {f g : S ∣ Γ ⊢ A} {f' g' : - ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r e f f' ≗ ⊗r e g g'
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
  ex : ∀ {S Γ Δ C} (σ : Swap Γ Δ) {f g : S ∣ Γ ⊢ C}
    → f ≗ g → ex σ f ≗ ex σ g
    
-- -- η-conversions
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r refl ax (pass refl ax))
  ax∧ : {A B : Fma} → ax {A ∧ B} ≗ ∧r (∧l₁ ax) (∧l₂ ax)
  ax∨ : {A B : Fma} → ax {A ∨ B} ≗ ∨l (∨r₁ ax) (∨r₂ ax)

-- -- permutative conversions
  ⊗rpass : {Γ Δ : Cxt} {A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r refl (pass refl f) g ≗ pass refl (⊗r refl f g)
  ⊗rIl : {Γ Δ : Cxt} {A B : Fma}
    → {f : - ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r refl (Il f) g ≗ Il (⊗r refl f g)
  ⊗r⊗l : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r refl (⊗l f) g ≗ ⊗l (⊗r refl f g)
  ⊗r∧l₁ : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r refl (∧l₁ {B = B'} f) g ≗ ∧l₁ (⊗r refl f g)
  ⊗r∧l₂ : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just B' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r refl (∧l₂ {A = A'} f) g ≗ ∧l₂ (⊗r refl f g)
  ⊗r∨l : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ Γ ⊢ A} {f' : just B' ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r refl (∨l f f') g ≗ ∨l (⊗r refl f g) (⊗r refl f' g)
  ∧rpass : {Γ : Cxt} {A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : just A' ∣ Γ ⊢ B}
    → ∧r (pass refl f) (pass refl g) ≗ pass refl (∧r f g)
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
    → ∨r₁ {B = B} (pass refl f) ≗ pass refl (∨r₁ f)
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
    → ∨r₂ {A = A} (pass refl f) ≗ pass refl (∨r₂ f)
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
    
  ex-iso : ∀ {S Γ Δ C} (σ : Swap Γ Δ) {f : S ∣ Γ ⊢ C}
    → ex (swap-sym σ) (ex σ f) ≗ f
  ex-braid : ∀ {S Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ C}
    {σ₁ : Swap Γ Δ₁} {σ₂ : Swap Δ₁ Δ₂} {σ₃ : Swap Δ₂ Θ}
    {τ₁ : Swap Γ Ξ₁} {τ₂ : Swap Ξ₁ Ξ₂} {τ₃ : Swap Ξ₂ Θ}
    → Braid σ₁ σ₂ σ₃ τ₁ τ₂ τ₃ → {f : S ∣ Γ ⊢ C}
    → ex σ₃ (ex σ₂ (ex σ₁ f)) ≗ ex τ₃ (ex τ₂ (ex τ₁ f))
  exex : ∀ {S Γ Δ Ξ Θ C}
    {σ₁ : Swap Γ Δ} {σ₂ : Swap Δ Θ} {τ₁ : Swap Γ Ξ} {τ₂ : Swap Ξ Θ}
    → Disjoint σ₁ σ₂ τ₁ τ₂ → {f : S ∣ Γ ⊢ C}
    → ex σ₂ (ex σ₁ f) ≗ ex τ₂ (ex τ₁ f)
  expass : ∀ {Γ Δ A C} (σ : Swap Γ Δ) {f : just A ∣ Γ ⊢ C}
    → ex (keep σ) (pass refl f) ≗ pass refl (ex σ f)
  exIl : ∀ {Γ Δ C} (σ : Swap Γ Δ) {f : - ∣ Γ ⊢ C}
    → ex σ (Il f) ≗ Il (ex σ f)
  ex⊗l : ∀ {Γ Δ A B C} (σ : Swap Γ Δ) {f : just A ∣ B ∷ Γ ⊢ C}
    → ex σ (⊗l f) ≗ ⊗l (ex (keep σ) f)
  ex⊗r₁ : ∀ {S Γ Γ' Δ A B} (σ : Swap Γ Γ')
    {f : S ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ex (swap-post σ Δ) (⊗r refl f g) ≗ ⊗r refl (ex σ f) g
  ex⊗r₂ : ∀ {S Γ Δ Δ' A B} (σ : Swap Δ Δ')
    {f : S ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ex (swap-pre Γ σ) (⊗r refl f g) ≗ ⊗r refl f (ex σ g)
  ex∧l₁ : ∀ {Γ Δ A B C} (σ : Swap Γ Δ) {f : just A ∣ Γ ⊢ C}
    → ex σ (∧l₁ {B = B} f) ≗ ∧l₁ (ex σ f)
  ex∧l₂ : ∀ {Γ Δ A B C} (σ : Swap Γ Δ) {f : just B ∣ Γ ⊢ C}
    → ex σ (∧l₂ {A = A} f) ≗ ∧l₂ (ex σ f)
  ex∧r : ∀ {S Γ Δ A B} (σ : Swap Γ Δ) {f : S ∣ Γ ⊢ A} {g : S ∣ Γ ⊢ B}
    → ex σ (∧r f g) ≗ ∧r (ex σ f) (ex σ g)
  ex∨l : ∀ {Γ Δ A B C} (σ : Swap Γ Δ) {f : just A ∣ Γ ⊢ C} {g : just B ∣ Γ ⊢ C}
    → ex σ (∨l f g) ≗ ∨l (ex σ f) (ex σ g)
  ex∨r₁ : ∀ {S Γ Δ A B} (σ : Swap Γ Δ) {f : S ∣ Γ ⊢ A}
    → ex σ (∨r₁ {B = B} f) ≗ ∨r₁ (ex σ f)
  ex∨r₂ : ∀ {S Γ Δ A B} (σ : Swap Γ Δ) {f : S ∣ Γ ⊢ B}
    → ex σ (∨r₂ {A = A} f) ≗ ∨r₂ (ex σ f)

≡to≗ : {S : Stp} {Γ : Cxt} {C : Fma}
  → {f g : S ∣ Γ ⊢ C}
  → f ≡ g
  → f ≗ g
≡to≗ refl = refl

-- The explicit permutation operations preserve the proof equations.
cong-ex-pickR : ∀ {S X Γ Δ C} (p : Pick X Γ Δ) (Λ : Cxt)
  {f g : S ∣ Λ ᴿ++ Γ ⊢ C} → f ≗ g → ex-pickR p Λ f ≗ ex-pickR p Λ g
cong-ex-pickR here Λ eq = eq
cong-ex-pickR (there {b = B} p) Λ eq =
  ex (swapᴿ++ Λ sw) (cong-ex-pickR p (B ∷ Λ) eq)

cong-ex-pickL : ∀ {S X Γ Δ C} (p : Pick X Γ Δ) (Λ : Cxt)
  {f g : S ∣ Λ ᴿ++ (X ∷ Δ) ⊢ C} → f ≗ g → ex-pickL p Λ f ≗ ex-pickL p Λ g
cong-ex-pickL here Λ eq = eq
cong-ex-pickL (there {b = B} p) Λ eq =
  cong-ex-pickL p (B ∷ Λ) (ex (swapᴿ++ Λ sw) eq)

cong-ex-part : ∀ {S Γ Δ Ξ C} (p : Part Γ Δ Ξ) (Λ : Cxt)
  {f g : S ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C} → f ≗ g → ex-part p Λ f ≗ ex-part p Λ g
cong-ex-part done Λ eq = eq
cong-ex-part (left {x = A} p) Λ eq = cong-ex-part p (A ∷ Λ) eq
cong-ex-part (right {x = B} {xs = Γ} p) Λ eq =
  cong-ex-part p (B ∷ Λ) (cong-ex-pickR (pick-prefix Γ) Λ eq)

-- A contiguous partition performs no exchanges.
ex-part-eq : ∀ {S C} (Γ Δ Λ : Cxt) (f : S ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C)
  → ex-part (part Γ Δ) Λ f ≡ f
ex-part-eq [] [] Λ f = refl
ex-part-eq [] (B ∷ Δ) Λ f = ex-part-eq [] Δ (B ∷ Λ) f
ex-part-eq (A ∷ Γ) Δ Λ f = ex-part-eq Γ Δ (A ∷ Λ) f

ex-pickR-Il : ∀ {Γ Δ Z C} (p : Pick Z Γ Δ) (Λ : Cxt)
  (f : - ∣ Λ ᴿ++ Γ ⊢ C)
  → ex-pickR p Λ (Il f) ≗ Il (ex-pickR p Λ f)
ex-pickR-Il here Λ f = refl
ex-pickR-Il (there {b = B} p) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR-Il p (B ∷ Λ) f) ∙ exIl (swapᴿ++ Λ sw)

ex-part-Il : ∀ {Γ Δ Ξ C} (p : Part Γ Δ Ξ) (Λ : Cxt)
  (f : - ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C)
  → ex-part p Λ (Il f) ≗ Il (ex-part p Λ f)
ex-part-Il done Λ f = refl
ex-part-Il (left {x = A} p) Λ f = ex-part-Il p (A ∷ Λ) f
ex-part-Il (right {x = B} {xs = Γ} p) Λ f =
  cong-ex-part p (B ∷ Λ) (ex-pickR-Il (pick-prefix Γ) Λ f) ∙
  ex-part-Il p (B ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f)

ex-pickR-∧l₁ : ∀ {Γ Δ Z C X Y} (p : Pick Z Γ Δ) (Λ : Cxt)
  (f : just X ∣ Λ ᴿ++ Γ ⊢ C)
  → ex-pickR p Λ (∧l₁ {B = Y} f) ≗ ∧l₁ (ex-pickR p Λ f)
ex-pickR-∧l₁ here Λ f = refl
ex-pickR-∧l₁ (there {b = B} p) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR-∧l₁ p (B ∷ Λ) f) ∙ ex∧l₁ (swapᴿ++ Λ sw)

ex-part-∧l₁ : ∀ {Γ Δ Ξ C X Y} (p : Part Γ Δ Ξ) (Λ : Cxt)
  (f : just X ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C)
  → ex-part p Λ (∧l₁ {B = Y} f) ≗ ∧l₁ (ex-part p Λ f)
ex-part-∧l₁ done Λ f = refl
ex-part-∧l₁ (left {x = A} p) Λ f = ex-part-∧l₁ p (A ∷ Λ) f
ex-part-∧l₁ (right {x = B} {xs = Γ} p) Λ f =
  cong-ex-part p (B ∷ Λ) (ex-pickR-∧l₁ (pick-prefix Γ) Λ f) ∙
  ex-part-∧l₁ p (B ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f)

ex-pickR-∧l₂ : ∀ {Γ Δ Z C X Y} (p : Pick Z Γ Δ) (Λ : Cxt)
  (f : just Y ∣ Λ ᴿ++ Γ ⊢ C)
  → ex-pickR p Λ (∧l₂ {A = X} f) ≗ ∧l₂ (ex-pickR p Λ f)
ex-pickR-∧l₂ here Λ f = refl
ex-pickR-∧l₂ (there {b = B} p) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR-∧l₂ p (B ∷ Λ) f) ∙ ex∧l₂ (swapᴿ++ Λ sw)

ex-part-∧l₂ : ∀ {Γ Δ Ξ C X Y} (p : Part Γ Δ Ξ) (Λ : Cxt)
  (f : just Y ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C)
  → ex-part p Λ (∧l₂ {A = X} f) ≗ ∧l₂ (ex-part p Λ f)
ex-part-∧l₂ done Λ f = refl
ex-part-∧l₂ (left {x = A} p) Λ f = ex-part-∧l₂ p (A ∷ Λ) f
ex-part-∧l₂ (right {x = B} {xs = Γ} p) Λ f =
  cong-ex-part p (B ∷ Λ) (ex-pickR-∧l₂ (pick-prefix Γ) Λ f) ∙
  ex-part-∧l₂ p (B ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f)

ex-pickR-∨l : ∀ {Γ Δ Z C X Y} (p : Pick Z Γ Δ) (Λ : Cxt)
  (f : just X ∣ Λ ᴿ++ Γ ⊢ C) (g : just Y ∣ Λ ᴿ++ Γ ⊢ C)
  → ex-pickR p Λ (∨l f g) ≗ ∨l (ex-pickR p Λ f) (ex-pickR p Λ g)
ex-pickR-∨l here Λ f g = refl
ex-pickR-∨l (there {b = B} p) Λ f g =
  ex (swapᴿ++ Λ sw) (ex-pickR-∨l p (B ∷ Λ) f g) ∙ ex∨l (swapᴿ++ Λ sw)

ex-part-∨l : ∀ {Γ Δ Ξ C X Y} (p : Part Γ Δ Ξ) (Λ : Cxt)
  (f : just X ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C) (g : just Y ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C)
  → ex-part p Λ (∨l f g) ≗ ∨l (ex-part p Λ f) (ex-part p Λ g)
ex-part-∨l done Λ f g = refl
ex-part-∨l (left {x = A} p) Λ f g = ex-part-∨l p (A ∷ Λ) f g
ex-part-∨l (right {x = B} {xs = Γ} p) Λ f g =
  cong-ex-part p (B ∷ Λ) (ex-pickR-∨l (pick-prefix Γ) Λ f g) ∙
  ex-part-∨l p (B ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f) (ex-pickR (pick-prefix Γ) Λ g)

ex-pickL-∧r : ∀ {S X Γ Δ A B} (p : Pick X Γ Δ) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ (X ∷ Δ) ⊢ A) (g : S ∣ Λ ᴿ++ (X ∷ Δ) ⊢ B)
  → ∧r (ex-pickL p Λ f) (ex-pickL p Λ g) ≗ ex-pickL p Λ (∧r f g)
ex-pickL-∧r here Λ f g = refl
ex-pickL-∧r (there {b = Y} p) Λ f g =
  ex-pickL-∧r p (Y ∷ Λ) (ex (swapᴿ++ Λ sw) f) (ex (swapᴿ++ Λ sw) g) ∙
  cong-ex-pickL p (Y ∷ Λ) (~ ex∧r (swapᴿ++ Λ sw))

ex-pickL-∨r₁ : ∀ {S X Γ Δ A B} (p : Pick X Γ Δ) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ (X ∷ Δ) ⊢ A)
  → ∨r₁ {B = B} (ex-pickL p Λ f) ≗ ex-pickL p Λ (∨r₁ f)
ex-pickL-∨r₁ here Λ f = refl
ex-pickL-∨r₁ (there {b = Y} p) Λ f =
  ex-pickL-∨r₁ p (Y ∷ Λ) (ex (swapᴿ++ Λ sw) f) ∙
  cong-ex-pickL p (Y ∷ Λ) (~ ex∨r₁ (swapᴿ++ Λ sw))

ex-pickL-∨r₂ : ∀ {S X Γ Δ A B} (p : Pick X Γ Δ) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ (X ∷ Δ) ⊢ B)
  → ∨r₂ {A = A} (ex-pickL p Λ f) ≗ ex-pickL p Λ (∨r₂ f)
ex-pickL-∨r₂ here Λ f = refl
ex-pickL-∨r₂ (there {b = Y} p) Λ f =
  ex-pickL-∨r₂ p (Y ∷ Λ) (ex (swapᴿ++ Λ sw) f) ∙
  cong-ex-pickL p (Y ∷ Λ) (~ ex∨r₂ (swapᴿ++ Λ sw))

-- Logical rules that add a formula before the accumulated prefix use
-- the snoc transport; permutation recursion itself needs no transports.
ex-pickR-⊗l : ∀ {Γ Δ X Y Z C} (p : Pick Z Γ Δ) (Λ : Cxt)
  (f : just X ∣ Y ∷ (Λ ᴿ++ Γ) ⊢ C)
  → ex-pickR p Λ (⊗l f) ≗
    ⊗l (subst-cxt (ᴿ++-snoc Λ Y (Z ∷ Δ))
      (ex-pickR p (Λ ++ [ Y ]) (subst-cxt (sym (ᴿ++-snoc Λ Y Γ)) f)))
ex-pickR-⊗l {Γ = Γ} {Y = Y} here Λ f =
  ⊗l (≡to≗ (sym (subst-cxt-coherent (sym (ᴿ++-snoc Λ Y Γ)) (ᴿ++-snoc Λ Y Γ) refl f)))
ex-pickR-⊗l {Δ = _ ∷ Δ} {Y = Y} {Z = Z} (there {b = B} p) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR-⊗l p (B ∷ Λ) f) ∙
  ex⊗l (swapᴿ++ Λ sw) ∙
  ⊗l (≡to≗ (sym (subst-cxt-ex
    (ᴿ++-snoc Λ Y (B ∷ Z ∷ Δ)) (ᴿ++-snoc Λ Y (Z ∷ B ∷ Δ))
    (swapᴿ++ (Λ ++ [ Y ]) sw) (keep (swapᴿ++ Λ sw))
    (swapᴿ++-snoc Λ Y sw) _)))

ex-part-⊗l : ∀ {Γ Δ Ξ X Y C} (p : Part Γ Δ Ξ) (Λ : Cxt)
  (f : just X ∣ Y ∷ (Λ ᴿ++ (Γ ++ Δ)) ⊢ C)
  → ex-part p Λ (⊗l f) ≗
    ⊗l (subst-cxt (ᴿ++-snoc Λ Y Ξ)
      (ex-part p (Λ ++ [ Y ]) (subst-cxt (sym (ᴿ++-snoc Λ Y (Γ ++ Δ))) f)))
ex-part-⊗l {Y = Y} done Λ f =
  ⊗l (≡to≗ (sym (subst-cxt-coherent (sym (ᴿ++-snoc Λ Y [])) (ᴿ++-snoc Λ Y []) refl f)))
ex-part-⊗l (left {x = B} p) Λ f = ex-part-⊗l p (B ∷ Λ) f
ex-part-⊗l {Δ = B ∷ Δ} {Ξ = B ∷ Ξ} {Y = Y} (right {xs = Γ} p) Λ f =
  cong-ex-part p (B ∷ Λ) (ex-pickR-⊗l (pick-prefix Γ) Λ f) ∙
  ex-part-⊗l p (B ∷ Λ) _ ∙
  ⊗l (≡to≗ (cong (λ h → subst-cxt (ᴿ++-snoc Λ Y (B ∷ Ξ))
      (ex-part p (B ∷ (Λ ++ [ Y ])) h))
    (subst-cxt-coherent (ᴿ++-snoc Λ Y (B ∷ Γ ++ Δ))
      (sym (ᴿ++-snoc Λ Y (B ∷ Γ ++ Δ))) refl _)))

-- Exchange commutes with pass for any presentation of its conclusion.
expass-cxt : ∀ {X Γ Δ Ω Θ C} (i : Ω ≡ X ∷ Γ) (o : Θ ≡ X ∷ Δ)
  (σ : Swap Ω Θ) (τ : Swap Γ Δ)
  → subst₂ Swap i o σ ≡ keep τ → {f : just X ∣ Γ ⊢ C}
  → ex σ (pass i f) ≗ pass o (ex τ f)
expass-cxt refl refl ._ τ refl = expass τ

ex-pickR-pass : ∀ {Γ Δ X Y C} (p : Pick Y Γ Δ) (Λ : Cxt)
  (f : just X ∣ Λ ᴿ++ Γ ⊢ C)
  → ex-pickR p (Λ ++ [ X ]) (pass (ᴿ++-snoc Λ X Γ) f)
    ≗ pass (ᴿ++-snoc Λ X (Y ∷ Δ)) (ex-pickR p Λ f)
ex-pickR-pass here Λ f = refl
ex-pickR-pass {Δ = _ ∷ Δ} {X = X} {Y = Y} (there {b = B} p) Λ f =
  ex (swapᴿ++ (Λ ++ [ X ]) sw) (ex-pickR-pass p (B ∷ Λ) f) ∙
  expass-cxt (ᴿ++-snoc Λ X (B ∷ Y ∷ Δ)) (ᴿ++-snoc Λ X (Y ∷ B ∷ Δ))
    (swapᴿ++ (Λ ++ [ X ]) sw) (swapᴿ++ Λ sw) (swapᴿ++-snoc Λ X sw)

ex-part-pass : ∀ {Γ Δ Ξ X C} (p : Part Γ Δ Ξ) (Λ : Cxt)
  (f : just X ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C)
  → ex-part p (Λ ++ [ X ]) (pass (ᴿ++-snoc Λ X (Γ ++ Δ)) f)
    ≗ pass (ᴿ++-snoc Λ X Ξ) (ex-part p Λ f)
ex-part-pass done Λ f = refl
ex-part-pass (left {x = B} p) Λ f = ex-part-pass p (B ∷ Λ) f
ex-part-pass {X = X} (right {x = B} {xs = Γ} p) Λ f =
  cong-ex-part p (B ∷ (Λ ++ [ X ])) (ex-pickR-pass (pick-prefix Γ) Λ f) ∙
  ex-part-pass p (B ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f)

-- Exchanges in the traversed prefix commute with each suffix operation.
ex-pickR-ex-prefix : ∀ {S X Γ Δ Λ Λ' C} (q : Pick X Γ Δ) (ρ : Swap Λ Λ')
  (f : S ∣ Λ ᴿ++ Γ ⊢ C)
  → ex-pickR q Λ' (ex (swap-prefixᴿ++ ρ Γ) f)
    ≗ ex (swap-prefixᴿ++ ρ (X ∷ Δ)) (ex-pickR q Λ f)
ex-pickR-ex-prefix here ρ f = refl
ex-pickR-ex-prefix {Λ = Λ} {Λ' = Λ'} (there {b = B} q) ρ f =
  ex (swapᴿ++ Λ' sw) (ex-pickR-ex-prefix q (keep ρ) f) ∙
  exex (disjoint-prefixᴿ++ ρ sw)

ex-pickL-ex-prefix : ∀ {S X Γ Δ Λ Λ' C} (q : Pick X Γ Δ) (ρ : Swap Λ Λ')
  (f : S ∣ Λ ᴿ++ X ∷ Δ ⊢ C)
  → ex-pickL q Λ' (ex (swap-prefixᴿ++ ρ (X ∷ Δ)) f)
    ≗ ex (swap-prefixᴿ++ ρ Γ) (ex-pickL q Λ f)
ex-pickL-ex-prefix here ρ f = refl
ex-pickL-ex-prefix {Λ = Λ} {Λ' = Λ'} (there {b = B} q) ρ f =
  cong-ex-pickL q (B ∷ Λ') (exex (disjoint-prefixᴿ++ ρ sw)) ∙
  ex-pickL-ex-prefix q (keep ρ) (ex (swapᴿ++ Λ sw) f)

ex-part-ex-prefix : ∀ {S Γ Δ Ξ Λ Λ' C} (p : Part Γ Δ Ξ) (ρ : Swap Λ Λ')
  (f : S ∣ Λ ᴿ++ (Γ ++ Δ) ⊢ C)
  → ex-part p Λ' (ex (swap-prefixᴿ++ ρ (Γ ++ Δ)) f)
    ≗ ex (swap-prefixᴿ++ ρ Ξ) (ex-part p Λ f)
ex-part-ex-prefix done ρ f = refl
ex-part-ex-prefix (left p) ρ f = ex-part-ex-prefix p (keep ρ) f
ex-part-ex-prefix {Λ = Λ} {Λ' = Λ'} (right {x = X} {xs = Γ} p) ρ f =
  cong-ex-part p (X ∷ Λ') (ex-pickR-ex-prefix (pick-prefix Γ) ρ f) ∙
  ex-part-ex-prefix p (keep ρ) (ex-pickR (pick-prefix Γ) Λ f)

-- Gather a right-premise occurrence across a scattered left-premise one.
-- The recursive crossing uses exactly the adjacent braid equation.
ex-pickR-ex-pickL : ∀ {S Γ Ω X Y Δ C} (q : Pick X Γ Ω) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ X ∷ Ω ++ Y ∷ Δ ⊢ C)
  → ex-pickR (pick-prefix Γ) Λ (ex-pickL (pick-post q (Y ∷ Δ)) Λ f)
    ≗ ex-pickL (pick-post q Δ) (Y ∷ Λ)
      (ex (swapᴿ++ Λ sw) (ex-pickR (pick-prefix Ω) (X ∷ Λ) f))
ex-pickR-ex-pickL here Λ f = refl
ex-pickR-ex-pickL {Ω = Z ∷ Ω} {X = X} {Y} {Δ} (there q) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR-ex-pickL q (Z ∷ Λ) (ex (swapᴿ++ Λ sw) f)) ∙
  ~ ex-pickL-ex-prefix (pick-post q Δ) sw _ ∙
  cong-ex-pickL (pick-post q Δ) (Z ∷ Y ∷ Λ)
    (ex (swapᴿ++ Λ sw)
      (ex (swapᴿ++ (Z ∷ Λ) sw)
        (ex-pickR-ex-prefix (pick-prefix Ω) sw f)) ∙
     ex-braid (braidᴿ++ Λ braid))

-- Remove a selected left occurrence before or after shuffling a partition.
ex-part-ex-pickL : ∀ {S Γ Δ Ξ Ω X C} (p : Part Γ Δ Ξ) (q : Pick X Γ Ω)
  (Λ : Cxt) (f : S ∣ Λ ᴿ++ X ∷ Ω ++ Δ ⊢ C)
  → ex-part p Λ (ex-pickL (pick-post q Δ) Λ f)
    ≗ let t = pull-left p q in
      ex-pickL (proj₁ (proj₂ t)) Λ (ex-part (proj₂ (proj₂ t)) (X ∷ Λ) f)
ex-part-ex-pickL (left p) here Λ f = refl
ex-part-ex-pickL {Δ = Δ} {X = X} (left {x = Y} p) (there q) Λ f =
  ex-part-ex-pickL p q (Y ∷ Λ) (ex (swapᴿ++ Λ sw) f) ∙
  cong-ex-pickL (proj₁ (proj₂ (pull-left p q))) (Y ∷ Λ)
    (ex-part-ex-prefix (proj₂ (proj₂ (pull-left p q))) sw f) ∙
  ≡to≗ (sym (cong (λ t → ex-pickL (proj₁ (proj₂ t)) Λ
    (ex-part (proj₂ (proj₂ t)) (X ∷ Λ) f)) (pull-left-left p q)))
ex-part-ex-pickL {Γ = Γ} {Δ = Y ∷ Δ} {X = X} (right p) q Λ f =
  cong-ex-part p (Y ∷ Λ) (ex-pickR-ex-pickL q Λ f) ∙
  ex-part-ex-pickL p q (Y ∷ Λ)
    (ex (swapᴿ++ Λ sw) (ex-pickR (pick-prefix _) (X ∷ Λ) f)) ∙
  cong-ex-pickL (proj₁ (proj₂ (pull-left p q))) (Y ∷ Λ)
    (ex-part-ex-prefix (proj₂ (proj₂ (pull-left p q))) sw
      (ex-pickR (pick-prefix _) (X ∷ Λ) f)) ∙
  ≡to≗ (sym (cong (λ t → ex-pickL (proj₁ (proj₂ t)) Λ
    (ex-part (proj₂ (proj₂ t)) (X ∷ Λ) f)) (pull-left-right p q)))

-- Tensor-right under an accumulated prefix. Its associativity transport
-- is stable when the next traversed formula is added to that prefix.
⊗r-ex-prefix : ∀ {S Γ Γ' Δ A B} (Λ : Cxt) (σ : Swap Γ Γ')
  (f : S ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Δ ⊢ B)
  → ⊗r (sym (ᴿ++-++ Λ _ _)) (ex (swapᴿ++ Λ σ) f) g
    ≗ ex (swapᴿ++ Λ (swap-post σ Δ)) (⊗r (sym (ᴿ++-++ Λ _ _)) f g)
⊗r-ex-prefix [] σ f g = ~ ex⊗r₁ σ
⊗r-ex-prefix (X ∷ Λ) σ f g = ⊗r-ex-prefix Λ (keep σ) f g

⊗r-ex-pickL : ∀ {S Γ Ω X Δ A B} (q : Pick X Γ Ω) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ X ∷ Ω ⊢ A) (g : - ∣ Δ ⊢ B)
  → ⊗r (sym (ᴿ++-++ Λ _ _)) (ex-pickL q Λ f) g
    ≗ ex-pickL (pick-post q Δ) Λ (⊗r (sym (ᴿ++-++ Λ _ _)) f g)
⊗r-ex-pickL here Λ f g = refl
⊗r-ex-pickL {Δ = Δ} (there {b = Y} q) Λ f g =
  ⊗r-ex-pickL q (Y ∷ Λ) (ex (swapᴿ++ Λ sw) f) g ∙
  cong-ex-pickL (pick-post q Δ) (Y ∷ Λ) (⊗r-ex-prefix Λ sw f g)

-- The tensor-pass case also needs compatibility between the two
-- explicit permutation programs, following the selected occurrence.
ex-part-⊗rpass : ∀ {Γ Δ Ξ Ω X A B} (p : Part Γ Δ Ξ) (q : Pick X Γ Ω)
  (f : just X ∣ Ω ⊢ A) (g : - ∣ Δ ⊢ B)
  → ex-part p [] (⊗r refl (ex-pickL q [] (pass refl f)) g)
    ≗ let t = pull-left p q in
      ex-pickL (proj₁ (proj₂ t)) [] (pass refl (ex-part (proj₂ (proj₂ t)) [] (⊗r refl f g)))
ex-part-⊗rpass {X = X} p q f g =
  cong-ex-part p [] (⊗r-ex-pickL q [] (pass refl f) g) ∙
  ex-part-ex-pickL p q [] (⊗r refl (pass refl f) g) ∙
  cong-ex-pickL (proj₁ (proj₂ (pull-left p q))) []
    (cong-ex-part (proj₂ (proj₂ (pull-left p q))) [ X ] ⊗rpass ∙
     ex-part-pass (proj₂ (proj₂ (pull-left p q))) [] (⊗r refl f g))

-- Split a selection into its accumulated prefix and unprocessed suffix.
ex-pickL-pickᴿ++ : ∀ {S X Γ Ω C} (Λ : Cxt) (q : Pick X Γ Ω)
  (f : S ∣ X ∷ (Λ ᴿ++ Ω) ⊢ C)
  → ex-pickL (pickᴿ++ Λ q) [] f
    ≡ ex-pickL q Λ (ex-pickL (pickᴿ++ Λ here) [] f)
ex-pickL-pickᴿ++ [] q f = refl
ex-pickL-pickᴿ++ (Y ∷ Λ) q f = trans (ex-pickL-pickᴿ++ Λ (there q) f)
  (cong (ex-pickL q (Y ∷ Λ)) (sym (ex-pickL-pickᴿ++ Λ (there here) f)))

ex-iso-prefix : ∀ {S X Y Γ C} (Λ : Cxt) (f : S ∣ Λ ᴿ++ X ∷ Y ∷ Γ ⊢ C)
  → ex (swapᴿ++ Λ sw) (ex (swapᴿ++ Λ sw) f) ≗ f
ex-iso-prefix Λ f = ≡to≗ (cong (λ σ → ex σ (ex (swapᴿ++ Λ sw) f)) (sym (swap-symᴿ++ Λ sw))) ∙
  ex-iso (swapᴿ++ Λ sw)

-- A suffix exchange commutes with passing across the accumulated prefix.
ex-pickL-pass-ex : ∀ {X Γ Δ C} (Λ : Cxt) (σ : Swap Γ Δ)
  (f : just X ∣ Λ ᴿ++ Γ ⊢ C)
  → ex (swapᴿ++ Λ (keep σ)) (ex-pickL (pickᴿ++ Λ here) [] (pass refl f))
    ≗ ex-pickL (pickᴿ++ Λ here) [] (pass refl (ex (swapᴿ++ Λ σ) f))
ex-pickL-pass-ex [] σ f = expass σ
ex-pickL-pass-ex (Y ∷ Λ) σ f =
  ex (swapᴿ++ Λ (keep (keep σ))) (≡to≗ (ex-pickL-pickᴿ++ Λ (there here) (pass refl f))) ∙
  exex (disjointᴿ++ Λ (disjoint σ)) ∙
  ex (swapᴿ++ Λ sw) (ex-pickL-pass-ex Λ (keep σ) f) ∙
  ≡to≗ (sym (ex-pickL-pickᴿ++ Λ (there here) (pass refl (ex (swapᴿ++ Λ (keep σ)) f))))

-- Exchange two skipped occurrences while scattering a later selection.
ex-pickL-ex-two : ∀ {S X Y Z Γ Ω C} (q : Pick X Γ Ω) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ X ∷ Y ∷ Z ∷ Ω ⊢ C)
  → ex (swapᴿ++ Λ sw) (ex-pickL (there (there q)) Λ f)
    ≗ ex-pickL (there (there q)) Λ (ex (swapᴿ++ Λ (keep sw)) f)
ex-pickL-ex-two {Y = Y} {Z} q Λ f =
  ~ ex-pickL-ex-prefix q sw _ ∙
  cong-ex-pickL q (Y ∷ Z ∷ Λ) (ex-braid (braidᴿ++ Λ braid))

-- Gather an occurrence after an exchanged pair, or before an exchange.
ex-pickR-ex-skips : ∀ {S Γ Γ' X Δ C} (σ : Swap Γ Γ') (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ (Γ ++ X ∷ Δ) ⊢ C)
  → ex-pickR (pick-prefix Γ') Λ (ex (swapᴿ++ Λ (swap-post σ (X ∷ Δ))) f)
    ≗ ex (swapᴿ++ (X ∷ Λ) (swap-post σ Δ)) (ex-pickR (pick-prefix Γ) Λ f)
ex-pickR-ex-skips {Γ = Y ∷ Z ∷ Γ} {X = X} sw Λ f =
  ex (swapᴿ++ Λ sw) (ex (swapᴿ++ (Z ∷ Λ) sw)
    (ex-pickR-ex-prefix (pick-prefix Γ) sw f)) ∙
  ex-braid (braidᴿ++ Λ braid)
ex-pickR-ex-skips {X = X} (keep {A = Y} σ) Λ f =
  ex (swapᴿ++ Λ sw) (ex-pickR-ex-skips σ (Y ∷ Λ) f) ∙
  ~ exex (disjointᴿ++ Λ (disjoint (swap-post σ _)))

ex-pickR-ex-suffix : ∀ {S X Δ Δ' C} (Γ Λ : Cxt) (σ : Swap Δ Δ')
  (f : S ∣ Λ ᴿ++ (Γ ++ X ∷ Δ) ⊢ C)
  → ex-pickR (pick-prefix Γ) Λ (ex (swapᴿ++ Λ (swap-pre Γ (keep σ))) f)
    ≗ ex (swapᴿ++ (X ∷ Λ) (swap-pre Γ σ)) (ex-pickR (pick-prefix Γ) Λ f)
ex-pickR-ex-suffix [] Λ σ f = refl
ex-pickR-ex-suffix (Y ∷ Γ) Λ σ f =
  ex (swapᴿ++ Λ sw) (ex-pickR-ex-suffix Γ (Y ∷ Λ) σ f) ∙
  ~ exex (disjointᴿ++ Λ (disjoint (swap-pre Γ σ)))

-- Interchanging the order of two consecutive gathers is the braid law.
ex-pickR-ex-two : ∀ {S X Y Δ C} (Γ Λ : Cxt)
  (f : S ∣ Λ ᴿ++ (Γ ++ X ∷ Y ∷ Δ) ⊢ C)
  → ex (swapᴿ++ Λ sw) (ex-pickR (pick-prefix Γ) (X ∷ Λ) (ex-pickR (pick-prefix Γ) Λ f))
    ≗ ex-pickR (pick-prefix Γ) (Y ∷ Λ)
      (ex-pickR (pick-prefix Γ) Λ (ex (swapᴿ++ Λ (swap-pre Γ sw)) f))
ex-pickR-ex-two [] Λ f = refl
ex-pickR-ex-two {X = X} {Y} (Z ∷ Γ) Λ f =
  ex (swapᴿ++ Λ sw) (ex (swapᴿ++ (X ∷ Λ) sw)
    (ex-pickR-ex-prefix (pick-prefix Γ) sw (ex-pickR (pick-prefix Γ) (Z ∷ Λ) f))) ∙
  ex-braid (braidᴿ++ Λ braid) ∙
  ex (swapᴿ++ (Y ∷ Λ) sw) (ex (swapᴿ++ Λ sw) (ex-pickR-ex-two Γ (Z ∷ Λ) f)) ∙
  ex (swapᴿ++ (Y ∷ Λ) sw)
    (~ ex-pickR-ex-prefix (pick-prefix Γ) sw
      (ex-pickR (pick-prefix Γ) (Z ∷ Λ) (ex (swapᴿ++ (Z ∷ Λ) (swap-pre Γ sw)) f)))

-- Exchange after an ordinary prefix partition. The four laws distinguish
-- the two occurrences' allocations, without introducing a case predicate.
ex-part-ex-ll : ∀ {S Λ Ω Ξ Γ Δ Θ X Y C} (r : Part Λ Ω Ξ) (p : Part Γ Δ Θ) (Π : Cxt)
  (f : S ∣ Π ᴿ++ ((Λ ++ X ∷ Y ∷ Γ) ++ (Ω ++ Δ)) ⊢ C)
  → ex (swapᴿ++ Π (swap-pre Ξ sw)) (ex-part (part++ r (left (left p))) Π f)
    ≗ ex-part (part++ r (left (left p))) Π
      (ex (swapᴿ++ Π (swap-post (swap-pre Λ sw) (Ω ++ Δ))) f)
ex-part-ex-ll done p Π f = ~ ex-part-ex-prefix p sw f
ex-part-ex-ll (left {x = X} r) p Π f = ex-part-ex-ll r p (X ∷ Π) f
ex-part-ex-ll {Λ = Λ} {Ω = Y ∷ Ω} (right r) p Π f =
  ex-part-ex-ll r p (Y ∷ Π) (ex-pickR (pick-prefix _) Π f) ∙
  cong-ex-part (part++ r (left (left p))) (Y ∷ Π)
    (~ ex-pickR-ex-skips (swap-pre Λ sw) Π f)

ex-part-ex-rr : ∀ {S Λ Ω Ξ Γ Δ Θ X Y C} (r : Part Λ Ω Ξ) (p : Part Γ Δ Θ) (Π : Cxt)
  (f : S ∣ Π ᴿ++ ((Λ ++ Γ) ++ (Ω ++ X ∷ Y ∷ Δ)) ⊢ C)
  → ex (swapᴿ++ Π (swap-pre Ξ sw)) (ex-part (part++ r (right (right p))) Π f)
    ≗ ex-part (part++ r (right (right p))) Π
      (ex (swapᴿ++ Π (swap-pre (Λ ++ Γ) (swap-pre Ω sw))) f)
ex-part-ex-rr {Γ = Γ} {X = X} {Y} done p Π f =
  ~ ex-part-ex-prefix p sw _ ∙
  cong-ex-part p (X ∷ Y ∷ Π) (ex-pickR-ex-two Γ Π f)
ex-part-ex-rr (left {x = X} r) p Π f = ex-part-ex-rr r p (X ∷ Π) f
ex-part-ex-rr {Λ = Λ} {Ω = Y ∷ Ω} {Γ = Γ} (right r) p Π f =
  ex-part-ex-rr r p (Y ∷ Π) (ex-pickR (pick-prefix (Λ ++ Γ)) Π f) ∙
  cong-ex-part (part++ r (right (right p))) (Y ∷ Π)
    (~ ex-pickR-ex-suffix (Λ ++ Γ) Π (swap-pre Ω sw) f)

ex-part-ex-lr : ∀ {S Λ Ω Ξ Γ Δ Θ X Y C}
  (r : Part Λ Ω Ξ) (p : Part Γ Δ Θ) (Π : Cxt)
  (f : S ∣ Π ᴿ++ ((Λ ++ X ∷ Γ) ++ (Ω ++ Y ∷ Δ)) ⊢ C)
  → ex (swapᴿ++ Π (swap-pre Ξ sw)) (ex-part (part++ r (left (right p))) Π f)
    ≗ ex-part (part++ r (right (left p))) Π f
ex-part-ex-lr done p Π f = ~ ex-part-ex-prefix p sw _
ex-part-ex-lr (left {x = X} r) p Π f = ex-part-ex-lr r p (X ∷ Π) f
ex-part-ex-lr (right {x = X} r) p Π f =
  ex-part-ex-lr r p (X ∷ Π) (ex-pickR (pick-prefix _) Π f)

ex-part-ex-rl : ∀ {S Λ Ω Ξ Γ Δ Θ X Y C}
  (r : Part Λ Ω Ξ) (p : Part Γ Δ Θ) (Π : Cxt)
  (f : S ∣ Π ᴿ++ ((Λ ++ X ∷ Γ) ++ (Ω ++ Y ∷ Δ)) ⊢ C)
  → ex (swapᴿ++ Π (swap-pre Ξ sw)) (ex-part (part++ r (right (left p))) Π f)
    ≗ ex-part (part++ r (left (right p))) Π f
ex-part-ex-rl {X = X} {Y} done p Π f =
  ~ ex-part-ex-prefix p sw _ ∙
  cong-ex-part p (Y ∷ X ∷ Π) (ex-iso-prefix Π _)
ex-part-ex-rl (left {x = X} r) p Π f = ex-part-ex-rl r p (X ∷ Π) f
ex-part-ex-rl (right {x = X} r) p Π f =
  ex-part-ex-rl r p (X ∷ Π) (ex-pickR (pick-prefix _) Π f)

-- Tensor exchange with a reversed prefix partition. The ordinary prefix
-- t accumulates r, allowing structural recursion without context transports.
ex-part-⊗r-ll : ∀ {S Λ Ω Ξ Λ′ Ω′ Ξ′ Γ Δ Θ X Y A B}
  (r : Part Λ Ω Ξ) (t : Part Λ′ Ω′ Ξ′) (p : Part Γ Δ Θ)
  (f : S ∣ Λ ᴿ++ (Λ′ ++ X ∷ Y ∷ Γ) ⊢ A) (g : - ∣ Ω ᴿ++ (Ω′ ++ Δ) ⊢ B)
  → ex (swapᴿ++ Ξ (swap-pre Ξ′ sw))
      (ex-part (partᴿ++ r (part++ t (left (left p)))) [] (⊗r refl f g))
    ≗ ex-part (partᴿ++ r (part++ t (left (left p)))) [] (⊗r refl (ex (swapᴿ++ Λ (swap-pre Λ′ sw)) f) g)
ex-part-⊗r-ll {Λ′ = Λ′} done t p f g =
  ex-part-ex-ll t p [] (⊗r refl f g) ∙
  cong-ex-part (part++ t (left (left p))) [] (ex⊗r₁ (swap-pre Λ′ sw))
ex-part-⊗r-ll (left r) t p f g = ex-part-⊗r-ll r (left t) p f g
ex-part-⊗r-ll (right r) t p f g = ex-part-⊗r-ll r (right t) p f g

ex-part-⊗r-rr : ∀ {S Λ Ω Ξ Λ′ Ω′ Ξ′ Γ Δ Θ X Y A B}
  (r : Part Λ Ω Ξ) (t : Part Λ′ Ω′ Ξ′) (p : Part Γ Δ Θ)
  (f : S ∣ Λ ᴿ++ (Λ′ ++ Γ) ⊢ A) (g : - ∣ Ω ᴿ++ (Ω′ ++ X ∷ Y ∷ Δ) ⊢ B)
  → ex (swapᴿ++ Ξ (swap-pre Ξ′ sw))
      (ex-part (partᴿ++ r (part++ t (right (right p)))) [] (⊗r refl f g))
    ≗ ex-part (partᴿ++ r (part++ t (right (right p)))) [] (⊗r refl f (ex (swapᴿ++ Ω (swap-pre Ω′ sw)) g))
ex-part-⊗r-rr {Ω′ = Ω′} done t p f g =
  ex-part-ex-rr t p [] (⊗r refl f g) ∙
  cong-ex-part (part++ t (right (right p))) [] (ex⊗r₂ (swap-pre Ω′ sw))
ex-part-⊗r-rr (left r) t p f g = ex-part-⊗r-rr r (left t) p f g
ex-part-⊗r-rr (right r) t p f g = ex-part-⊗r-rr r (right t) p f g

ex-part-⊗r-lr : ∀ {S Λ Ω Ξ Λ′ Ω′ Ξ′ Γ Δ Θ X Y A B}
  (r : Part Λ Ω Ξ) (t : Part Λ′ Ω′ Ξ′) (p : Part Γ Δ Θ)
  (f : S ∣ Λ ᴿ++ (Λ′ ++ X ∷ Γ) ⊢ A) (g : - ∣ Ω ᴿ++ (Ω′ ++ Y ∷ Δ) ⊢ B)
  → ex (swapᴿ++ Ξ (swap-pre Ξ′ sw))
      (ex-part (partᴿ++ r (part++ t (left (right p)))) [] (⊗r refl f g))
    ≗ ex-part (partᴿ++ r (part++ t (right (left p)))) [] (⊗r refl f g)
ex-part-⊗r-lr done t p f g = ex-part-ex-lr t p [] (⊗r refl f g)
ex-part-⊗r-lr (left r) t p f g = ex-part-⊗r-lr r (left t) p f g
ex-part-⊗r-lr (right r) t p f g = ex-part-⊗r-lr r (right t) p f g

ex-part-⊗r-rl : ∀ {S Λ Ω Ξ Λ′ Ω′ Ξ′ Γ Δ Θ X Y A B}
  (r : Part Λ Ω Ξ) (t : Part Λ′ Ω′ Ξ′) (p : Part Γ Δ Θ)
  (f : S ∣ Λ ᴿ++ (Λ′ ++ X ∷ Γ) ⊢ A) (g : - ∣ Ω ᴿ++ (Ω′ ++ Y ∷ Δ) ⊢ B)
  → ex (swapᴿ++ Ξ (swap-pre Ξ′ sw))
      (ex-part (partᴿ++ r (part++ t (right (left p)))) [] (⊗r refl f g))
    ≗ ex-part (partᴿ++ r (part++ t (left (right p)))) [] (⊗r refl f g)
ex-part-⊗r-rl done t p f g = ex-part-ex-rl t p [] (⊗r refl f g)
ex-part-⊗r-rl (left r) t p f g = ex-part-⊗r-rl r (left t) p f g
ex-part-⊗r-rl (right r) t p f g = ex-part-⊗r-rl r (right t) p f g

