{-# OPTIONS --safe #-}

module SeqCalc.ImplEq (At : Set) where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open ≡-Reasoning
open import Utilities hiding (ex-pickR)
open import Formulae At
open import SeqCalc.Impl At public

infixl 15 _∙_

-- Only logical congruences and conversions generate this equality.
-- Ex congruence and the ex laws are established below.
data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where

-- -- equivalence relation
  refl : ∀{S Γ A} {f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S Γ A} {f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S Γ A} {f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h

-- -- congruence
  Il : ∀{Γ C} {f g : - ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗l : ∀{Γ A B C} {f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
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
  pass : ∀ {A Γ Δ C} (p : Pick A Γ Δ) {f g : just A ∣ Δ ⊢ C}
    → f ≗ g → pass p f ≗ pass p g
  ⊗r : ∀ {S Γ Δ Ξ A B} (p : Part Γ Δ Ξ)
    {f f' : S ∣ Γ ⊢ A} {g g' : - ∣ Δ ⊢ B}
    → f ≗ f' → g ≗ g' → ⊗r p f g ≗ ⊗r p f' g'

-- -- η-conversions
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r (right done) ax (pass here ax))
  ax∧ : {A B : Fma} → ax {A ∧ B} ≗ ∧r (∧l₁ ax) (∧l₂ ax)
  ax∨ : {A B : Fma} → ax {A ∨ B} ≗ ∨l (∨r₁ ax) (∨r₂ ax)

-- -- permutative conversions
  ⊗rpass : ∀ {Γ Δ Ξ Ω X A B} (p : Part Γ Δ Ξ) (q : Pick X Γ Ω)
    {f : just X ∣ Ω ⊢ A} {g : - ∣ Δ ⊢ B}
    → let r = pull-left p q in
      ⊗r p (pass q f) g ≗ pass (proj₁ (proj₂ r)) (⊗r (proj₂ (proj₂ r)) f g)
  ⊗rIl : ∀ {Γ Δ Ξ A B} (p : Part Γ Δ Ξ)
    {f : - ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r p (Il f) g ≗ Il (⊗r p f g)
  ⊗r⊗l : ∀ {Γ Δ Ξ X Y A B} (p : Part Γ Δ Ξ)
    {f : just X ∣ Y ∷ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r p (⊗l f) g ≗ ⊗l (⊗r (left p) f g)
  ⊗r∧l₁ : ∀ {Γ Δ Ξ X Y A B} (p : Part Γ Δ Ξ)
    {f : just X ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r p (∧l₁ {B = Y} f) g ≗ ∧l₁ (⊗r p f g)
  ⊗r∧l₂ : ∀ {Γ Δ Ξ X Y A B} (p : Part Γ Δ Ξ)
    {f : just Y ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r p (∧l₂ {A = X} f) g ≗ ∧l₂ (⊗r p f g)
  ⊗r∨l : ∀ {Γ Δ Ξ X Y A B} (p : Part Γ Δ Ξ)
    {f : just X ∣ Γ ⊢ A} {f' : just Y ∣ Γ ⊢ A} {g : - ∣ Δ ⊢ B}
    → ⊗r p (∨l f f') g ≗ ∨l (⊗r p f g) (⊗r p f' g)
  ∧rpass : ∀ {Γ Δ X A B} (p : Pick X Γ Δ)
    {f : just X ∣ Δ ⊢ A} {g : just X ∣ Δ ⊢ B}
    → ∧r (pass p f) (pass p g) ≗ pass p (∧r f g)
  ∨r₁pass : ∀ {Γ Δ X A B} (p : Pick X Γ Δ) {f : just X ∣ Δ ⊢ A}
    → ∨r₁ {B = B} (pass p f) ≗ pass p (∨r₁ f)
  ∨r₂pass : ∀ {Γ Δ X A B} (p : Pick X Γ Δ) {f : just X ∣ Δ ⊢ B}
    → ∨r₂ {A = A} (pass p f) ≗ pass p (∨r₂ f)
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

-- An accumulated prefix can be supplied to ex-pass directly, or lifted
-- into both the exchange witness and the selected occurrence.
ex-passᴿ++ : ∀ Λ {A Γ Δ Ω C} (σ : Swap Γ Δ) (p : Pick A Γ Ω)
  (f : just A ∣ Λ ᴿ++ Ω ⊢ C)
  → ex (swapᴿ++ Λ σ) (pass (pickᴿ++ Λ p) f) ≡ ex-pass Λ σ p f
ex-passᴿ++ [] σ p f = refl
ex-passᴿ++ (B ∷ Λ) σ p f = ex-passᴿ++ Λ (keep σ) (there p) f

-- The same prefix property for tensor-right, keeping the partition of
-- the accumulated prefix between the two premises.
ex-⊗rᴿ++ : ∀ {S Λ Ω Ξ Γ Δ Θ Θ' A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : S ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex (swapᴿ++ Ξ σ) (⊗r (partᴿ++ r p) f g) ≡ ex-⊗r r σ p f g
ex-⊗rᴿ++ done σ p f g = refl
ex-⊗rᴿ++ (left r) σ p f g = ex-⊗rᴿ++ r (keep σ) (left p) f g
ex-⊗rᴿ++ (right r) σ p f g = ex-⊗rᴿ++ r (keep σ) (right p) f g

-- Involution is a theorem about raw derivations, not an equation generator.
ex-iso : ∀ {S Γ Δ C} (σ : Swap Γ Δ) (f : S ∣ Γ ⊢ C)
  → ex (swap-sym σ) (ex σ f) ≡ f
ex-pass-iso : ∀ (Λ : Cxt) {A Γ Δ Ω C} (σ : Swap Γ Δ) (p : Pick A Γ Ω)
  → (f : just A ∣ Λ ᴿ++ Ω ⊢ C)
  → ex (swapᴿ++ Λ (swap-sym σ)) (ex-pass Λ σ p f) ≡ pass (pickᴿ++ Λ p) f

ex-⊗r-iso : ∀ {S Λ Ω Ξ Γ Δ Θ Θ' A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : S ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex (swapᴿ++ Ξ (swap-sym σ)) (ex-⊗r r σ p f g)
    ≡ ⊗r (partᴿ++ r p) f g

ex-iso σ (pass p f) = ex-pass-iso [] σ p f
ex-iso σ (Il f) = cong Il (ex-iso σ f)
ex-iso σ (⊗r p f g) = ex-⊗r-iso done σ p f g
ex-iso σ (⊗l f) = cong ⊗l (ex-iso (keep σ) f)
ex-iso σ (∧r f g) = cong₂ ∧r (ex-iso σ f) (ex-iso σ g)
ex-iso σ (∧l₁ f) = cong ∧l₁ (ex-iso σ f)
ex-iso σ (∧l₂ f) = cong ∧l₂ (ex-iso σ f)
ex-iso σ (∨r₁ f) = cong ∨r₁ (ex-iso σ f)
ex-iso σ (∨r₂ f) = cong ∨r₂ (ex-iso σ f)
ex-iso σ (∨l f g) = cong₂ ∨l (ex-iso σ f) (ex-iso σ g)

ex-pass-iso Λ sw here f = ex-passᴿ++ Λ sw (there here) f
ex-pass-iso Λ sw (there here) f = ex-passᴿ++ Λ sw here f
ex-pass-iso Λ sw (there (there p)) f = trans
  (ex-passᴿ++ Λ sw (there (there p)) (ex (swapᴿ++ Λ sw) f))
  (cong (pass (pickᴿ++ Λ (there (there p))))
    (trans (cong (λ τ → ex τ (ex (swapᴿ++ Λ sw) f)) (sym (swap-symᴿ++ Λ sw)))
      (ex-iso (swapᴿ++ Λ sw) f)))
ex-pass-iso Λ (keep σ) here f = trans
  (ex-passᴿ++ Λ (keep (swap-sym σ)) here (ex (swapᴿ++ Λ σ) f))
  (cong (pass (pickᴿ++ Λ here))
    (trans (cong (λ τ → ex τ (ex (swapᴿ++ Λ σ) f)) (sym (swap-symᴿ++ Λ σ)))
      (ex-iso (swapᴿ++ Λ σ) f)))
ex-pass-iso Λ (keep σ) (there p) f = ex-pass-iso (_ ∷ Λ) σ p f

-- When both exchanged occurrences belong to one premise, use its
-- induction hypothesis. Mixed occurrences only change the partition.
ex-⊗r-iso {Λ = Λ} r sw (left (left p)) f g = trans
  (ex-⊗rᴿ++ r sw (left (left p)) (ex (swapᴿ++ Λ sw) f) g)
  (cong (λ h → ⊗r (partᴿ++ r (left (left p))) h g)
    (trans (cong (λ τ → ex τ (ex (swapᴿ++ Λ sw) f)) (sym (swap-symᴿ++ Λ sw)))
      (ex-iso (swapᴿ++ Λ sw) f)))
ex-⊗r-iso {Ω = Ω} r sw (right (right p)) f g = trans
  (ex-⊗rᴿ++ r sw (right (right p)) f (ex (swapᴿ++ Ω sw) g))
  (cong (⊗r (partᴿ++ r (right (right p))) f)
    (trans (cong (λ τ → ex τ (ex (swapᴿ++ Ω sw) g)) (sym (swap-symᴿ++ Ω sw)))
      (ex-iso (swapᴿ++ Ω sw) g)))
ex-⊗r-iso r sw (left (right p)) f g = ex-⊗rᴿ++ r sw (right (left p)) f g
ex-⊗r-iso r sw (right (left p)) f g = ex-⊗rᴿ++ r sw (left (right p)) f g
ex-⊗r-iso r (keep σ) (left p) f g = ex-⊗r-iso (left r) σ p f g
ex-⊗r-iso r (keep σ) (right p) f g = ex-⊗r-iso (right r) σ p f g



-- For a contiguous partition, a swap confined to one premise changes
-- only that derivation. Keep the accumulated prefix partition arbitrary
-- so the statements remain applicable while traversing keep constructors.
ex-⊗r-part₁ : ∀ {S Λ Ω Ξ Γ Γ' Δ A B} (r : Part Λ Ω Ξ)
  (σ : Swap Γ Γ') (f : S ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r (swap-post σ Δ) (part Γ Δ) f g
    ≡ ⊗r (partᴿ++ r (part Γ' Δ)) (ex (swapᴿ++ Λ σ) f) g
ex-⊗r-part₁ r sw f g = refl
ex-⊗r-part₁ r (keep σ) f g = ex-⊗r-part₁ (left r) σ f g

ex-⊗r-part₂ : ∀ {S Λ Ω Ξ Δ Δ' A B} (r : Part Λ Ω Ξ) (Γ : Cxt)
  (σ : Swap Δ Δ') (f : S ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r (swap-pre Γ σ) (part Γ Δ) f g
    ≡ ⊗r (partᴿ++ r (part Γ Δ')) f (ex (swapᴿ++ Ω σ) g)
ex-⊗r-part₂ r [] sw f g = refl
ex-⊗r-part₂ r [] (keep σ) f g = ex-⊗r-part₂ (right r) [] σ f g
ex-⊗r-part₂ r (X ∷ Γ) σ f g = ex-⊗r-part₂ (left r) Γ σ f g

-- Tensor commutation in a form without concatenation transports.
ex-⊗r₁ : ∀ {S Γ Γ' Δ A B} (σ : Swap Γ Γ')
  (f : S ∣ Γ ⊢ A) (g : - ∣ Δ ⊢ B)
  → ex (swap-post σ Δ) (⊗r (part Γ Δ) f g)
    ≡ ⊗r (part Γ' Δ) (ex σ f) g
ex-⊗r₁ σ f g = ex-⊗r-part₁ done σ f g

ex-⊗r₂ : ∀ {S Γ Δ Δ' A B} (σ : Swap Δ Δ')
  (f : S ∣ Γ ⊢ A) (g : - ∣ Δ ⊢ B)
  → ex (swap-pre Γ σ) (⊗r (part Γ Δ) f g)
    ≡ ⊗r (part Γ Δ') f (ex σ g)
ex-⊗r₂ {Γ = Γ} σ f g = ex-⊗r-part₂ done Γ σ f g

-- Exchange leaves a selection in its fixed prefix in place.
ex-pass-prefixᴿ++ : ∀ {A Λ Λ' Γ Δ C} (q : Pick A Λ Λ') (σ : Swap Γ Δ)
  (f : just A ∣ Λ' ᴿ++ Γ ⊢ C)
  → ex (swapᴿ++ Λ σ) (pass (pick-prefixᴿ++ q Γ) f)
    ≡ pass (pick-prefixᴿ++ q Δ) (ex (swapᴿ++ Λ' σ) f)
ex-pass-prefixᴿ++ (here {xs = Λ}) σ f = ex-passᴿ++ Λ (keep σ) here f
ex-pass-prefixᴿ++ (there q) σ f = ex-pass-prefixᴿ++ q (keep σ) f

ex-⊗r-pass-prefix : ∀ {Λ Λ' Ω Ξ Γ Δ Θ Θ' X A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ) (q : Pick X Λ Λ')
  (f : just X ∣ Λ' ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r σ p (pass (pick-prefixᴿ++ q Γ) f) g
    ≗ let t = pull-left r q in
      pass (pick-prefixᴿ++ (proj₁ (proj₂ t)) Θ') (ex-⊗r (proj₂ (proj₂ t)) σ p f g)
ex-⊗r-pass-prefix {Λ' = Λ'} r sw (left (left p)) q f g =
  ≡to≗ (cong (λ h → ⊗r (partᴿ++ r (left (left p))) h g) (ex-pass-prefixᴿ++ q sw f)) ∙
  ⊗rpass (partᴿ++ r (left (left p))) (pick-prefixᴿ++ q _) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) (ex (swapᴿ++ Λ' sw) f) g))
    (pull-left-prefixᴿ++ r q (left (left p))))
ex-⊗r-pass-prefix {Ω = Ω} r sw (right (right p)) q f g =
  ⊗rpass (partᴿ++ r (right (right p))) (pick-prefixᴿ++ q _) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) f (ex (swapᴿ++ Ω sw) g)))
    (pull-left-prefixᴿ++ r q (right (right p))))
ex-⊗r-pass-prefix r sw (left (right p)) q f g =
  ⊗rpass (partᴿ++ r (right (left p))) (pick-prefixᴿ++ q _) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) f g))
    (pull-left-prefixᴿ++ r q (right (left p))))
ex-⊗r-pass-prefix r sw (right (left p)) q f g =
  ⊗rpass (partᴿ++ r (left (right p))) (pick-prefixᴿ++ q _) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) f g))
    (pull-left-prefixᴿ++ r q (left (right p))))
ex-⊗r-pass-prefix {Θ' = Θ'} r (keep σ) (left p) q f g =
  ex-⊗r-pass-prefix (left r) σ p (there q) f g ∙
  ≡to≗ (cong (λ t → pass (pick-prefixᴿ++ (proj₁ (proj₂ t)) _) (ex-⊗r (proj₂ (proj₂ t)) σ p f g))
    (pull-left-left r q))
ex-⊗r-pass-prefix {Θ' = Θ'} r (keep σ) (right p) q f g =
  ex-⊗r-pass-prefix (right r) σ p q f g ∙
  ≡to≗ (cong (λ t → pass (pick-prefixᴿ++ (proj₁ (proj₂ t)) _) (ex-⊗r (proj₂ (proj₂ t)) σ p f g))
    (pull-left-right r q))

-- Naturality of tensor-pass when the selected occurrence is in the
-- unprocessed suffix. The prefix-selection lemma handles passing it.
ex-⊗r-pass : ∀ {Λ Ω Ξ Γ Δ Θ Θ' Γ' X A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ) (q : Pick X Γ Γ')
  (f : just X ∣ Λ ᴿ++ Γ' ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r σ p (pass (pickᴿ++ Λ q) f) g
    ≗ let t = pull-left p q in
      ex-pass Ξ σ (proj₁ (proj₂ t)) (⊗r (partᴿ++ r (proj₂ (proj₂ t))) f g)
ex-⊗r-pass {Λ = Λ} r sw (left (left p)) here f g =
  ≡to≗ (cong (λ h → ⊗r (partᴿ++ r (left (left p))) h g) (ex-passᴿ++ Λ sw here f)) ∙
  ⊗rpass (partᴿ++ r (left (left p))) (pickᴿ++ Λ (there here)) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) f g))
    (pull-leftᴿ++ r (left (left p)) (there here)))
ex-⊗r-pass {Λ = Λ} r sw (left (left p)) (there here) f g =
  ≡to≗ (cong (λ h → ⊗r (partᴿ++ r (left (left p))) h g) (ex-passᴿ++ Λ sw (there here) f)) ∙
  ⊗rpass (partᴿ++ r (left (left p))) (pickᴿ++ Λ here) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) f g))
    (pull-leftᴿ++ r (left (left p)) here))
ex-⊗r-pass {Λ = Λ} {Ξ = Ξ} r sw (left (left p)) (there (there q)) f g
  with pull-left p q in eq
... | _ , t , p' =
  ≡to≗ (cong (λ h → ⊗r (partᴿ++ r (left (left p))) h g) (ex-passᴿ++ Λ sw (there (there q)) f)) ∙
  subst (_≗_ _) (cong (λ u → pass (pickᴿ++ Ξ (there (there (proj₁ (proj₂ u)))))
    (⊗r (partᴿ++ r (left (left (proj₂ (proj₂ u))))) (ex (swapᴿ++ Λ sw) f) g)) eq)
    (⊗rpass (partᴿ++ r (left (left p))) (pickᴿ++ Λ (there (there q))) ∙
      ≡to≗ (cong (λ u → pass (proj₁ (proj₂ u)) (⊗r (proj₂ (proj₂ u)) (ex (swapᴿ++ Λ sw) f) g))
        (pull-leftᴿ++ r (left (left p)) (there (there q))))) ∙
  ≡to≗ (cong (pass (pickᴿ++ Ξ (there (there t)))) (sym (ex-⊗rᴿ++ r sw (left (left p')) f g)))
ex-⊗r-pass {Λ = Λ} {Ω = Ω} {Ξ = Ξ} r sw (right (right p)) q f g
  with pull-left p q in eq
... | _ , t , p' =
  subst (_≗_ _) (cong (λ u → pass (pickᴿ++ Ξ (there (there (proj₁ (proj₂ u)))))
    (⊗r (partᴿ++ r (right (right (proj₂ (proj₂ u))))) f (ex (swapᴿ++ Ω sw) g))) eq)
    (⊗rpass (partᴿ++ r (right (right p))) (pickᴿ++ Λ q) ∙
      ≡to≗ (cong (λ u → pass (proj₁ (proj₂ u)) (⊗r (proj₂ (proj₂ u)) f (ex (swapᴿ++ Ω sw) g)))
        (pull-leftᴿ++ r (right (right p)) q))) ∙
  ≡to≗ (cong (pass (pickᴿ++ Ξ (there (there t)))) (sym (ex-⊗rᴿ++ r sw (right (right p')) f g)))
ex-⊗r-pass {Λ = Λ} r sw (left (right p)) here f g =
  ⊗rpass (partᴿ++ r (right (left p))) (pickᴿ++ Λ here) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) f g))
    (pull-leftᴿ++ r (right (left p)) here))
ex-⊗r-pass {Λ = Λ} {Ξ = Ξ} r sw (left (right p)) (there q) f g
  with pull-left p q in eq
... | _ , t , p' =
  subst (_≗_ _) (cong (λ u → pass (pickᴿ++ Ξ (there (there (proj₁ (proj₂ u)))))
    (⊗r (partᴿ++ r (right (left (proj₂ (proj₂ u))))) f g)) eq)
    (⊗rpass (partᴿ++ r (right (left p))) (pickᴿ++ Λ (there q)) ∙
      ≡to≗ (cong (λ u → pass (proj₁ (proj₂ u)) (⊗r (proj₂ (proj₂ u)) f g))
        (pull-leftᴿ++ r (right (left p)) (there q)))) ∙
  ≡to≗ (cong (pass (pickᴿ++ Ξ (there (there t)))) (sym (ex-⊗rᴿ++ r sw (left (right p')) f g)))
ex-⊗r-pass {Λ = Λ} r sw (right (left p)) here f g =
  ⊗rpass (partᴿ++ r (left (right p))) (pickᴿ++ Λ here) ∙
  ≡to≗ (cong (λ t → pass (proj₁ (proj₂ t)) (⊗r (proj₂ (proj₂ t)) f g))
    (pull-leftᴿ++ r (left (right p)) here))
ex-⊗r-pass {Λ = Λ} {Ξ = Ξ} r sw (right (left p)) (there q) f g
  with pull-left p q in eq
... | _ , t , p' =
  subst (_≗_ _) (cong (λ u → pass (pickᴿ++ Ξ (there (there (proj₁ (proj₂ u)))))
    (⊗r (partᴿ++ r (left (right (proj₂ (proj₂ u))))) f g)) eq)
    (⊗rpass (partᴿ++ r (left (right p))) (pickᴿ++ Λ (there q)) ∙
      ≡to≗ (cong (λ u → pass (proj₁ (proj₂ u)) (⊗r (proj₂ (proj₂ u)) f g))
        (pull-leftᴿ++ r (left (right p)) (there q)))) ∙
  ≡to≗ (cong (pass (pickᴿ++ Ξ (there (there t)))) (sym (ex-⊗rᴿ++ r sw (right (left p')) f g)))
ex-⊗r-pass {Ξ = Ξ} r (keep σ) (left p) here f g =
  ex-⊗r-pass-prefix (left r) σ p here f g ∙
  ≡to≗ (sym (cong (pass (pickᴿ++ Ξ here)) (ex-⊗rᴿ++ r σ p f g)))
ex-⊗r-pass {Ξ = Ξ} r (keep σ) (left p) (there q) f g =
  ex-⊗r-pass (left r) σ p q f g ∙
  ≡to≗ (sym (cong (λ t → ex-pass Ξ (keep σ) (proj₁ (proj₂ t))
    (⊗r (partᴿ++ r (proj₂ (proj₂ t))) f g)) (pull-left-left p q)))
ex-⊗r-pass {Ξ = Ξ} r (keep σ) (right p) q f g =
  ex-⊗r-pass (right r) σ p q f g ∙
  ≡to≗ (sym (cong (λ t → ex-pass Ξ (keep σ) (proj₁ (proj₂ t))
    (⊗r (partᴿ++ r (proj₂ (proj₂ t))) f g)) (pull-left-right p q)))

-- Tensor-left exposes X at the front of the left premise. In a reversed
-- prefix this is represented by appending X, with explicit transports.
ex-⊗r-⊗l : ∀ {Λ Ω Ξ Γ Δ Θ Θ' X Y A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : just X ∣ Y ∷ (Λ ᴿ++ Γ) ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r σ p (⊗l f) g
    ≗ ⊗l (subst-cxt (ᴿ++-snoc Ξ Y Θ')
      (ex-⊗r (part-snoc-left r Y) σ p (subst-cxt (sym (ᴿ++-snoc Λ Y Γ)) f) g))
ex-⊗r-⊗l {Λ = Λ} {Ξ = Ξ} {Γ = Γ} {Y = Y} r sw (left (left p)) f g =
  ⊗r⊗l (partᴿ++ r (left (left p))) ∙ ≡to≗ (sym (cong ⊗l (trans
    (⊗r-subst (ᴿ++-snoc Λ Y _) (ᴿ++-snoc Ξ Y _)
      (partᴿ++ (part-snoc-left r Y) (left (left p)))
      (ex (swapᴿ++ (Λ ++ [ Y ]) sw) (subst-cxt (sym (ᴿ++-snoc Λ Y Γ)) f)) g)
    (cong₂ (λ t h → ⊗r t h g) (partᴿ++-snoc-left r Y (left (left p)))
      (trans
        (sym (ex-subst (ᴿ++-snoc Λ Y Γ) (ᴿ++-snoc Λ Y _) (swapᴿ++ (Λ ++ [ Y ]) sw)
          (subst-cxt (sym (ᴿ++-snoc Λ Y Γ)) f)))
        (cong₂ ex (swapᴿ++-snoc Λ Y sw) (subst-cxt-cancel (ᴿ++-snoc Λ Y Γ) f)))))))
ex-⊗r-⊗l {Λ = Λ} {Ω = Ω} {Ξ = Ξ} {Γ = Γ} {Y = Y} r sw (right (right p)) f g =
  ⊗r⊗l (partᴿ++ r (right (right p))) ∙ ≡to≗ (sym (cong ⊗l (trans
    (⊗r-subst (ᴿ++-snoc Λ Y Γ) (ᴿ++-snoc Ξ Y _)
      (partᴿ++ (part-snoc-left r Y) (right (right p)))
      (subst-cxt (sym (ᴿ++-snoc Λ Y Γ)) f) (ex (swapᴿ++ Ω sw) g))
    (cong₂ (λ t h → ⊗r t h (ex (swapᴿ++ Ω sw) g))
      (partᴿ++-snoc-left r Y (right (right p))) (subst-cxt-cancel (ᴿ++-snoc Λ Y Γ) f)))))
ex-⊗r-⊗l {Λ = Λ} {Ξ = Ξ} {Γ = Γ} {Y = Y} r sw (left (right p)) f g =
  ⊗r⊗l (partᴿ++ r (right (left p))) ∙ ≡to≗ (sym (cong ⊗l (trans
    (⊗r-subst (ᴿ++-snoc Λ Y Γ) (ᴿ++-snoc Ξ Y _)
      (partᴿ++ (part-snoc-left r Y) (right (left p))) (subst-cxt (sym (ᴿ++-snoc Λ Y Γ)) f) g)
    (cong₂ (λ t h → ⊗r t h g) (partᴿ++-snoc-left r Y (right (left p)))
      (subst-cxt-cancel (ᴿ++-snoc Λ Y Γ) f)))))
ex-⊗r-⊗l {Λ = Λ} {Ξ = Ξ} {Γ = Γ} {Y = Y} r sw (right (left p)) f g =
  ⊗r⊗l (partᴿ++ r (left (right p))) ∙ ≡to≗ (sym (cong ⊗l (trans
    (⊗r-subst (ᴿ++-snoc Λ Y Γ) (ᴿ++-snoc Ξ Y _)
      (partᴿ++ (part-snoc-left r Y) (left (right p))) (subst-cxt (sym (ᴿ++-snoc Λ Y Γ)) f) g)
    (cong₂ (λ t h → ⊗r t h g) (partᴿ++-snoc-left r Y (left (right p)))
      (subst-cxt-cancel (ᴿ++-snoc Λ Y Γ) f)))))
ex-⊗r-⊗l r (keep σ) (left p) f g = ex-⊗r-⊗l (left r) σ p f g
ex-⊗r-⊗l r (keep σ) (right p) f g = ex-⊗r-⊗l (right r) σ p f g

-- The remaining commuting conversions follow the direct helper cases.
ex-⊗r-Il : ∀ {Λ Ω Ξ Γ Δ Θ Θ' A B} (r : Part Λ Ω Ξ) (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : - ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r σ p (Il f) g ≗ Il (ex-⊗r r σ p f g)
ex-⊗r-Il r sw (left (left p)) f g = ⊗rIl (partᴿ++ r (left (left p)))
ex-⊗r-Il r sw (right (right p)) f g = ⊗rIl (partᴿ++ r (right (right p)))
ex-⊗r-Il r sw (left (right p)) f g = ⊗rIl (partᴿ++ r (right (left p)))
ex-⊗r-Il r sw (right (left p)) f g = ⊗rIl (partᴿ++ r (left (right p)))
ex-⊗r-Il r (keep σ) (left p) f g = ex-⊗r-Il (left r) σ p f g
ex-⊗r-Il r (keep σ) (right p) f g = ex-⊗r-Il (right r) σ p f g

ex-⊗r-∧l₁ : ∀ {Λ Ω Ξ Γ Δ Θ Θ' X Y A B} (r : Part Λ Ω Ξ) (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : just X ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r σ p (∧l₁ {B = Y} f) g ≗ ∧l₁ (ex-⊗r r σ p f g)
ex-⊗r-∧l₁ r sw (left (left p)) f g = ⊗r∧l₁ (partᴿ++ r (left (left p)))
ex-⊗r-∧l₁ r sw (right (right p)) f g = ⊗r∧l₁ (partᴿ++ r (right (right p)))
ex-⊗r-∧l₁ r sw (left (right p)) f g = ⊗r∧l₁ (partᴿ++ r (right (left p)))
ex-⊗r-∧l₁ r sw (right (left p)) f g = ⊗r∧l₁ (partᴿ++ r (left (right p)))
ex-⊗r-∧l₁ r (keep σ) (left p) f g = ex-⊗r-∧l₁ (left r) σ p f g
ex-⊗r-∧l₁ r (keep σ) (right p) f g = ex-⊗r-∧l₁ (right r) σ p f g

ex-⊗r-∧l₂ : ∀ {Λ Ω Ξ Γ Δ Θ Θ' X Y A B} (r : Part Λ Ω Ξ) (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : just Y ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r σ p (∧l₂ {A = X} f) g ≗ ∧l₂ (ex-⊗r r σ p f g)
ex-⊗r-∧l₂ r sw (left (left p)) f g = ⊗r∧l₂ (partᴿ++ r (left (left p)))
ex-⊗r-∧l₂ r sw (right (right p)) f g = ⊗r∧l₂ (partᴿ++ r (right (right p)))
ex-⊗r-∧l₂ r sw (left (right p)) f g = ⊗r∧l₂ (partᴿ++ r (right (left p)))
ex-⊗r-∧l₂ r sw (right (left p)) f g = ⊗r∧l₂ (partᴿ++ r (left (right p)))
ex-⊗r-∧l₂ r (keep σ) (left p) f g = ex-⊗r-∧l₂ (left r) σ p f g
ex-⊗r-∧l₂ r (keep σ) (right p) f g = ex-⊗r-∧l₂ (right r) σ p f g

ex-⊗r-∨l : ∀ {Λ Ω Ξ Γ Δ Θ Θ' X Y A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : just X ∣ Λ ᴿ++ Γ ⊢ A) (f' : just Y ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-⊗r r σ p (∨l f f') g ≗ ∨l (ex-⊗r r σ p f g) (ex-⊗r r σ p f' g)
ex-⊗r-∨l r sw (left (left p)) f f' g = ⊗r∨l (partᴿ++ r (left (left p)))
ex-⊗r-∨l r sw (right (right p)) f f' g = ⊗r∨l (partᴿ++ r (right (right p)))
ex-⊗r-∨l r sw (left (right p)) f f' g = ⊗r∨l (partᴿ++ r (right (left p)))
ex-⊗r-∨l r sw (right (left p)) f f' g = ⊗r∨l (partᴿ++ r (left (right p)))
ex-⊗r-∨l r (keep σ) (left p) f f' g = ex-⊗r-∨l (left r) σ p f f' g
ex-⊗r-∨l r (keep σ) (right p) f f' g = ex-⊗r-∨l (right r) σ p f f' g

ex-pass-∧r : ∀ Λ {X Γ Δ Ω A B} (σ : Swap Γ Δ) (p : Pick X Γ Ω)
  (f : just X ∣ Λ ᴿ++ Ω ⊢ A) (g : just X ∣ Λ ᴿ++ Ω ⊢ B)
  → ∧r (ex-pass Λ σ p f) (ex-pass Λ σ p g) ≗ ex-pass Λ σ p (∧r f g)
ex-pass-∧r Λ sw (here) f g = ∧rpass (pickᴿ++ Λ (there here))
ex-pass-∧r Λ sw (there here) f g = ∧rpass (pickᴿ++ Λ (here))
ex-pass-∧r Λ sw (there (there p)) f g = ∧rpass (pickᴿ++ Λ (there (there p)))
ex-pass-∧r Λ (keep σ) here f g = ∧rpass (pickᴿ++ Λ here)
ex-pass-∧r Λ (keep {A = Z} σ) (there p) f g = ex-pass-∧r (Z ∷ Λ) σ p f g

ex-pass-∨r₁ : ∀ Λ {X Γ Δ Ω A B} (σ : Swap Γ Δ) (p : Pick X Γ Ω)
  (f : just X ∣ Λ ᴿ++ Ω ⊢ A) 
  → ∨r₁ {B = B} (ex-pass Λ σ p f) ≗ ex-pass Λ σ p (∨r₁ f)
ex-pass-∨r₁ Λ sw (here) f = ∨r₁pass (pickᴿ++ Λ (there here))
ex-pass-∨r₁ Λ sw (there here) f = ∨r₁pass (pickᴿ++ Λ (here))
ex-pass-∨r₁ Λ sw (there (there p)) f = ∨r₁pass (pickᴿ++ Λ (there (there p)))
ex-pass-∨r₁ Λ (keep σ) here f = ∨r₁pass (pickᴿ++ Λ here)
ex-pass-∨r₁ Λ (keep {A = Z} σ) (there p) f = ex-pass-∨r₁ (Z ∷ Λ) σ p f

ex-pass-∨r₂ : ∀ Λ {X Γ Δ Ω A B} (σ : Swap Γ Δ) (p : Pick X Γ Ω)
  (f : just X ∣ Λ ᴿ++ Ω ⊢ B) 
  → ∨r₂ {A = A} (ex-pass Λ σ p f) ≗ ex-pass Λ σ p (∨r₂ f)
ex-pass-∨r₂ Λ sw (here) f = ∨r₂pass (pickᴿ++ Λ (there here))
ex-pass-∨r₂ Λ sw (there here) f = ∨r₂pass (pickᴿ++ Λ (here))
ex-pass-∨r₂ Λ sw (there (there p)) f = ∨r₂pass (pickᴿ++ Λ (there (there p)))
ex-pass-∨r₂ Λ (keep σ) here f = ∨r₂pass (pickᴿ++ Λ here)
ex-pass-∨r₂ Λ (keep {A = Z} σ) (there p) f = ex-pass-∨r₂ (Z ∷ Λ) σ p f

-- Ex congruence follows the same direct selection/partition cases.
cong-ex : ∀ {S Γ Δ C} (σ : Swap Γ Δ) {f g : S ∣ Γ ⊢ C}
  → f ≗ g → ex σ f ≗ ex σ g
cong-ex-pass : ∀ Λ {A Γ Δ Ω C} (σ : Swap Γ Δ) (p : Pick A Γ Ω)
  {f g : just A ∣ Λ ᴿ++ Ω ⊢ C} → f ≗ g → ex-pass Λ σ p f ≗ ex-pass Λ σ p g
cong-ex-⊗r : ∀ {S Λ Ω Ξ Γ Δ Θ Θ' A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  {f f' : S ∣ Λ ᴿ++ Γ ⊢ A} {g g' : - ∣ Ω ᴿ++ Δ ⊢ B}
  → f ≗ f' → g ≗ g' → ex-⊗r r σ p f g ≗ ex-⊗r r σ p f' g'

cong-ex σ refl = refl
cong-ex σ (~ eq) = ~ cong-ex σ eq
cong-ex σ (eq ∙ eq') = cong-ex σ eq ∙ cong-ex σ eq'
cong-ex σ (Il eq) = Il (cong-ex σ eq)
cong-ex σ (⊗l eq) = ⊗l (cong-ex (keep σ) eq)
cong-ex σ (∧l₁ eq) = ∧l₁ (cong-ex σ eq)
cong-ex σ (∧l₂ eq) = ∧l₂ (cong-ex σ eq)
cong-ex σ (∨r₁ eq) = ∨r₁ (cong-ex σ eq)
cong-ex σ (∨r₂ eq) = ∨r₂ (cong-ex σ eq)
cong-ex σ (∧r eq eq') = ∧r (cong-ex σ eq) (cong-ex σ eq')
cong-ex σ (∨l eq eq') = ∨l (cong-ex σ eq) (cong-ex σ eq')
cong-ex σ (pass p eq) = cong-ex-pass [] σ p eq
cong-ex σ (⊗r p eq eq') = cong-ex-⊗r done σ p eq eq'
cong-ex σ (⊗rpass p q {f = f} {g}) = ex-⊗r-pass done σ p q f g
cong-ex σ (⊗rIl p {f = f} {g}) = ex-⊗r-Il done σ p f g
cong-ex σ (⊗r⊗l p {f = f} {g}) = ex-⊗r-⊗l done σ p f g
cong-ex σ (⊗r∧l₁ {Y = Y} p {f = f} {g}) = ex-⊗r-∧l₁ {Y = Y} done σ p f g
cong-ex σ (⊗r∧l₂ {X = X} p {f = f} {g}) = ex-⊗r-∧l₂ {X = X} done σ p f g
cong-ex σ (⊗r∨l p {f = f} {f'} {g}) = ex-⊗r-∨l done σ p f f' g
cong-ex σ (∧rpass p {f = f} {g}) = ex-pass-∧r [] σ p f g
cong-ex σ (∨r₁pass {B = B} p {f = f}) = ex-pass-∨r₁ [] {B = B} σ p f
cong-ex σ (∨r₂pass {A = A} p {f = f}) = ex-pass-∨r₂ [] {A = A} σ p f
cong-ex σ ∧rIl = ∧rIl
cong-ex σ ∧r⊗l = ∧r⊗l
cong-ex σ ∧r∧l₁ = ∧r∧l₁
cong-ex σ ∧r∧l₂ = ∧r∧l₂
cong-ex σ ∧r∨l = ∧r∨l
cong-ex σ ∨r₁Il = ∨r₁Il
cong-ex σ ∨r₁⊗l = ∨r₁⊗l
cong-ex σ ∨r₁∧l₁ = ∨r₁∧l₁
cong-ex σ ∨r₁∧l₂ = ∨r₁∧l₂
cong-ex σ ∨r₁∨l = ∨r₁∨l
cong-ex σ ∨r₂Il = ∨r₂Il
cong-ex σ ∨r₂⊗l = ∨r₂⊗l
cong-ex σ ∨r₂∧l₁ = ∨r₂∧l₁
cong-ex σ ∨r₂∧l₂ = ∨r₂∧l₂
cong-ex σ ∨r₂∨l = ∨r₂∨l

cong-ex-pass Λ sw here eq = pass (pickᴿ++ Λ (there here)) eq
cong-ex-pass Λ sw (there here) eq = pass (pickᴿ++ Λ here) eq
cong-ex-pass Λ sw (there (there p)) eq = pass (pickᴿ++ Λ (there (there p))) (cong-ex (swapᴿ++ Λ sw) eq)
cong-ex-pass Λ (keep σ) here eq = pass (pickᴿ++ Λ here) (cong-ex (swapᴿ++ Λ σ) eq)
cong-ex-pass Λ (keep {A = B} σ) (there p) eq = cong-ex-pass (B ∷ Λ) σ p eq

cong-ex-⊗r {Λ = Λ} r sw (left (left p)) eq eq' =
  ⊗r (partᴿ++ r (left (left p))) (cong-ex (swapᴿ++ Λ sw) eq) eq'
cong-ex-⊗r {Ω = Ω} r sw (right (right p)) eq eq' =
  ⊗r (partᴿ++ r (right (right p))) eq (cong-ex (swapᴿ++ Ω sw) eq')
cong-ex-⊗r r sw (left (right p)) eq eq' = ⊗r (partᴿ++ r (right (left p))) eq eq'
cong-ex-⊗r r sw (right (left p)) eq eq' = ⊗r (partᴿ++ r (left (right p))) eq eq'
cong-ex-⊗r r (keep σ) (left p) eq eq' = cong-ex-⊗r (left r) σ p eq eq'
cong-ex-⊗r r (keep σ) (right p) eq eq' = cong-ex-⊗r (right r) σ p eq eq'

-- A prefix exchange leaves a suffix selection unchanged.
ex-prefix-pass : ∀ {Λ Λ' X Γ Δ C} (ρ : Swap Λ Λ') (p : Pick X Γ Δ)
  (f : just X ∣ Λ ᴿ++ Δ ⊢ C)
  → ex-pass [] (swap-prefixᴿ++ ρ Γ) (pickᴿ++ Λ p) f
    ≡ pass (pickᴿ++ Λ' p) (ex (swap-prefixᴿ++ ρ Δ) f)
ex-prefix-pass (sw {Γ = Λ}) p f = ex-passᴿ++ Λ sw (there (there p)) f
ex-prefix-pass (keep ρ) p f = ex-prefix-pass ρ (there p) f

-- Split the accumulated prefix around the exchanged pair. The four
-- cases record its allocation directly, using only ordinary partitions.
⊗r-prefix-ex-ll : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ X ∷ Y ∷ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ Ω₀) ᴿ++ Δ ⊢ B)
  → ex-⊗r done (swap-prefixᴿ++ (swap-pre Ξ sw) Θ) (partᴿ++ (part++ t (left (left r))) p) f g
    ≡ ⊗r (partᴿ++ (part++ t (left (left r))) p) (ex (swap-prefixᴿ++ (swap-pre Λ sw) Γ) f) g
⊗r-prefix-ex-ll done r p f g = ex-⊗rᴿ++ r sw (left (left p)) f g
⊗r-prefix-ex-ll (left t) r p f g = ⊗r-prefix-ex-ll t r (left p) f g
⊗r-prefix-ex-ll (right t) r p f g = ⊗r-prefix-ex-ll t r (right p) f g

⊗r-prefix-ex-rr : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ X ∷ Y ∷ Ω₀) ᴿ++ Δ ⊢ B)
  → ex-⊗r done (swap-prefixᴿ++ (swap-pre Ξ sw) Θ) (partᴿ++ (part++ t (right (right r))) p) f g
    ≡ ⊗r (partᴿ++ (part++ t (right (right r))) p) f (ex (swap-prefixᴿ++ (swap-pre Ω sw) Δ) g)
⊗r-prefix-ex-rr done r p f g = ex-⊗rᴿ++ r sw (right (right p)) f g
⊗r-prefix-ex-rr (left t) r p f g = ⊗r-prefix-ex-rr t r (left p) f g
⊗r-prefix-ex-rr (right t) r p f g = ⊗r-prefix-ex-rr t r (right p) f g

⊗r-prefix-ex-lr : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ X ∷ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ Y ∷ Ω₀) ᴿ++ Δ ⊢ B)
  → ex-⊗r done (swap-prefixᴿ++ (swap-pre Ξ sw) Θ) (partᴿ++ (part++ t (left (right r))) p) f g
    ≡ ⊗r (partᴿ++ (part++ t (right (left r))) p) f g
⊗r-prefix-ex-lr done r p f g = ex-⊗rᴿ++ r sw (right (left p)) f g
⊗r-prefix-ex-lr (left t) r p f g = ⊗r-prefix-ex-lr t r (left p) f g
⊗r-prefix-ex-lr (right t) r p f g = ⊗r-prefix-ex-lr t r (right p) f g

⊗r-prefix-ex-rl : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ Y ∷ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ X ∷ Ω₀) ᴿ++ Δ ⊢ B)
  → ex-⊗r done (swap-prefixᴿ++ (swap-pre Ξ sw) Θ) (partᴿ++ (part++ t (right (left r))) p) f g
    ≡ ⊗r (partᴿ++ (part++ t (left (right r))) p) f g
⊗r-prefix-ex-rl done r p f g = ex-⊗rᴿ++ r sw (left (right p)) f g
⊗r-prefix-ex-rl (left t) r p f g = ⊗r-prefix-ex-rl t r (left p) f g
⊗r-prefix-ex-rl (right t) r p f g = ⊗r-prefix-ex-rl t r (right p) f g



exex : ∀ {S Γ Δ Ξ Θ C}
  {σ₁ : Swap Γ Δ} {σ₂ : Swap Δ Θ} {τ₁ : Swap Γ Ξ} {τ₂ : Swap Ξ Θ}
  → Disjoint σ₁ σ₂ τ₁ τ₂ → (f : S ∣ Γ ⊢ C)
  → ex σ₂ (ex σ₁ f) ≡ ex τ₂ (ex τ₁ f)

exex-pass : ∀ Λ {X Γ Δ Ξ Θ Ω C}
  {σ₁ : Swap Γ Δ} {σ₂ : Swap Δ Θ} {τ₁ : Swap Γ Ξ} {τ₂ : Swap Ξ Θ}
  (d : Disjoint σ₁ σ₂ τ₁ τ₂) (p : Pick X Γ Ω) (f : just X ∣ Λ ᴿ++ Ω ⊢ C)
  → ex (swapᴿ++ Λ σ₂) (ex-pass Λ σ₁ p f)
    ≡ ex (swapᴿ++ Λ τ₂) (ex-pass Λ τ₁ p f)

ex-pass-prefix-ex : ∀ {Λ Λ' Γ Δ Ω X C} (ρ : Swap Λ Λ') (σ : Swap Γ Δ)
  (p : Pick X Γ Ω) (f : just X ∣ Λ ᴿ++ Ω ⊢ C)
  → ex (swap-prefixᴿ++ ρ Δ) (ex-pass Λ σ p f)
    ≡ ex-pass Λ' σ p (ex (swap-prefixᴿ++ ρ Ω) f)

exex-⊗r : ∀ {S Λ Ω Π Γ Δ Ξ Θ Γ₁ Γ₂ A B} (r : Part Λ Ω Π)
  {σ₁ : Swap Γ Δ} {σ₂ : Swap Δ Θ} {τ₁ : Swap Γ Ξ} {τ₂ : Swap Ξ Θ}
  (d : Disjoint σ₁ σ₂ τ₁ τ₂) (p : Part Γ₁ Γ₂ Γ)
  (f : S ∣ Λ ᴿ++ Γ₁ ⊢ A) (g : - ∣ Ω ᴿ++ Γ₂ ⊢ B)
  → ex (swapᴿ++ Π σ₂) (ex-⊗r r σ₁ p f g)
    ≡ ex (swapᴿ++ Π τ₂) (ex-⊗r r τ₁ p f g)

ex-⊗r-prefix-ex-ll : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ Θ' A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ X ∷ Y ∷ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ Ω₀) ᴿ++ Δ ⊢ B)
  → ex (swap-prefixᴿ++ (swap-pre Ξ sw) Θ') (ex-⊗r (part++ t (left (left r))) σ p f g)
    ≡ ex-⊗r (part++ t (left (left r))) σ p (ex (swap-prefixᴿ++ (swap-pre Λ sw) Γ) f) g

ex-⊗r-prefix-ex-rr : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ Θ' A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ X ∷ Y ∷ Ω₀) ᴿ++ Δ ⊢ B)
  → ex (swap-prefixᴿ++ (swap-pre Ξ sw) Θ') (ex-⊗r (part++ t (right (right r))) σ p f g)
    ≡ ex-⊗r (part++ t (right (right r))) σ p f (ex (swap-prefixᴿ++ (swap-pre Ω sw) Δ) g)

ex-⊗r-prefix-ex-lr : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ Θ' A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ X ∷ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ Y ∷ Ω₀) ᴿ++ Δ ⊢ B)
  → ex (swap-prefixᴿ++ (swap-pre Ξ sw) Θ') (ex-⊗r (part++ t (left (right r))) σ p f g)
    ≡ ex-⊗r (part++ t (right (left r))) σ p f g

ex-⊗r-prefix-ex-rl : ∀ {S Λ Ω Ξ Λ₀ Ω₀ Ξ₀ Γ Δ Θ Θ' A B X Y}
  (t : Part Λ Ω Ξ) (r : Part Λ₀ Ω₀ Ξ₀) (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ++ Y ∷ Λ₀) ᴿ++ Γ ⊢ A) (g : - ∣ (Ω ++ X ∷ Ω₀) ᴿ++ Δ ⊢ B)
  → ex (swap-prefixᴿ++ (swap-pre Ξ sw) Θ') (ex-⊗r (part++ t (right (left r))) σ p f g)
    ≡ ex-⊗r (part++ t (left (right r))) σ p f g

exex d (Il f) = cong Il (exex d f)
exex d (⊗l f) = cong ⊗l (exex (keep-disjoint d) f)
exex d (∧l₁ f) = cong ∧l₁ (exex d f)
exex d (∧l₂ f) = cong ∧l₂ (exex d f)
exex d (∨r₁ f) = cong ∨r₁ (exex d f)
exex d (∨r₂ f) = cong ∨r₂ (exex d f)
exex d (∧r f g) = cong₂ ∧r (exex d f) (exex d g)
exex d (∨l f g) = cong₂ ∨l (exex d f) (exex d g)
exex d (pass p f) = exex-pass [] d p f
exex d (⊗r p f g) = exex-⊗r done d p f g

ex-pass-prefix-ex ρ sw here f = ex-prefix-pass ρ (there here) f
ex-pass-prefix-ex ρ sw (there here) f = ex-prefix-pass ρ here f
ex-pass-prefix-ex {Λ = Λ} {Λ'} ρ sw (there (there p)) f = trans
  (ex-prefix-pass ρ (there (there p)) (ex (swapᴿ++ Λ sw) f))
  (cong (pass (pickᴿ++ Λ' (there (there p)))) (sym (exex (disjoint-prefixᴿ++ ρ sw) f)))
ex-pass-prefix-ex {Λ = Λ} {Λ'} ρ (keep σ) here f = trans
  (ex-prefix-pass ρ here (ex (swapᴿ++ Λ σ) f))
  (cong (pass (pickᴿ++ Λ' here)) (sym (exex (disjoint-prefixᴿ++ ρ σ) f)))
ex-pass-prefix-ex ρ (keep σ) (there p) f = ex-pass-prefix-ex (keep ρ) σ p f

exex-pass Λ (disjoint σ) here f = trans
  (ex-passᴿ++ Λ (keep (keep σ)) (there here) f)
  (sym (ex-passᴿ++ Λ sw here (ex (swapᴿ++ Λ (keep σ)) f)))
exex-pass Λ (disjoint σ) (there here) f = trans
  (ex-passᴿ++ Λ (keep (keep σ)) here f)
  (sym (ex-passᴿ++ Λ sw (there here) (ex (swapᴿ++ Λ (keep σ)) f)))
exex-pass Λ (disjoint σ) (there (there p)) f = trans
  (ex-passᴿ++ Λ (keep (keep σ)) (there (there p)) (ex (swapᴿ++ Λ sw) f))
  (sym (ex-pass-prefix-ex sw σ p f))
exex-pass Λ (keep-disjoint {σ₁ = σ₁} {σ₂} {τ₁} {τ₂} d) here f = trans
  (ex-passᴿ++ Λ (keep σ₂) here (ex (swapᴿ++ Λ σ₁) f))
  (trans (cong (pass (pickᴿ++ Λ here)) (exex (disjointᴿ++ Λ d) f))
    (sym (ex-passᴿ++ Λ (keep τ₂) here (ex (swapᴿ++ Λ τ₁) f))))
exex-pass Λ (keep-disjoint {A = A} d) (there p) f = exex-pass (A ∷ Λ) d p f

ex-⊗r-prefix-ex-ll {Λ = Λ} {Λ₀ = Λ₀} {X = X} {Y = Y} t r sw (left (left p)) f g = trans
  (⊗r-prefix-ex-ll t r (left (left p)) (ex (swapᴿ++ (Λ ++ X ∷ Y ∷ Λ₀) sw) f) g)
  (cong (λ f' → ⊗r (partᴿ++ (part++ t (left {x = Y} (left {x = X} r))) (left (left p))) f' g)
    (sym (exex (disjoint-prefixᴿ++ (swap-pre Λ (sw {A = X} {B = Y} {Γ = Λ₀})) sw) f)))
ex-⊗r-prefix-ex-ll {Ω = Ω} {Ω₀ = Ω₀} t r sw (right (right p)) f g =
  ⊗r-prefix-ex-ll t r (right (right p)) f (ex (swapᴿ++ (Ω ++ Ω₀) sw) g)
ex-⊗r-prefix-ex-ll t r sw (left (right p)) f g = ⊗r-prefix-ex-ll t r (right (left p)) f g
ex-⊗r-prefix-ex-ll t r sw (right (left p)) f g = ⊗r-prefix-ex-ll t r (left (right p)) f g
ex-⊗r-prefix-ex-ll t r (keep σ) (left p) f g = ex-⊗r-prefix-ex-ll (left t) r σ p f g
ex-⊗r-prefix-ex-ll t r (keep σ) (right p) f g = ex-⊗r-prefix-ex-ll (right t) r σ p f g

ex-⊗r-prefix-ex-rr {Λ = Λ} {Λ₀ = Λ₀} t r sw (left (left p)) f g =
  ⊗r-prefix-ex-rr t r (left (left p)) (ex (swapᴿ++ (Λ ++ Λ₀) sw) f) g
ex-⊗r-prefix-ex-rr {Ω = Ω} {Ω₀ = Ω₀} {X = X} {Y = Y} t r sw (right (right p)) f g = trans
  (⊗r-prefix-ex-rr t r (right (right p)) f (ex (swapᴿ++ (Ω ++ X ∷ Y ∷ Ω₀) sw) g))
  (cong (λ g' → ⊗r (partᴿ++ (part++ t (right {x = Y} (right {x = X} r))) (right (right p))) f g')
    (sym (exex (disjoint-prefixᴿ++ (swap-pre Ω (sw {A = X} {B = Y} {Γ = Ω₀})) sw) g)))
ex-⊗r-prefix-ex-rr t r sw (left (right p)) f g = ⊗r-prefix-ex-rr t r (right (left p)) f g
ex-⊗r-prefix-ex-rr t r sw (right (left p)) f g = ⊗r-prefix-ex-rr t r (left (right p)) f g
ex-⊗r-prefix-ex-rr t r (keep σ) (left p) f g = ex-⊗r-prefix-ex-rr (left t) r σ p f g
ex-⊗r-prefix-ex-rr t r (keep σ) (right p) f g = ex-⊗r-prefix-ex-rr (right t) r σ p f g

ex-⊗r-prefix-ex-lr {Λ = Λ} {Λ₀ = Λ₀} {X = X} t r sw (left (left p)) f g =
  ⊗r-prefix-ex-lr t r (left (left p)) (ex (swapᴿ++ (Λ ++ X ∷ Λ₀) sw) f) g
ex-⊗r-prefix-ex-lr {Ω = Ω} {Ω₀ = Ω₀} {Y = Y} t r sw (right (right p)) f g =
  ⊗r-prefix-ex-lr t r (right (right p)) f (ex (swapᴿ++ (Ω ++ Y ∷ Ω₀) sw) g)
ex-⊗r-prefix-ex-lr t r sw (left (right p)) f g = ⊗r-prefix-ex-lr t r (right (left p)) f g
ex-⊗r-prefix-ex-lr t r sw (right (left p)) f g = ⊗r-prefix-ex-lr t r (left (right p)) f g
ex-⊗r-prefix-ex-lr t r (keep σ) (left p) f g = ex-⊗r-prefix-ex-lr (left t) r σ p f g
ex-⊗r-prefix-ex-lr t r (keep σ) (right p) f g = ex-⊗r-prefix-ex-lr (right t) r σ p f g

ex-⊗r-prefix-ex-rl {Λ = Λ} {Λ₀ = Λ₀} {Y = Y} t r sw (left (left p)) f g =
  ⊗r-prefix-ex-rl t r (left (left p)) (ex (swapᴿ++ (Λ ++ Y ∷ Λ₀) sw) f) g
ex-⊗r-prefix-ex-rl {Ω = Ω} {Ω₀ = Ω₀} {X = X} t r sw (right (right p)) f g =
  ⊗r-prefix-ex-rl t r (right (right p)) f (ex (swapᴿ++ (Ω ++ X ∷ Ω₀) sw) g)
ex-⊗r-prefix-ex-rl t r sw (left (right p)) f g = ⊗r-prefix-ex-rl t r (right (left p)) f g
ex-⊗r-prefix-ex-rl t r sw (right (left p)) f g = ⊗r-prefix-ex-rl t r (left (right p)) f g
ex-⊗r-prefix-ex-rl t r (keep σ) (left p) f g = ex-⊗r-prefix-ex-rl (left t) r σ p f g
ex-⊗r-prefix-ex-rl t r (keep σ) (right p) f g = ex-⊗r-prefix-ex-rl (right t) r σ p f g

exex-⊗r {Λ = Λ} r (disjoint σ) (left (left p)) f g = trans
  (ex-⊗rᴿ++ r (keep (keep σ)) (left (left p)) (ex (swapᴿ++ Λ sw) f) g)
  (sym (ex-⊗r-prefix-ex-ll done r σ p f g))
exex-⊗r {Ω = Ω} r (disjoint σ) (right (right p)) f g = trans
  (ex-⊗rᴿ++ r (keep (keep σ)) (right (right p)) f (ex (swapᴿ++ Ω sw) g))
  (sym (ex-⊗r-prefix-ex-rr done r σ p f g))
exex-⊗r r (disjoint σ) (left (right p)) f g = trans
  (ex-⊗rᴿ++ r (keep (keep σ)) (right (left p)) f g)
  (sym (ex-⊗r-prefix-ex-rl done r σ p f g))
exex-⊗r r (disjoint σ) (right (left p)) f g = trans
  (ex-⊗rᴿ++ r (keep (keep σ)) (left (right p)) f g)
  (sym (ex-⊗r-prefix-ex-lr done r σ p f g))
exex-⊗r r (keep-disjoint d) (left p) f g = exex-⊗r (left r) d p f g
exex-⊗r r (keep-disjoint d) (right p) f g = exex-⊗r (right r) d p f g

-- Braid commutation follows the derivation and the direct exchange
-- helpers simultaneously. All derivation arguments are explicit.
ex-braid : ∀ {S Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ C}
  {σ₁ : Swap Γ Δ₁} {σ₂ : Swap Δ₁ Δ₂} {σ₃ : Swap Δ₂ Θ}
  {τ₁ : Swap Γ Ξ₁} {τ₂ : Swap Ξ₁ Ξ₂} {τ₃ : Swap Ξ₂ Θ}
  → Braid σ₁ σ₂ σ₃ τ₁ τ₂ τ₃ → (f : S ∣ Γ ⊢ C)
  → ex σ₃ (ex σ₂ (ex σ₁ f)) ≡ ex τ₃ (ex τ₂ (ex τ₁ f))

ex-braid-pass : ∀ Λ {X Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ Ω C}
  {σ₁ : Swap Γ Δ₁} {σ₂ : Swap Δ₁ Δ₂} {σ₃ : Swap Δ₂ Θ}
  {τ₁ : Swap Γ Ξ₁} {τ₂ : Swap Ξ₁ Ξ₂} {τ₃ : Swap Ξ₂ Θ}
  (b : Braid σ₁ σ₂ σ₃ τ₁ τ₂ τ₃) (p : Pick X Γ Ω) (f : just X ∣ Λ ᴿ++ Ω ⊢ C)
  → ex (swapᴿ++ Λ σ₃) (ex (swapᴿ++ Λ σ₂) (ex-pass Λ σ₁ p f))
    ≡ ex (swapᴿ++ Λ τ₃) (ex (swapᴿ++ Λ τ₂) (ex-pass Λ τ₁ p f))

ex-braid-⊗r : ∀ {S Λ Ω Π Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ Γ₁ Γ₂ A B} (r : Part Λ Ω Π)
  {σ₁ : Swap Γ Δ₁} {σ₂ : Swap Δ₁ Δ₂} {σ₃ : Swap Δ₂ Θ}
  {τ₁ : Swap Γ Ξ₁} {τ₂ : Swap Ξ₁ Ξ₂} {τ₃ : Swap Ξ₂ Θ}
  (b : Braid σ₁ σ₂ σ₃ τ₁ τ₂ τ₃) (p : Part Γ₁ Γ₂ Γ)
  (f : S ∣ Λ ᴿ++ Γ₁ ⊢ A) (g : - ∣ Ω ᴿ++ Γ₂ ⊢ B)
  → ex (swapᴿ++ Π σ₃) (ex (swapᴿ++ Π σ₂) (ex-⊗r r σ₁ p f g))
    ≡ ex (swapᴿ++ Π τ₃) (ex (swapᴿ++ Π τ₂) (ex-⊗r r τ₁ p f g))

ex-braid b (Il f) = cong Il (ex-braid b f)
ex-braid b (⊗l f) = cong ⊗l (ex-braid (keep-braid b) f)
ex-braid b (∧l₁ f) = cong ∧l₁ (ex-braid b f)
ex-braid b (∧l₂ f) = cong ∧l₂ (ex-braid b f)
ex-braid b (∨r₁ f) = cong ∨r₁ (ex-braid b f)
ex-braid b (∨r₂ f) = cong ∨r₂ (ex-braid b f)
ex-braid b (∧r f g) = cong₂ ∧r (ex-braid b f) (ex-braid b g)
ex-braid b (∨l f g) = cong₂ ∨l (ex-braid b f) (ex-braid b g)
ex-braid b (pass p f) = ex-braid-pass [] b p f
ex-braid b (⊗r p f g) = ex-braid-⊗r done b p f g

ex-braid-pass Λ braid here f = trans
  (trans
    (cong (ex (swapᴿ++ Λ sw)) (ex-passᴿ++ Λ (keep sw) (there here) f))
    (ex-passᴿ++ Λ sw (there (there here)) f))
  (sym (trans
    (cong (ex (swapᴿ++ Λ (keep sw))) (ex-passᴿ++ Λ sw here (ex (swapᴿ++ Λ sw) f)))
    (ex-passᴿ++ Λ (keep sw) (there here) (ex (swapᴿ++ Λ sw) f))))

ex-braid-pass Λ braid (there here) f = trans
  (trans
    (cong (ex (swapᴿ++ Λ sw)) (ex-passᴿ++ Λ (keep sw) here f))
    (ex-passᴿ++ Λ sw here (ex (swapᴿ++ Λ sw) f)))
  (sym (trans
    (cong (ex (swapᴿ++ Λ (keep sw))) (ex-passᴿ++ Λ sw (there (there here)) f))
    (ex-passᴿ++ Λ (keep sw) (there (there here)) (ex (swapᴿ++ Λ sw) f))))

ex-braid-pass Λ braid (there (there here)) f = trans
  (trans
    (cong (ex (swapᴿ++ Λ sw)) (ex-passᴿ++ Λ (keep sw) (there (there here)) (ex (swapᴿ++ Λ sw) f)))
    (ex-passᴿ++ Λ sw (there here) (ex (swapᴿ++ Λ sw) f)))
  (sym (trans
    (cong (ex (swapᴿ++ Λ (keep sw))) (ex-passᴿ++ Λ sw (there here) f))
    (ex-passᴿ++ Λ (keep sw) here f)))

ex-braid-pass Λ braid (there (there (there p))) f = trans
  (trans
    (cong (ex (swapᴿ++ Λ sw)) (ex-passᴿ++ Λ (keep sw) (there (there (there p))) (ex (swapᴿ++ Λ sw) f)))
    (ex-passᴿ++ Λ sw (there (there (there p))) (ex (swapᴿ++ Λ (keep sw)) (ex (swapᴿ++ Λ sw) f))))
  (trans (cong (pass (pickᴿ++ Λ (there (there (there p))))) (ex-braid (braidᴿ++ Λ braid) f))
    (sym (trans
    (cong (ex (swapᴿ++ Λ (keep sw))) (ex-passᴿ++ Λ sw (there (there (there p))) (ex (swapᴿ++ Λ (keep sw)) f)))
    (ex-passᴿ++ Λ (keep sw) (there (there (there p))) (ex (swapᴿ++ Λ sw) (ex (swapᴿ++ Λ (keep sw)) f))))))

ex-braid-pass Λ (keep-braid {σ₁ = σ₁} {σ₂} {σ₃} {τ₁} {τ₂} {τ₃} b) here f = trans
  (trans
    (cong (ex (swapᴿ++ Λ (keep σ₃))) (ex-passᴿ++ Λ (keep σ₂) here (ex (swapᴿ++ Λ σ₁) f)))
    (ex-passᴿ++ Λ (keep σ₃) here (ex (swapᴿ++ Λ σ₂) (ex (swapᴿ++ Λ σ₁) f))))
  (trans (cong (pass (pickᴿ++ Λ here)) (ex-braid (braidᴿ++ Λ b) f))
    (sym (trans
      (cong (ex (swapᴿ++ Λ (keep τ₃))) (ex-passᴿ++ Λ (keep τ₂) here (ex (swapᴿ++ Λ τ₁) f)))
      (ex-passᴿ++ Λ (keep τ₃) here (ex (swapᴿ++ Λ τ₂) (ex (swapᴿ++ Λ τ₁) f))))))
ex-braid-pass Λ (keep-braid {A = A} b) (there p) f = ex-braid-pass (A ∷ Λ) b p f

ex-braid-⊗r {Λ = Λ} {Π = Π} r braid (left (left (left p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (left (left (left p))) (ex (swapᴿ++ Λ sw) f) g))
    (ex-⊗rᴿ++ r sw (left (left (left p))) (ex (swapᴿ++ Λ (keep sw)) (ex (swapᴿ++ Λ sw) f)) g))
  (trans (cong (λ f' → ⊗r (partᴿ++ r (left (left (left p)))) f' g) (ex-braid (braidᴿ++ Λ braid) f))
    (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (left (left (left p))) (ex (swapᴿ++ Λ (keep sw)) f) g))
    (ex-⊗rᴿ++ r (keep sw) (left (left (left p))) (ex (swapᴿ++ Λ sw) (ex (swapᴿ++ Λ (keep sw)) f)) g))))

ex-braid-⊗r {Λ = Λ} {Π = Π} r braid (left (left (right p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (left (left (right p))) (ex (swapᴿ++ Λ sw) f) g))
    (ex-⊗rᴿ++ r sw (left (right (left p))) (ex (swapᴿ++ Λ sw) f) g))
  (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (left (right (left p))) f g))
    (ex-⊗rᴿ++ r (keep sw) (right (left (left p))) f g)))

ex-braid-⊗r {Λ = Λ} {Π = Π} r braid (left (right (left p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (right (left (left p))) f g))
    (ex-⊗rᴿ++ r sw (right (left (left p))) (ex (swapᴿ++ Λ sw) f) g))
  (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (left (left (right p))) f g))
    (ex-⊗rᴿ++ r (keep sw) (left (left (right p))) (ex (swapᴿ++ Λ sw) f) g)))

ex-braid-⊗r {Ω = Ω} {Π = Π} r braid (left (right (right p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (right (left (right p))) f g))
    (ex-⊗rᴿ++ r sw (right (right (left p))) f g))
  (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (left (right (right p))) f (ex (swapᴿ++ Ω sw) g)))
    (ex-⊗rᴿ++ r (keep sw) (right (left (right p))) f (ex (swapᴿ++ Ω sw) g))))

ex-braid-⊗r {Λ = Λ} {Π = Π} r braid (right (left (left p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (left (right (left p))) f g))
    (ex-⊗rᴿ++ r sw (left (left (right p))) f g))
  (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (right (left (left p))) (ex (swapᴿ++ Λ sw) f) g))
    (ex-⊗rᴿ++ r (keep sw) (left (right (left p))) (ex (swapᴿ++ Λ sw) f) g)))

ex-braid-⊗r {Ω = Ω} {Π = Π} r braid (right (left (right p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (left (right (right p))) f g))
    (ex-⊗rᴿ++ r sw (left (right (right p))) f (ex (swapᴿ++ Ω sw) g)))
  (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (right (right (left p))) f g))
    (ex-⊗rᴿ++ r (keep sw) (right (right (left p))) f (ex (swapᴿ++ Ω sw) g))))

ex-braid-⊗r {Ω = Ω} {Π = Π} r braid (right (right (left p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (right (right (left p))) f (ex (swapᴿ++ Ω sw) g)))
    (ex-⊗rᴿ++ r sw (right (left (right p))) f (ex (swapᴿ++ Ω sw) g)))
  (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (right (left (right p))) f g))
    (ex-⊗rᴿ++ r (keep sw) (left (right (right p))) f g)))

ex-braid-⊗r {Ω = Ω} {Π = Π} r braid (right (right (right p))) f g = trans
  (trans
    (cong (ex (swapᴿ++ Π sw)) (ex-⊗rᴿ++ r (keep sw) (right (right (right p))) f (ex (swapᴿ++ Ω sw) g)))
    (ex-⊗rᴿ++ r sw (right (right (right p))) f (ex (swapᴿ++ Ω (keep sw)) (ex (swapᴿ++ Ω sw) g))))
  (trans (cong (⊗r (partᴿ++ r (right (right (right p)))) f) (ex-braid (braidᴿ++ Ω braid) g))
    (sym (trans
    (cong (ex (swapᴿ++ Π (keep sw))) (ex-⊗rᴿ++ r sw (right (right (right p))) f (ex (swapᴿ++ Ω (keep sw)) g)))
    (ex-⊗rᴿ++ r (keep sw) (right (right (right p))) f (ex (swapᴿ++ Ω sw) (ex (swapᴿ++ Ω (keep sw)) g))))))

ex-braid-⊗r r (keep-braid b) (left p) f g = ex-braid-⊗r (left r) b p f g
ex-braid-⊗r r (keep-braid b) (right p) f g = ex-braid-⊗r (right r) b p f g

-- Moving the first right-premise occurrence across the remaining left
-- context changes only its position in the partition.
ex-pickR-⊗r : ∀ {S Δ X Λ Ω Ξ A B} (Γ : Cxt) (r : Part Λ Ω Ξ)
  (f : S ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ (X ∷ Δ) ⊢ B)
  → ex-pickR (pick-prefix Γ) Ξ (⊗r (partᴿ++ r (part Γ (X ∷ Δ))) f g)
    ≡ ⊗r (partᴿ++ (right r) (part Γ Δ)) f g
ex-pickR-⊗r [] r f g = refl
ex-pickR-⊗r {Δ = Δ} {Ξ = Ξ} (Y ∷ Γ) r f g = trans
  (cong (ex (swapᴿ++ Ξ sw)) (ex-pickR-⊗r Γ (left r) f g))
  (ex-⊗rᴿ++ r sw (left (right (part Γ Δ))) f g)

-- Interleaving the context of a tensor introduction reconstructs its
-- partition, including any prefix already processed.
ex-part-⊗r : ∀ {S Γ Δ Θ Λ Ω Ξ A B} (p : Part Γ Δ Θ) (r : Part Λ Ω Ξ)
  (f : S ∣ Λ ᴿ++ Γ ⊢ A) (g : - ∣ Ω ᴿ++ Δ ⊢ B)
  → ex-part p Ξ (⊗r (partᴿ++ r (part Γ Δ)) f g)
    ≡ ⊗r (partᴿ++ r p) f g
ex-part-⊗r done r f g = refl
ex-part-⊗r (left p) r f g = ex-part-⊗r p (left r) f g
ex-part-⊗r {Ξ = Ξ} (right {x = X} {xs = Γ} p) r f g = trans
  (cong (ex-part p (X ∷ Ξ)) (ex-pickR-⊗r Γ r f g))
  (ex-part-⊗r p (right r) f g)

-- Moving the passed occurrence into its selected position changes the
-- selection witness and leaves the premise derivation fixed.
ex-pickL-pass : ∀ {X Γ Δ C} (q : Pick X Γ Δ) (Λ : Cxt)
  (f : just X ∣ Λ ᴿ++ Δ ⊢ C)
  → ex-pickL q Λ (pass (pickᴿ++ Λ here) f)
    ≡ pass (pickᴿ++ Λ q) f
ex-pickL-pass here Λ f = refl
ex-pickL-pass (there {b = Y} q) Λ f = trans
  (cong (ex-pickL q (Y ∷ Λ)) (ex-passᴿ++ Λ sw here f))
  (ex-pickL-pass q (Y ∷ Λ) f)
