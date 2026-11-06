{-# OPTIONS --safe #-}

module DecEq (At : Set) where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Sum renaming ([_,_]′ to rec⊎)
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
open import SeqCalc At
open import Tags
open import FocusedSeqCalc At
open import Focus At
open import FocusWellDef At
open import Emb At
open import EmbFocus At

-- Comparing splits of the same context needs no equality test on atoms:
-- corresponding heads already agree by the given context equality.
∷-inj : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
∷-inj refl = refl , refl

split≟ : (Γ Γ' : Cxt) {Δ Δ' : Cxt} → Γ ++ Δ ≡ Γ' ++ Δ'
  → (Γ ≡ Γ' × Δ ≡ Δ') ⊎ (Γ ≡ Γ' × Δ ≡ Δ' → ⊥)
split≟ [] [] eq = inj₁ (refl , eq)
split≟ [] (A ∷ Γ') eq = inj₂ (λ { (() , _) })
split≟ (A ∷ Γ) [] eq = inj₂ (λ { (() , _) })
split≟ (A ∷ Γ) (B ∷ Γ') eq with ∷-inj eq
... | refl , eq' with split≟ Γ Γ' eq'
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ neq = inj₂ (λ { (refl , refl) → neq (refl , refl) })

-- Context equality witnesses carry no additional information.
uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

-- Decide equality of derivations of the same sequent in each focused phase.
-- Indices already fix the formulae, so no equality test on At is needed.
Dec≡ri : ∀ {S Γ C} (f g : S ∣ Γ ⊢ri C) → (f ≡ g) ⊎ (f ≡ g → ⊥)
Dec≡li : ∀ {S Γ C} (f g : S ∣ Γ ⊢li C) → (f ≡ g) ⊎ (f ≡ g → ⊥)
Dec≡f : ∀ {S Γ C} (f g : S ∣ Γ ⊢f C) → (f ≡ g) ⊎ (f ≡ g → ⊥)

Dec≡ri (∧r f f') (∧r g g') =
  rec⊎ (λ { refl → rec⊎ (λ { refl → inj₁ refl })
                        (λ neq → inj₂ (λ { refl → neq refl }))
                        (Dec≡ri f' g') })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f g)
Dec≡ri (li2ri {C = A , i} f) (li2ri {C = .A , j} g)
  rewrite isPos-unique A i j =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)

Dec≡li (⊗l f) (⊗l g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡li (Il f) (Il g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡li (∨l f f') (∨l g g') =
  rec⊎ (λ { refl → rec⊎ (λ { refl → inj₁ refl })
                        (λ neq → inj₂ (λ { refl → neq refl }))
                        (Dec≡li f' g') })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡li (f2li {S = S , i} f) (f2li {S = .S , j} g)
  rewrite isIrr-unique S i j =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡f f g)

Dec≡f ax ax = inj₁ refl
Dec≡f Ir Ir = inj₁ refl
Dec≡f (pass f) (pass g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡f (∧l₁ f) (∧l₁ g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡f (∧l₂ f) (∧l₂ g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡f (∨r₁ f ok) (∨r₁ g ok') =
  rec⊎ (λ eq → inj₁ (∨r₁eq eq))
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f g)
Dec≡f (∨r₂ f ok) (∨r₂ g ok') =
  rec⊎ (λ eq → inj₁ (∨r₂eq eq))
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f g)
-- Tensor premises can have different context splits. Compare these first,
-- identify their equality witnesses by uip, then compare both premises.
Dec≡f (⊗r {Γ = Γ} {Δ} eq f g ok) (⊗r {Γ = Γ'} {Δ'} eq' f' g' ok')
  with split≟ Γ Γ' (trans (sym eq) eq')
... | inj₂ neq = inj₂ (λ { refl → neq (refl , refl) })
... | inj₁ (refl , refl) rewrite uip eq eq' =
  rec⊎ (λ { refl → rec⊎ (λ eqg → inj₁ (⊗req eq' refl eqg))
                        (λ neq → inj₂ (λ { refl → neq refl }))
                        (Dec≡ri g g') })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f f')
Dec≡f (pass f) (⊗r eq′ f′ g′ ok′) = inj₂ (λ ())
Dec≡f (pass f) (∨r₁ f′ ok′) = inj₂ (λ ())
Dec≡f (pass f) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (⊗r eq′ f′ g′ ok′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (∨r₁ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (⊗r eq′ f′ g′ ok′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (∨r₁ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (⊗r eq f g ok) (pass f′) = inj₂ (λ ())
Dec≡f (⊗r eq f g ok) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (⊗r eq f g ok) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (pass f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (pass f′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (∨r₁ f′ ok′) = inj₂ (λ ())

-- Equal normal forms imply equivalence through their common embedding.
injective-focus : ∀ {S Γ C} {f g : S ∣ Γ ⊢ C} → focus f ≡ focus g → f ≗ g
injective-focus eq = ~ embfocus _ ∙ ≡to≗ (cong emb-ri eq) ∙ embfocus _

-- Sequent-calculus equivalence is decided by equality of normal forms.
Dec≗ : ∀ {S Γ C} (f g : S ∣ Γ ⊢ C) → (f ≗ g) ⊎ (f ≗ g → ⊥)
Dec≗ f g with Dec≡ri (focus f) (focus g)
... | inj₁ eq = inj₁ (injective-focus eq)
... | inj₂ neq = inj₂ (λ eq → neq (eqfocus eq))
