{-# OPTIONS --safe #-}

module SeqCalc.Equiv.Maps (At : Set) where

open import Data.List
open import Relation.Binary.PropositionalEquality using (refl)
open import Utilities
open import Formulae At
import SeqCalc.Expl At as E
import SeqCalc.Impl At as I

infix 15 _∣_⊢I_ _∣_⊢E_

_∣_⊢I_ = I._∣_⊢_
_∣_⊢E_ = E._∣_⊢_


-- Translate explicit exchange into the admissible exchange operation.
toI : ∀ {S Γ C} → S ∣ Γ ⊢E C → S ∣ Γ ⊢I C
toI E.ax = I.ax
toI E.Ir = I.Ir
toI (E.pass refl f) = I.pass here (toI f)
toI (E.Il f) = I.Il (toI f)
toI (E.⊗l f) = I.⊗l (toI f)
toI (E.⊗r {Γ = Γ} {Δ} refl f g) = I.⊗r (part Γ Δ) (toI f) (toI g)
toI (E.∧r f g) = I.∧r (toI f) (toI g)
toI (E.∧l₁ f) = I.∧l₁ (toI f)
toI (E.∧l₂ f) = I.∧l₂ (toI f)
toI (E.∨r₁ f) = I.∨r₁ (toI f)
toI (E.∨r₂ f) = I.∨r₂ (toI f)
toI (E.∨l f g) = I.∨l (toI f) (toI g)
toI (E.ex σ f) = I.ex σ (toI f)

-- Realize implicit choices by explicit adjacent exchanges.
toE : ∀ {S Γ C} → S ∣ Γ ⊢I C → S ∣ Γ ⊢E C
toE I.ax = E.ax
toE I.Ir = E.Ir
toE (I.Il f) = E.Il (toE f)
toE (I.⊗l f) = E.⊗l (toE f)
toE (I.∧r f g) = E.∧r (toE f) (toE g)
toE (I.∧l₁ f) = E.∧l₁ (toE f)
toE (I.∧l₂ f) = E.∧l₂ (toE f)
toE (I.∨r₁ f) = E.∨r₁ (toE f)
toE (I.∨r₂ f) = E.∨r₂ (toE f)
toE (I.∨l f g) = E.∨l (toE f) (toE g)
toE (I.pass p f) = E.ex-pickL p [] (E.pass refl (toE f))
toE (I.⊗r p f g) = E.ex-part p [] (E.⊗r refl (toE f) (toE g))
