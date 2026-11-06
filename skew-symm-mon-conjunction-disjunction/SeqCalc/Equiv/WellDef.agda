{-# OPTIONS --safe #-}

module SeqCalc.Equiv.WellDef (At : Set) where

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Utilities
open import Formulae At
import SeqCalc.ExplEq At as E
import SeqCalc.ImplEq At as I
open import SeqCalc.Equiv.Maps At public using (_∣_⊢I_; _∣_⊢E_; toI; toE)

-- Every generating equation of the explicit calculus is preserved.
toI-≗ : ∀ {S Γ C} {f g : S ∣ Γ ⊢E C}
  → f E.≗ g → toI f I.≗ toI g
toI-≗ E.refl = I.refl
toI-≗ (E.~ eq) = I.~ toI-≗ eq
toI-≗ (eq E.∙ eq') = toI-≗ eq I.∙ toI-≗ eq'
toI-≗ (E.pass refl eq) = I.pass here (toI-≗ eq)
toI-≗ (E.Il eq) = I.Il (toI-≗ eq)
toI-≗ (E.⊗l eq) = I.⊗l (toI-≗ eq)
toI-≗ (E.⊗r {Γ = Γ} {Δ} refl eq eq') = I.⊗r (part Γ Δ) (toI-≗ eq) (toI-≗ eq')
toI-≗ (E.∧r eq eq') = I.∧r (toI-≗ eq) (toI-≗ eq')
toI-≗ (E.∧l₁ eq) = I.∧l₁ (toI-≗ eq)
toI-≗ (E.∧l₂ eq) = I.∧l₂ (toI-≗ eq)
toI-≗ (E.∨r₁ eq) = I.∨r₁ (toI-≗ eq)
toI-≗ (E.∨r₂ eq) = I.∨r₂ (toI-≗ eq)
toI-≗ (E.∨l eq eq') = I.∨l (toI-≗ eq) (toI-≗ eq')
toI-≗ E.axI = I.axI
toI-≗ E.ax⊗ = I.ax⊗
toI-≗ E.ax∧ = I.ax∧
toI-≗ E.ax∨ = I.ax∨
toI-≗ (E.⊗rpass {Γ = Γ} {Δ} {A' = X}) = I.⊗rpass (part (X ∷ Γ) Δ) here
toI-≗ (E.⊗rIl {Γ = Γ} {Δ}) = I.⊗rIl (part Γ Δ)
toI-≗ (E.⊗r⊗l {Γ = Γ} {Δ}) = I.⊗r⊗l (part Γ Δ)
toI-≗ (E.⊗r∧l₁ {Γ = Γ} {Δ}) = I.⊗r∧l₁ (part Γ Δ)
toI-≗ (E.⊗r∧l₂ {Γ = Γ} {Δ}) = I.⊗r∧l₂ (part Γ Δ)
toI-≗ (E.⊗r∨l {Γ = Γ} {Δ}) = I.⊗r∨l (part Γ Δ)
toI-≗ E.∧rpass = I.∧rpass here
toI-≗ E.∧rIl = I.∧rIl
toI-≗ E.∧r⊗l = I.∧r⊗l
toI-≗ E.∧r∧l₁ = I.∧r∧l₁
toI-≗ E.∧r∧l₂ = I.∧r∧l₂
toI-≗ E.∧r∨l = I.∧r∨l
toI-≗ E.∨r₁pass = I.∨r₁pass here
toI-≗ E.∨r₁Il = I.∨r₁Il
toI-≗ E.∨r₁⊗l = I.∨r₁⊗l
toI-≗ E.∨r₁∧l₁ = I.∨r₁∧l₁
toI-≗ E.∨r₁∧l₂ = I.∨r₁∧l₂
toI-≗ E.∨r₁∨l = I.∨r₁∨l
toI-≗ E.∨r₂pass = I.∨r₂pass here
toI-≗ E.∨r₂Il = I.∨r₂Il
toI-≗ E.∨r₂⊗l = I.∨r₂⊗l
toI-≗ E.∨r₂∧l₁ = I.∨r₂∧l₁
toI-≗ E.∨r₂∧l₂ = I.∨r₂∧l₂
toI-≗ E.∨r₂∨l = I.∨r₂∨l
toI-≗ (E.ex-iso σ {f = f}) = I.≡to≗ (I.ex-iso σ (toI f))
toI-≗ (E.expass σ) = I.refl
toI-≗ (E.exIl σ) = I.refl
toI-≗ (E.ex⊗l σ) = I.refl
toI-≗ (E.ex∧l₁ σ) = I.refl
toI-≗ (E.ex∧l₂ σ) = I.refl
toI-≗ (E.ex∧r σ) = I.refl
toI-≗ (E.ex∨l σ) = I.refl
toI-≗ (E.ex∨r₁ σ) = I.refl
toI-≗ (E.ex∨r₂ σ) = I.refl
toI-≗ (E.ex σ eq) = I.cong-ex σ (toI-≗ eq)
toI-≗ (E.ex-braid β {f = f}) = I.≡to≗ (I.ex-braid β (toI f))
toI-≗ (E.exex δ {f = f}) = I.≡to≗ (I.exex δ (toI f))
toI-≗ (E.ex⊗r₁ σ {f = f} {g}) =
  I.≡to≗ (I.ex-⊗r₁ σ (toI f) (toI g))
toI-≗ (E.ex⊗r₂ σ {f = f} {g}) =
  I.≡to≗ (I.ex-⊗r₂ σ (toI f) (toI g))

-- Equation preservation in the other direction uses the permutation
-- compatibility lemmas in ExplEq.
toE-≗ : ∀ {S Γ C} {f g : S ∣ Γ ⊢I C}
  → f I.≗ g → toE f E.≗ toE g
toE-≗ I.refl = E.refl
toE-≗ (I.~ eq) = E.~ toE-≗ eq
toE-≗ (eq I.∙ eq') = toE-≗ eq E.∙ toE-≗ eq'
toE-≗ (I.Il eq) = E.Il (toE-≗ eq)
toE-≗ (I.⊗l eq) = E.⊗l (toE-≗ eq)
toE-≗ (I.∧r eq eq') = E.∧r (toE-≗ eq) (toE-≗ eq')
toE-≗ (I.∧l₁ eq) = E.∧l₁ (toE-≗ eq)
toE-≗ (I.∧l₂ eq) = E.∧l₂ (toE-≗ eq)
toE-≗ (I.∨r₁ eq) = E.∨r₁ (toE-≗ eq)
toE-≗ (I.∨r₂ eq) = E.∨r₂ (toE-≗ eq)
toE-≗ (I.∨l eq eq') = E.∨l (toE-≗ eq) (toE-≗ eq')
toE-≗ (I.pass p eq) = E.cong-ex-pickL p [] (E.pass refl (toE-≗ eq))
toE-≗ (I.⊗r p eq eq') = E.cong-ex-part p [] (E.⊗r refl (toE-≗ eq) (toE-≗ eq'))
toE-≗ I.axI = E.axI
toE-≗ I.ax⊗ = E.ax⊗
toE-≗ I.ax∧ = E.ax∧
toE-≗ I.ax∨ = E.ax∨
toE-≗ (I.⊗rpass p q {f = f} {g}) = E.ex-part-⊗rpass p q (toE f) (toE g)
toE-≗ (I.⊗rIl p {f = f} {g}) = E.cong-ex-part p [] E.⊗rIl E.∙
  E.ex-part-Il p [] (E.⊗r refl (toE f) (toE g))
toE-≗ (I.⊗r⊗l p {f = f} {g}) = E.cong-ex-part p [] E.⊗r⊗l E.∙
  E.ex-part-⊗l p [] (E.⊗r refl (toE f) (toE g))
toE-≗ (I.⊗r∧l₁ p {f = f} {g}) = E.cong-ex-part p [] E.⊗r∧l₁ E.∙
  E.ex-part-∧l₁ p [] (E.⊗r refl (toE f) (toE g))
toE-≗ (I.⊗r∧l₂ p {f = f} {g}) = E.cong-ex-part p [] E.⊗r∧l₂ E.∙
  E.ex-part-∧l₂ p [] (E.⊗r refl (toE f) (toE g))
toE-≗ (I.⊗r∨l p {f = f} {f'} {g}) = E.cong-ex-part p [] E.⊗r∨l E.∙
  E.ex-part-∨l p [] (E.⊗r refl (toE f) (toE g)) (E.⊗r refl (toE f') (toE g))
toE-≗ (I.∧rpass p {f = f} {g}) =
  E.ex-pickL-∧r p [] (E.pass refl (toE f)) (E.pass refl (toE g)) E.∙ E.cong-ex-pickL p [] E.∧rpass
toE-≗ (I.∨r₁pass p {f = f}) = E.ex-pickL-∨r₁ p [] (E.pass refl (toE f)) E.∙ E.cong-ex-pickL p [] E.∨r₁pass
toE-≗ (I.∨r₂pass p {f = f}) = E.ex-pickL-∨r₂ p [] (E.pass refl (toE f)) E.∙ E.cong-ex-pickL p [] E.∨r₂pass
toE-≗ I.∧rIl = E.∧rIl
toE-≗ I.∧r⊗l = E.∧r⊗l
toE-≗ I.∧r∧l₁ = E.∧r∧l₁
toE-≗ I.∧r∧l₂ = E.∧r∧l₂
toE-≗ I.∧r∨l = E.∧r∨l
toE-≗ I.∨r₁Il = E.∨r₁Il
toE-≗ I.∨r₁⊗l = E.∨r₁⊗l
toE-≗ I.∨r₁∧l₁ = E.∨r₁∧l₁
toE-≗ I.∨r₁∧l₂ = E.∨r₁∧l₂
toE-≗ I.∨r₁∨l = E.∨r₁∨l
toE-≗ I.∨r₂Il = E.∨r₂Il
toE-≗ I.∨r₂⊗l = E.∨r₂⊗l
toE-≗ I.∨r₂∧l₁ = E.∨r₂∧l₁
toE-≗ I.∨r₂∧l₂ = E.∨r₂∧l₂
toE-≗ I.∨r₂∨l = E.∨r₂∨l
