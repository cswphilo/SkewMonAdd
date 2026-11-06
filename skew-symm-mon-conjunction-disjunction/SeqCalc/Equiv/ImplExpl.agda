{-# OPTIONS --safe #-}

module SeqCalc.Equiv.ImplExpl (At : Set) where

open import Data.Maybe using (just)
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Utilities
open import Formulae At
import SeqCalc.ExplEq At as E
import SeqCalc.ImplEq At as I
open import SeqCalc.Equiv.Maps At public using (_∣_⊢I_; _∣_⊢E_; toI; toE)

-- Translation commutes with realizing any selection or partition.
-- These proofs recurse directly on the corresponding witness.
toI-ex-pickR : ∀ {S X Γ Δ C} (q : Pick X Γ Δ) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ Γ ⊢E C)
  → toI (E.ex-pickR q Λ f) ≡ I.ex-pickR q Λ (toI f)
toI-ex-pickR here Λ f = refl
toI-ex-pickR (there {b = X} q) Λ f =
  cong (I.ex (swapᴿ++ Λ sw)) (toI-ex-pickR q (X ∷ Λ) f)

toI-ex-pickL : ∀ {S X Γ Δ C} (q : Pick X Γ Δ) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ (X ∷ Δ) ⊢E C)
  → toI (E.ex-pickL q Λ f) ≡ I.ex-pickL q Λ (toI f)
toI-ex-pickL here Λ f = refl
toI-ex-pickL (there {b = X} q) Λ f =
  toI-ex-pickL q (X ∷ Λ) (E.ex (swapᴿ++ Λ sw) f)

toI-ex-part : ∀ {S Γ Δ Θ C} (p : Part Γ Δ Θ) (Λ : Cxt)
  (f : S ∣ Λ ᴿ++ (Γ ++ Δ) ⊢E C)
  → toI (E.ex-part p Λ f) ≡ I.ex-part p Λ (toI f)
toI-ex-part done Λ f = refl
toI-ex-part (left {x = X} p) Λ f = toI-ex-part p (X ∷ Λ) f
toI-ex-part (right {x = X} {xs = Γ} p) Λ f =
  trans (toI-ex-part p (X ∷ Λ) (E.ex-pickR (pick-prefix Γ) Λ f))
    (cong (I.ex-part p (X ∷ Λ)) (toI-ex-pickR (pick-prefix Γ) Λ f))

-- The implicit calculus is recovered after realizing and reinterpreting
-- its selections and partitions.
toI-toE : ∀ {S Γ C} (f : S ∣ Γ ⊢I C) → toI (toE f) I.≗ f
toI-toE I.ax = I.refl
toI-toE I.Ir = I.refl
toI-toE (I.Il f) = I.Il (toI-toE f)
toI-toE (I.⊗l f) = I.⊗l (toI-toE f)
toI-toE (I.∧r f g) = I.∧r (toI-toE f) (toI-toE g)
toI-toE (I.∧l₁ f) = I.∧l₁ (toI-toE f)
toI-toE (I.∧l₂ f) = I.∧l₂ (toI-toE f)
toI-toE (I.∨r₁ f) = I.∨r₁ (toI-toE f)
toI-toE (I.∨r₂ f) = I.∨r₂ (toI-toE f)
toI-toE (I.∨l f g) = I.∨l (toI-toE f) (toI-toE g)
toI-toE (I.pass q f) =
  I.≡to≗ (trans (toI-ex-pickL q [] (E.pass refl (toE f)))
    (I.ex-pickL-pass q [] (toI (toE f)))) I.∙
  I.pass q (toI-toE f)
toI-toE (I.⊗r p f g) =
  I.≡to≗ (trans (toI-ex-part p [] (E.⊗r refl (toE f) (toE g)))
    (I.ex-part-⊗r p done (toI (toE f)) (toI (toE g)))) I.∙
  I.⊗r p (toI-toE f) (toI-toE g)
