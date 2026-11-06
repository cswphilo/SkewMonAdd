{-# OPTIONS --safe #-}

module SeqCalc.Equiv.ExplImpl (At : Set) where

open import Data.Maybe using (just)
open import Data.List
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Utilities
open import Formulae At
import SeqCalc.ExplEq At as E
import SeqCalc.ImplEq At as I
open import SeqCalc.Equiv.Maps At public using (_∣_⊢I_; _∣_⊢E_; toI; toE)

-- Exchange compatibility, simultaneously with its Pick and Part cases.
-- All recursive calls descend through the input derivation or through
-- the exchange witness; no continuation arguments are used.
toE-ex : ∀ {S Γ Δ C} (σ : Swap Γ Δ) (f : S ∣ Γ ⊢I C)
  → (E.ex σ (toE f)) E.≗ (toE (I.ex σ f))
toE-ex-pass : ∀ {X Γ Δ Ω C} (Λ : Cxt) (σ : Swap Γ Δ) (q : Pick X Γ Ω)
  (f : (just X) ∣ (Λ ᴿ++ Ω) ⊢I C)
  → (E.ex (swapᴿ++ Λ σ) (toE (I.pass (pickᴿ++ Λ q) f))) E.≗ (toE (I.ex-pass Λ σ q f))
toE-ex-⊗r : ∀ {S Λ Ω Ξ Γ Δ Θ Θ' A B} (r : Part Λ Ω Ξ)
  (σ : Swap Θ Θ') (p : Part Γ Δ Θ)
  (f : S ∣ (Λ ᴿ++ Γ) ⊢I A) (g : - ∣ (Ω ᴿ++ Δ) ⊢I B)
  → (E.ex (swapᴿ++ Ξ σ) (toE (I.⊗r (partᴿ++ r p) f g))) E.≗ (toE (I.ex-⊗r r σ p f g))

toE-ex σ (I.Il f) = E.exIl σ E.∙ E.Il (toE-ex σ f)
toE-ex σ (I.⊗l f) = E.ex⊗l σ E.∙ E.⊗l (toE-ex (keep σ) f)
toE-ex σ (I.∧r f g) = E.ex∧r σ E.∙ E.∧r (toE-ex σ f) (toE-ex σ g)
toE-ex σ (I.∧l₁ f) = E.ex∧l₁ σ E.∙ E.∧l₁ (toE-ex σ f)
toE-ex σ (I.∧l₂ f) = E.ex∧l₂ σ E.∙ E.∧l₂ (toE-ex σ f)
toE-ex σ (I.∨r₁ f) = E.ex∨r₁ σ E.∙ E.∨r₁ (toE-ex σ f)
toE-ex σ (I.∨r₂ f) = E.ex∨r₂ σ E.∙ E.∨r₂ (toE-ex σ f)
toE-ex σ (I.∨l f g) = E.ex∨l σ E.∙ E.∨l (toE-ex σ f) (toE-ex σ g)
toE-ex σ (I.pass q f) = toE-ex-pass [] σ q f
toE-ex σ (I.⊗r p f g) = toE-ex-⊗r done σ p f g

toE-ex-pass Λ sw here f = E.≡to≗ (sym (E.ex-pickL-pickᴿ++ Λ (there here) (E.pass refl (toE f))))
toE-ex-pass Λ sw (there here) f =
  E.ex (swapᴿ++ Λ sw) (E.≡to≗ (E.ex-pickL-pickᴿ++ Λ (there here) (E.pass refl (toE f)))) E.∙
  E.ex-iso-prefix Λ _
toE-ex-pass Λ sw (there (there q)) f =
  E.ex (swapᴿ++ Λ sw)
    (E.≡to≗ (E.ex-pickL-pickᴿ++ Λ (there (there q)) (E.pass refl (toE f)))) E.∙
  E.ex-pickL-ex-two q Λ _ E.∙
  E.cong-ex-pickL (there (there q)) Λ
    (E.ex-pickL-pass-ex Λ sw (toE f)) E.∙
  E.≡to≗ (sym (E.ex-pickL-pickᴿ++ Λ (there (there q)) (E.pass refl (E.ex (swapᴿ++ Λ sw) (toE f))))) E.∙
  E.cong-ex-pickL (pickᴿ++ Λ (there (there q))) [] (E.pass refl (toE-ex (swapᴿ++ Λ sw) f))
toE-ex-pass Λ (keep σ) here f =
  E.ex-pickL-pass-ex Λ σ (toE f) E.∙
  E.cong-ex-pickL (pickᴿ++ Λ here) [] (E.pass refl (toE-ex (swapᴿ++ Λ σ) f))
toE-ex-pass Λ (keep {A = Y} σ) (there q) f = toE-ex-pass (Y ∷ Λ) σ q f

toE-ex-⊗r {Λ = Λ} r sw (left (left p)) f g =
  E.ex-part-⊗r-ll r done p (toE f) (toE g) E.∙
  E.cong-ex-part (partᴿ++ r (left (left p))) []
    (E.⊗r refl (toE-ex (swapᴿ++ Λ sw) f) E.refl)
toE-ex-⊗r {Ω = Ω} r sw (right (right p)) f g =
  E.ex-part-⊗r-rr r done p (toE f) (toE g) E.∙
  E.cong-ex-part (partᴿ++ r (right (right p))) []
    (E.⊗r refl E.refl (toE-ex (swapᴿ++ Ω sw) g))
toE-ex-⊗r r sw (left (right p)) f g = E.ex-part-⊗r-lr r done p (toE f) (toE g)
toE-ex-⊗r r sw (right (left p)) f g = E.ex-part-⊗r-rl r done p (toE f) (toE g)
toE-ex-⊗r r (keep σ) (left p) f g = toE-ex-⊗r (left r) σ p f g
toE-ex-⊗r r (keep σ) (right p) f g = toE-ex-⊗r (right r) σ p f g

-- The explicit calculus is recovered modulo its generating equations.
toE-toI : ∀ {S Γ C} (f : S ∣ Γ ⊢E C) → toE (toI f) E.≗ f
toE-toI E.ax = E.refl
toE-toI E.Ir = E.refl
toE-toI (E.pass refl f) = E.pass refl (toE-toI f)
toE-toI (E.Il f) = E.Il (toE-toI f)
toE-toI (E.⊗l f) = E.⊗l (toE-toI f)
toE-toI (E.⊗r {Γ = Γ} {Δ} refl f g) =
  E.≡to≗ (E.ex-part-eq Γ Δ [] (E.⊗r refl (toE (toI f)) (toE (toI g)))) E.∙
  E.⊗r refl (toE-toI f) (toE-toI g)
toE-toI (E.∧r f g) = E.∧r (toE-toI f) (toE-toI g)
toE-toI (E.∧l₁ f) = E.∧l₁ (toE-toI f)
toE-toI (E.∧l₂ f) = E.∧l₂ (toE-toI f)
toE-toI (E.∨r₁ f) = E.∨r₁ (toE-toI f)
toE-toI (E.∨r₂ f) = E.∨r₂ (toE-toI f)
toE-toI (E.∨l f g) = E.∨l (toE-toI f) (toE-toI g)
toE-toI (E.ex σ f) = (E.~ toE-ex σ (toI f)) E.∙ E.ex σ (toE-toI f)
