{-# OPTIONS --safe #-}

module Emb (At : Set) where

open import Relation.Binary.PropositionalEquality hiding (_≗_)

open import Formulae At
open import SeqCalc At
open import FocusedSeqCalc At

-- Forget focusing phases and their normal-form side conditions.
emb-ri : ∀ {S Γ C} (f : S ∣ Γ ⊢ri C) → S ∣ Γ ⊢ C
emb-li : ∀ {S Γ C} (f : S ∣ Γ ⊢li C) → S ∣ Γ ⊢ pos C
emb-f : ∀ {S Γ C} (f : S ∣ Γ ⊢f C) → irr S ∣ Γ ⊢ pos C

emb-ri (∧r f g) = ∧r (emb-ri f) (emb-ri g)
emb-ri (li2ri f) = emb-li f

emb-li (⊗l f) = ⊗l (emb-li f)
emb-li (Il f) = Il (emb-li f)
emb-li (∨l f g) = ∨l (emb-li f) (emb-li g)
emb-li (f2li f) = emb-f f

emb-f ax = ax
emb-f Ir = Ir
emb-f (pass f) = pass (emb-li f)
-- Matching refl identifies the conclusion context with the premise split.
emb-f (⊗r refl f g ok) = ⊗r (emb-ri f) (emb-ri g)
emb-f (∧l₁ f) = ∧l₁ (emb-li f)
emb-f (∧l₂ f) = ∧l₂ (emb-li f)
emb-f (∨r₁ f ok) = ∨r₁ (emb-ri f)
emb-f (∨r₂ f ok) = ∨r₂ (emb-ri f)
