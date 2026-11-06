{-# OPTIONS --safe #-}

module Emb (At : Set) where

open import Relation.Binary.PropositionalEquality.Core hiding (_≗_)

open import Fma At
open import FocusSeqCalc At
open import SeqCalc At

emb-ri : ∀ {S Γ A} → S ∣ Γ ⊢ri A → S ∣ Γ ⊢ A
emb-li : ∀ {S Γ A} → S ∣ Γ ⊢li A → S ∣ Γ ⊢ pos A
emb-f : ∀ {S Γ A} → S ∣ Γ ⊢f A → irr S ∣ Γ ⊢ pos A

emb-ri (∧r f g) = ∧r (emb-ri f) (emb-ri g)
emb-ri (⊸r f) = ⊸r (emb-ri f)
emb-ri (li2ri f) = emb-li f

emb-li (Il f) = Il (emb-li f)
emb-li (⊗l f) = ⊗l (emb-li f)
emb-li (∨l f g) = ∨l (emb-li f) (emb-li g)
emb-li (f2li f) = emb-f f

emb-f ax = ax
emb-f Ir = Ir
emb-f (pass f) = pass (emb-li f)
emb-f (∧l₁ f) = ∧l₁ (emb-li f)
emb-f (∧l₂ f) = ∧l₂ (emb-li f)
emb-f (⊸l refl f g) = ⊸l (emb-ri f) (emb-li g)
emb-f (⊗r refl f g ok) = ⊗r (emb-ri f) (emb-ri g)
emb-f (∨r₁ f ok) = ∨r₁ (emb-ri f)
emb-f (∨r₂ f ok) = ∨r₂ (emb-ri f)

