{-# OPTIONS --safe #-}

module FocusWellDef (At : Set) where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
open import SeqCalc At
open import Tags
open import FocusedSeqCalc At
open import Focus At

-- Left rules acting on trees of positive conclusions.
Il-fs : ∀ {Γ Φ} → All (λ C → - ∣ Γ ⊢li C) Φ → All (λ C → just I ∣ Γ ⊢li C) Φ
Il-fs = mapAll Il

⊗l-fs : ∀ {A B Γ Φ} → All (λ C → just A ∣ B ∷ Γ ⊢li C) Φ → All (λ C → just (A ⊗ B) ∣ Γ ⊢li C) Φ
⊗l-fs = mapAll ⊗l

∨l-fs : ∀ {A B Γ Φ} → All (λ C → just A ∣ Γ ⊢li C) Φ → All (λ C → just B ∣ Γ ⊢li C) Φ → All (λ C → just (A ∨ B) ∣ Γ ⊢li C) Φ
∨l-fs = map2All ∨l

-- Exposing right-invertible premises commutes with each left rule.
∧r*invpass-ri : {Γ : Cxt} {A D : Fma} (f : just A ∣ Γ ⊢ri D)
  → ∧r*-ri-inv (pass-ri f) ≡ f2li-fs (pass-f-fs (∧r*-ri-inv f))
∧r*invpass-ri (∧r f g) = cong₂ node (∧r*invpass-ri f) (∧r*invpass-ri g)
∧r*invpass-ri (li2ri {C = (` X , _)} f) = refl
∧r*invpass-ri (li2ri {C = (I , _)} f) = refl
∧r*invpass-ri (li2ri {C = (A ⊗ B , _)} f) = refl
∧r*invpass-ri (li2ri {C = (A ∨ B , _)} f) = refl

∧r*invIl-ri : {Γ : Cxt} {D : Fma} (f : - ∣ Γ ⊢ri D)
  → ∧r*-ri-inv (Il-ri f) ≡ Il-fs (∧r*-ri-inv f)
∧r*invIl-ri (∧r f g) = cong₂ node (∧r*invIl-ri f) (∧r*invIl-ri g)
∧r*invIl-ri (li2ri {C = (` X , _)} f) = refl
∧r*invIl-ri (li2ri {C = (I , _)} f) = refl
∧r*invIl-ri (li2ri {C = (A ⊗ B , _)} f) = refl
∧r*invIl-ri (li2ri {C = (A ∨ B , _)} f) = refl

∧r*inv⊗l-ri : {Γ : Cxt} {A B D : Fma} (f : just A ∣ B ∷ Γ ⊢ri D)
  → ∧r*-ri-inv (⊗l-ri f) ≡ ⊗l-fs (∧r*-ri-inv f)
∧r*inv⊗l-ri (∧r f g) = cong₂ node (∧r*inv⊗l-ri f) (∧r*inv⊗l-ri g)
∧r*inv⊗l-ri (li2ri {C = (` X , _)} f) = refl
∧r*inv⊗l-ri (li2ri {C = (I , _)} f) = refl
∧r*inv⊗l-ri (li2ri {C = (A ⊗ B , _)} f) = refl
∧r*inv⊗l-ri (li2ri {C = (A ∨ B , _)} f) = refl

∧r*inv∧l₁-ri : {Γ : Cxt} {A B D : Fma} (f : just A ∣ Γ ⊢ri D)
  → ∧r*-ri-inv (∧l₁-ri {B = B} f) ≡ f2li-fs (∧l₁-f-fs (∧r*-ri-inv f))
∧r*inv∧l₁-ri (∧r f g) = cong₂ node (∧r*inv∧l₁-ri f) (∧r*inv∧l₁-ri g)
∧r*inv∧l₁-ri (li2ri {C = (` X , _)} f) = refl
∧r*inv∧l₁-ri (li2ri {C = (I , _)} f) = refl
∧r*inv∧l₁-ri (li2ri {C = (A ⊗ B , _)} f) = refl
∧r*inv∧l₁-ri (li2ri {C = (A ∨ B , _)} f) = refl

∧r*inv∧l₂-ri : {Γ : Cxt} {A B D : Fma} (f : just B ∣ Γ ⊢ri D)
  → ∧r*-ri-inv (∧l₂-ri {A = A} f) ≡ f2li-fs (∧l₂-f-fs (∧r*-ri-inv f))
∧r*inv∧l₂-ri (∧r f g) = cong₂ node (∧r*inv∧l₂-ri f) (∧r*inv∧l₂-ri g)
∧r*inv∧l₂-ri (li2ri {C = (` X , _)} f) = refl
∧r*inv∧l₂-ri (li2ri {C = (I , _)} f) = refl
∧r*inv∧l₂-ri (li2ri {C = (A ⊗ B , _)} f) = refl
∧r*inv∧l₂-ri (li2ri {C = (A ∨ B , _)} f) = refl

∧r*-inv∨l-ri : ∀ {A B Γ C} (f : just A ∣ Γ ⊢ri C) (g : just B ∣ Γ ⊢ri C)
  → ∧r*-ri-inv (∨l-ri f g) ≡ ∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv g)
∧r*-inv∨l-ri (∧r f f') (∧r g g') = cong₂ node (∧r*-inv∨l-ri f g) (∧r*-inv∨l-ri f' g')
∧r*-inv∨l-ri (li2ri {C = (` X , _)} f) (li2ri g) = refl
∧r*-inv∨l-ri (li2ri {C = (I , _)} f) (li2ri g) = refl
∧r*-inv∨l-ri (li2ri {C = (A ⊗ B , _)} f) (li2ri g) = refl
∧r*-inv∨l-ri (li2ri {C = (A ∨ B , _)} f) (li2ri g) = refl

-- The classifier recognizes trees with a shared noninvertible left rule.
check-focus-allpass : ∀ {A Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ)
  → check-focus (f2li-fs (pass-f-fs fs)) ≡ casepass (allPass fs refl refl refl)
check-focus-allpass (leaf f) = refl
check-focus-allpass (node fs gs) rewrite check-focus-allpass fs | check-focus-allpass gs = refl

check-focus-all∧l₁ : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ)
  → check-focus (f2li-fs (∧l₁-f-fs {B = B} fs)) ≡ case1 (all∧l₁ fs refl refl)
check-focus-all∧l₁ (leaf f) = refl
check-focus-all∧l₁ {B = B} (node fs gs) rewrite check-focus-all∧l₁ {B = B} fs | check-focus-all∧l₁ {B = B} gs = refl

check-focus-all∧l₂ : ∀ {A B Γ Φ} (fs : All (λ C → just B ∣ Γ ⊢li C) Φ)
  → check-focus (f2li-fs (∧l₂-f-fs {A = A} fs)) ≡ case2 (all∧l₂ fs refl refl)
check-focus-all∧l₂ (leaf f) = refl
check-focus-all∧l₂ {A = A} (node fs gs) rewrite check-focus-all∧l₂ {A = A} fs | check-focus-all∧l₂ {A = A} gs = refl

-- Inverting a left rule applied to a tree recovers its premises.
Il-inv-fsIl-fs : ∀ {Γ Φ} (fs : All (λ C → - ∣ Γ ⊢li C) Φ)
  → Il-inv-fs (Il-fs fs) ≡ fs
Il-inv-fsIl-fs (leaf f) = refl
Il-inv-fsIl-fs (node fs gs) = cong₂ node (Il-inv-fsIl-fs fs) (Il-inv-fsIl-fs gs)

⊗l-inv-fs⊗l-fs : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ B ∷ Γ ⊢li C) Φ)
  → ⊗l-inv-fs (⊗l-fs fs) ≡ fs
⊗l-inv-fs⊗l-fs (leaf f) = refl
⊗l-inv-fs⊗l-fs (node fs gs) = cong₂ node (⊗l-inv-fs⊗l-fs fs) (⊗l-inv-fs⊗l-fs gs)

∨l-inv-fs₁∨l-fs : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ) (gs : All (λ C → just B ∣ Γ ⊢li C) Φ)
  → ∨l-inv-fs₁ (∨l-fs fs gs) ≡ fs
∨l-inv-fs₁∨l-fs (leaf f) (leaf g) = refl
∨l-inv-fs₁∨l-fs (node fs fs') (node gs gs') = cong₂ node (∨l-inv-fs₁∨l-fs fs gs) (∨l-inv-fs₁∨l-fs fs' gs')

∨l-inv-fs₂∨l-fs : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ) (gs : All (λ C → just B ∣ Γ ⊢li C) Φ)
  → ∨l-inv-fs₂ (∨l-fs fs gs) ≡ gs
∨l-inv-fs₂∨l-fs (leaf f) (leaf g) = refl
∨l-inv-fs₂∨l-fs (node fs fs') (node gs gs') = cong₂ node (∨l-inv-fs₂∨l-fs fs gs) (∨l-inv-fs₂∨l-fs fs' gs')

-- The admissible right introductions respect the left-rule conversions.
⊗rpass-ri : {Γ Δ : Cxt} {A D E : Fma} (f : just A ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (pass-ri f) g ≡ pass-ri (⊗r-ri f g)
⊗rpass-ri f g rewrite ∧r*invpass-ri f | check-focus-allpass (∧r*-ri-inv f) = refl

⊗rIl-ri : {Γ Δ : Cxt} {D E : Fma} (f : - ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (Il-ri f) g ≡ Il-ri (⊗r-ri f g)
⊗rIl-ri f g rewrite ∧r*invIl-ri f | Il-inv-fsIl-fs (∧r*-ri-inv f) = refl

⊗r⊗l-ri : {Γ Δ : Cxt} {A B D E : Fma} (f : just A ∣ B ∷ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (⊗l-ri f) g ≡ ⊗l-ri (⊗r-ri f g)
⊗r⊗l-ri f g rewrite ∧r*inv⊗l-ri f | ⊗l-inv-fs⊗l-fs (∧r*-ri-inv f) = refl

⊗r∧l₁-ri : {Γ Δ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (∧l₁-ri {B = B} f) g ≡ ∧l₁-ri (⊗r-ri f g)
⊗r∧l₁-ri {B = B} f g rewrite ∧r*inv∧l₁-ri {B = B} f | check-focus-all∧l₁ {B = B} (∧r*-ri-inv f) = refl

⊗r∧l₂-ri : {Γ Δ : Cxt} {A B D E : Fma} (f : just B ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (∧l₂-ri {A = A} f) g ≡ ∧l₂-ri (⊗r-ri f g)
⊗r∧l₂-ri {A = A} f g rewrite ∧r*inv∧l₂-ri {A = A} f | check-focus-all∧l₂ {A = A} (∧r*-ri-inv f) = refl

⊗r∨l-ri : {Γ Δ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri D) (f' : just B ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (∨l-ri f f') g ≡ ∨l-ri (⊗r-ri f g) (⊗r-ri f' g)
⊗r∨l-ri f f' g rewrite ∧r*-inv∨l-ri f f' | ∨l-inv-fs₁∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f') | ∨l-inv-fs₂∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f') = refl

∨r₁pass-ri : {Γ : Cxt} {A D E : Fma} (f : just A ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (pass-ri f) ≡ pass-ri (∨r₁-ri {B = E} f)
∨r₁pass-ri f rewrite ∧r*invpass-ri f | check-focus-allpass (∧r*-ri-inv f) = refl

∨r₁Il-ri : {Γ : Cxt} {D E : Fma} (f : - ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (Il-ri f) ≡ Il-ri (∨r₁-ri {B = E} f)
∨r₁Il-ri f rewrite ∧r*invIl-ri f | Il-inv-fsIl-fs (∧r*-ri-inv f) = refl

∨r₁⊗l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ B ∷ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (⊗l-ri f) ≡ ⊗l-ri (∨r₁-ri {B = E} f)
∨r₁⊗l-ri f rewrite ∧r*inv⊗l-ri f | ⊗l-inv-fs⊗l-fs (∧r*-ri-inv f) = refl

∨r₁∧l₁-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₁-ri {B = E} f)
∨r₁∧l₁-ri {B = B} f rewrite ∧r*inv∧l₁-ri {B = B} f | check-focus-all∧l₁ {B = B} (∧r*-ri-inv f) = refl

∨r₁∧l₂-ri : {Γ : Cxt} {A B D E : Fma} (f : just B ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₁-ri {B = E} f)
∨r₁∧l₂-ri {A = A} f rewrite ∧r*inv∧l₂-ri {A = A} f | check-focus-all∧l₂ {A = A} (∧r*-ri-inv f) = refl

∨r₁∨l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri D) (f' : just B ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∨l-ri f f') ≡ ∨l-ri (∨r₁-ri {B = E} f) (∨r₁-ri {B = E} f')
∨r₁∨l-ri f f' rewrite ∧r*-inv∨l-ri f f' | ∨l-inv-fs₁∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f') | ∨l-inv-fs₂∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f') = refl

∨r₂pass-ri : {Γ : Cxt} {A D E : Fma} (f : just A ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (pass-ri f) ≡ pass-ri (∨r₂-ri {A = D} f)
∨r₂pass-ri f rewrite ∧r*invpass-ri f | check-focus-allpass (∧r*-ri-inv f) = refl

∨r₂Il-ri : {Γ : Cxt} {D E : Fma} (f : - ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (Il-ri f) ≡ Il-ri (∨r₂-ri {A = D} f)
∨r₂Il-ri f rewrite ∧r*invIl-ri f | Il-inv-fsIl-fs (∧r*-ri-inv f) = refl

∨r₂⊗l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ B ∷ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (⊗l-ri f) ≡ ⊗l-ri (∨r₂-ri {A = D} f)
∨r₂⊗l-ri f rewrite ∧r*inv⊗l-ri f | ⊗l-inv-fs⊗l-fs (∧r*-ri-inv f) = refl

∨r₂∧l₁-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₂-ri {A = D} f)
∨r₂∧l₁-ri {B = B} f rewrite ∧r*inv∧l₁-ri {B = B} f | check-focus-all∧l₁ {B = B} (∧r*-ri-inv f) = refl

∨r₂∧l₂-ri : {Γ : Cxt} {A B D E : Fma} (f : just B ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₂-ri {A = D} f)
∨r₂∧l₂-ri {A = A} f rewrite ∧r*inv∧l₂-ri {A = A} f | check-focus-all∧l₂ {A = A} (∧r*-ri-inv f) = refl

∨r₂∨l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri E) (f' : just B ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∨l-ri f f') ≡ ∨l-ri (∨r₂-ri {A = D} f) (∨r₂-ri {A = D} f')
∨r₂∨l-ri f f' rewrite ∧r*-inv∨l-ri f f' | ∨l-inv-fs₁∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f') | ∨l-inv-fs₂∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f') = refl

-- Equivalent derivations have equal focused normal forms.
eqfocus : {S : Stp} {Γ : Cxt} {C : Fma}
  → {f f' : S ∣ Γ ⊢ C}
  → f ≗ f'
  → focus f ≡ focus f'
eqfocus refl = refl
eqfocus (~ eq) = sym (eqfocus eq)
eqfocus (eq ∙ eq₁) = trans (eqfocus eq) (eqfocus eq₁)
eqfocus (pass eq) = cong pass-ri (eqfocus eq)
eqfocus (Il eq) = cong Il-ri (eqfocus eq)
eqfocus (⊗l eq) = cong ⊗l-ri (eqfocus eq)
eqfocus (⊗r eq eq₁) = cong₂ (λ x y → ⊗r-ri x y) (eqfocus eq) (eqfocus eq₁)
eqfocus (∧r eq eq₁) = cong₂ (λ x y → ∧r x y) (eqfocus eq) (eqfocus eq₁)
eqfocus (∧l₁ eq) = cong ∧l₁-ri (eqfocus eq)
eqfocus (∧l₂ eq) = cong ∧l₂-ri (eqfocus eq)
eqfocus axI = refl
eqfocus ax⊗ = refl
eqfocus ax∧ = refl
eqfocus ax∨ = refl
eqfocus (⊗rpass {f = f} {g}) = ⊗rpass-ri (focus f) (focus g)
eqfocus (⊗rIl {f = f} {g}) = ⊗rIl-ri (focus f) (focus g)
eqfocus (⊗r⊗l {f = f} {g}) = ⊗r⊗l-ri (focus f) (focus g)
eqfocus (⊗r∧l₁ {f = f} {g}) = ⊗r∧l₁-ri (focus f) (focus g)
eqfocus (⊗r∧l₂ {f = f} {g}) = ⊗r∧l₂-ri (focus f) (focus g)
eqfocus (⊗r∨l {f = f} {f'} {g}) = ⊗r∨l-ri (focus f) (focus f') (focus g)
eqfocus ∧rpass = refl
eqfocus ∧rIl = refl
eqfocus ∧r⊗l = refl
eqfocus ∧r∧l₁ = refl
eqfocus ∧r∧l₂ = refl
eqfocus ∧r∨l = refl
eqfocus (∨r₁ eq) = cong ∨r₁-ri (eqfocus eq)
eqfocus (∨r₂ eq) = cong ∨r₂-ri (eqfocus eq)
eqfocus (∨l eq1 eq2) = cong₂ (λ x y → ∨l-ri x y) (eqfocus eq1) (eqfocus eq2)
eqfocus (∨r₁pass {f = f}) = ∨r₁pass-ri (focus f)
eqfocus (∨r₁Il {f = f}) = ∨r₁Il-ri (focus f)
eqfocus (∨r₁⊗l {f = f}) = ∨r₁⊗l-ri (focus f)
eqfocus (∨r₁∧l₁ {f = f}) = ∨r₁∧l₁-ri (focus f)
eqfocus (∨r₁∧l₂ {f = f}) = ∨r₁∧l₂-ri (focus f)
eqfocus (∨r₁∨l {f = f} {g}) = ∨r₁∨l-ri (focus f) (focus g)
eqfocus (∨r₂pass {f = f}) = ∨r₂pass-ri (focus f)
eqfocus (∨r₂Il {f = f}) = ∨r₂Il-ri (focus f)
eqfocus (∨r₂⊗l {f = f}) = ∨r₂⊗l-ri (focus f)
eqfocus (∨r₂∧l₁ {f = f}) = ∨r₂∧l₁-ri (focus f)
eqfocus (∨r₂∧l₂ {f = f}) = ∨r₂∧l₂-ri (focus f)
eqfocus (∨r₂∨l {f = f} {g}) = ∨r₂∨l-ri (focus f) (focus g)
