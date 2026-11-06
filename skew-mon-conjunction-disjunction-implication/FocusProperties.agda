{-# OPTIONS --safe #-}

module FocusProperties (At : Set) where

open import Data.List.Base hiding (head)
open import Data.List.Relation.Unary.All as LA using ()
open import Agda.Builtin.Maybe
open import Data.Product.Base
open import Agda.Builtin.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality.Core

open import Utilities
open import Fma At
open import FocusSeqCalc At
open import FocusSeqCalcProperties At
open import Focus At

-- Left rules on premise trees used by FocusEq and EmbFocus.

Il-fs : ∀ {Γ Φ} → All (λ x → - ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just I) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
Il-fs = mapAll Il

⊗l-fs : ∀ {Γ A B Φ} → All (λ x → (just A) ∣ (B ∷ Γ) ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just (A ⊗ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
⊗l-fs = mapAll ⊗l

∨l-fs : ∀ {Γ A B Φ} → All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just (A ∨ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
∨l-fs = map2All ∨l

-- The disjunction-left phase change used by FocusEmb.

∨l-ri-li2ri : ∀ {Γ A B C} (f : just A ∣ Γ ⊢li C) (g : just B ∣ Γ ⊢li C)
  → ∨l-ri (li2ri f) (li2ri g) ≡ li2ri (∨l f g)
∨l-ri-li2ri {C = ` X , tt} f g = refl
∨l-ri-li2ri {C = I , tt} f g = refl
∨l-ri-li2ri {C = A ⊗ B , tt} f g = refl
∨l-ri-li2ri {C = A ∨ B , tt} f g = refl

subst-li-⊸l : ∀ {Γ Δ Λ Ξ A B C} (p : Λ ≡ Ξ) (q : Λ ≡ Γ ++ Δ) (r : Ξ ≡ Γ ++ Δ)
  (h : - ∣ Γ ⊢ri A) (f : just B ∣ Δ ⊢li C) → subst-li p (f2li (⊸l q h f)) ≡ f2li (⊸l r h f)
subst-li-⊸l refl q r h f rewrite uip {p = q} {r} = refl

Il-ri*-inv : ∀ {Γ Λ C} (Ω : Cxt) (f : - ∣ (Λ) ⊢ri C) (eq : Λ ≡ Γ ++ Ω)
  → ri*-inv {Γ = Γ} Ω (Il-ri f) (eq) ≡ Il-fs (ri*-inv {Γ = Γ} Ω f (eq))
Il-ri*-inv {Γ} {Λ} Ω (∧r f g) refl = cong₂ node (Il-ri*-inv Ω f refl) (Il-ri*-inv Ω g refl)
Il-ri*-inv {Γ} {Λ} Ω (⊸r {A = D} f) refl = Il-ri*-inv {Γ = Γ} (Ω ++ [ D ]) f (++ass Γ)
Il-ri*-inv Ω (li2ri {C = ` X , tt} f) refl = refl
Il-ri*-inv Ω (li2ri {C = I , tt} f) refl = refl
Il-ri*-inv Ω (li2ri {C = D ⊗ E , tt} f) refl = refl
Il-ri*-inv Ω (li2ri {C = D ∨ E , tt} f) refl = refl

⊗l-ri*-inv : ∀ {Γ Λ A B C} (Ω : Cxt) (f : just A ∣ (B ∷ Λ) ⊢ri C) (eq : Λ ≡ Γ ++ Ω)
  → ri*-inv {Γ = Γ} Ω (⊗l-ri f) (eq) ≡ ⊗l-fs {Γ} {A} {B} (ri*-inv {Γ = B ∷ Γ} Ω f (cong (B ∷_) eq))
⊗l-ri*-inv {Γ} {Λ} {A} {B} Ω (∧r f g) refl = cong₂ node (⊗l-ri*-inv Ω f refl) (⊗l-ri*-inv Ω g refl)
⊗l-ri*-inv {Γ} {Λ} {A} {B} Ω (⊸r {A = D} f) refl = ⊗l-ri*-inv {Γ = Γ} {A = A} {B = B} (Ω ++ [ D ]) f (++ass Γ)
⊗l-ri*-inv Ω (li2ri {C = ` X , tt} f) refl = refl
⊗l-ri*-inv Ω (li2ri {C = I , tt} f) refl = refl
⊗l-ri*-inv Ω (li2ri {C = D ⊗ E , tt} f) refl = refl
⊗l-ri*-inv Ω (li2ri {C = D ∨ E , tt} f) refl = refl

pass-ri*-inv : ∀ {Γ Λ A C} (Ω : Cxt) (f : just A ∣ (Λ) ⊢ri C) (eq : Λ ≡ Γ ++ Ω)
  → ri*-inv {Γ = A ∷ Γ} Ω (pass-ri f) (cong (A ∷_) eq) ≡ pass-fs {Γ} {A} (ri*-inv {Γ = Γ} Ω f (eq))
pass-ri*-inv {Γ} {Λ} {A} Ω (∧r f g) refl = cong₂ node (pass-ri*-inv Ω f refl) (pass-ri*-inv Ω g refl)
pass-ri*-inv {Γ} {Λ} {A} Ω (⊸r {A = D} f) refl = pass-ri*-inv {Γ = Γ} {A = A} (Ω ++ [ D ]) f (++ass Γ)
pass-ri*-inv Ω (li2ri {C = ` X , tt} f) refl = refl
pass-ri*-inv Ω (li2ri {C = I , tt} f) refl = refl
pass-ri*-inv Ω (li2ri {C = D ⊗ E , tt} f) refl = refl
pass-ri*-inv Ω (li2ri {C = D ∨ E , tt} f) refl = refl

∧l₁-ri*-inv : ∀ {Γ Λ A B C} (Ω : Cxt) (f : just A ∣ (Λ) ⊢ri C) (eq : Λ ≡ Γ ++ Ω)
  → ri*-inv {Γ = Γ} Ω (∧l₁-ri {B = B} f) (eq) ≡ ∧l₁-fs {Γ} {A} {B} (ri*-inv {Γ = Γ} Ω f (eq))
∧l₁-ri*-inv {Γ} {Λ} {A} {B} Ω (∧r f g) refl = cong₂ node (∧l₁-ri*-inv Ω f refl) (∧l₁-ri*-inv Ω g refl)
∧l₁-ri*-inv {Γ} {Λ} {A} {B} Ω (⊸r {A = D} f) refl = ∧l₁-ri*-inv {Γ = Γ} {A = A} {B = B} (Ω ++ [ D ]) f (++ass Γ)
∧l₁-ri*-inv Ω (li2ri {C = ` X , tt} f) refl = refl
∧l₁-ri*-inv Ω (li2ri {C = I , tt} f) refl = refl
∧l₁-ri*-inv Ω (li2ri {C = D ⊗ E , tt} f) refl = refl
∧l₁-ri*-inv Ω (li2ri {C = D ∨ E , tt} f) refl = refl

∧l₂-ri*-inv : ∀ {Γ Λ A B C} (Ω : Cxt) (f : just B ∣ (Λ) ⊢ri C) (eq : Λ ≡ Γ ++ Ω)
  → ri*-inv {Γ = Γ} Ω (∧l₂-ri {A = A} f) (eq) ≡ ∧l₂-fs {Γ} {A} {B} (ri*-inv {Γ = Γ} Ω f (eq))
∧l₂-ri*-inv {Γ} {Λ} {A} {B} Ω (∧r f g) refl = cong₂ node (∧l₂-ri*-inv Ω f refl) (∧l₂-ri*-inv Ω g refl)
∧l₂-ri*-inv {Γ} {Λ} {A} {B} Ω (⊸r {A = D} f) refl = ∧l₂-ri*-inv {Γ = Γ} {A = A} {B = B} (Ω ++ [ D ]) f (++ass Γ)
∧l₂-ri*-inv Ω (li2ri {C = ` X , tt} f) refl = refl
∧l₂-ri*-inv Ω (li2ri {C = I , tt} f) refl = refl
∧l₂-ri*-inv Ω (li2ri {C = D ⊗ E , tt} f) refl = refl
∧l₂-ri*-inv Ω (li2ri {C = D ∨ E , tt} f) refl = refl

⊸l-ri*-inv : ∀ {Γ Δ Λ A B C} (Ω : Cxt) (h : - ∣ Γ ⊢ri A) (f : just B ∣ Λ ⊢ri C) (eq : Λ ≡ Δ ++ Ω)
  → ri*-inv {Γ = Γ ++ Δ} Ω (⊸l-ri h f) (trans (cong (Γ ++_) eq) (sym (++ass Γ)))
    ≡ ⊸l-fs {Γ} {Δ} h (ri*-inv {Γ = Δ} Ω f eq)
⊸l-ri*-inv {Γ} {Δ} Ω h (∧r f g) refl = cong₂ node (⊸l-ri*-inv Ω h f refl) (⊸l-ri*-inv Ω h g refl)
⊸l-ri*-inv {Γ} {Δ} Ω h (⊸r {A = D} f) refl =
  trans (ri*-inv-subst (Ω ++ [ D ]) (sym (++ass Γ)) (⊸l-ri h f) (trans (cong (_++ [ D ]) (sym (++ass Γ))) (++ass (Γ ++ Δ))))
    (trans (cong (ri*-inv {Γ = Γ ++ Δ} (Ω ++ [ D ]) (⊸l-ri h f)) uip) (⊸l-ri*-inv {Γ} {Δ} (Ω ++ [ D ]) h f (++ass Δ)))
⊸l-ri*-inv {Γ} Ω h (li2ri {C = ` X , tt} f) refl = cong leaf (subst-li-⊸l (sym (++ass Γ)) refl (++ass Γ) h f)
⊸l-ri*-inv {Γ} Ω h (li2ri {C = I , tt} f) refl = cong leaf (subst-li-⊸l (sym (++ass Γ)) refl (++ass Γ) h f)
⊸l-ri*-inv {Γ} Ω h (li2ri {C = D ⊗ E , tt} f) refl = cong leaf (subst-li-⊸l (sym (++ass Γ)) refl (++ass Γ) h f)
⊸l-ri*-inv {Γ} Ω h (li2ri {C = D ∨ E , tt} f) refl = cong leaf (subst-li-⊸l (sym (++ass Γ)) refl (++ass Γ) h f)

∨l-ri*-inv : ∀ {Γ Λ A B C} (Ω : Cxt) (f : just A ∣ Λ ⊢ri C) (g : just B ∣ Λ ⊢ri C) (eq : Λ ≡ Γ ++ Ω)
  → ri*-inv Ω (∨l-ri f g) eq ≡ ∨l-fs (ri*-inv Ω f eq) (ri*-inv Ω g eq)
∨l-ri*-inv Ω (∧r f g) (∧r f' g') refl = cong₂ node (∨l-ri*-inv Ω f f' refl) (∨l-ri*-inv Ω g g' refl)
∨l-ri*-inv {Γ} Ω (⊸r {A = D} f) (⊸r g) refl = ∨l-ri*-inv (Ω ++ [ D ]) f g (++ass Γ)
∨l-ri*-inv Ω (li2ri {C = ` X , tt} f) (li2ri g) refl = refl
∨l-ri*-inv Ω (li2ri {C = I , tt} f) (li2ri g) refl = refl
∨l-ri*-inv Ω (li2ri {C = D ⊗ E , tt} f) (li2ri g) refl = refl
∨l-ri*-inv Ω (li2ri {C = D ∨ E , tt} f) (li2ri g) refl = refl

Il-ri-inv : ∀ {Γ C} (f : - ∣ Γ ⊢ri C) → ri-inv (Il-ri f) ≡ Il-fs (ri-inv f)
Il-ri-inv {Γ} f = Il-ri*-inv [] f (sym (++ru Γ))

⊗l-ri-inv : ∀ {Γ A B C} (f : just A ∣ B ∷ Γ ⊢ri C) → ri-inv (⊗l-ri f) ≡ ⊗l-fs {Γ} {A} {B} (ri-inv f)
⊗l-ri-inv {Γ} {A} {B} f = trans (⊗l-ri*-inv [] f (sym (++ru Γ)))
  (cong (⊗l-fs {Γ} {A} {B}) (cong (ri*-inv {Γ = B ∷ Γ} [] f) uip))

pass-ri-inv : ∀ {Γ A C} (f : just A ∣ Γ ⊢ri C) → ri-inv (pass-ri f) ≡ pass-fs (ri-inv f)
pass-ri-inv {Γ} {A} f = trans (cong (ri*-inv {Γ = A ∷ Γ} [] (pass-ri f)) uip) (pass-ri*-inv [] f (sym (++ru Γ)))

∧l₁-ri-inv : ∀ {Γ A B C} (f : just A ∣ Γ ⊢ri C) → ri-inv (∧l₁-ri {B = B} f) ≡ ∧l₁-fs (ri-inv f)
∧l₁-ri-inv {Γ} f = ∧l₁-ri*-inv [] f (sym (++ru Γ))

∧l₂-ri-inv : ∀ {Γ A B C} (f : just B ∣ Γ ⊢ri C) → ri-inv (∧l₂-ri {A = A} f) ≡ ∧l₂-fs (ri-inv f)
∧l₂-ri-inv {Γ} f = ∧l₂-ri*-inv [] f (sym (++ru Γ))

⊸l-ri-inv : ∀ {Γ Δ A B C} (h : - ∣ Γ ⊢ri A) (f : just B ∣ Δ ⊢ri C) → ri-inv (⊸l-ri h f) ≡ ⊸l-fs {Γ} {Δ} h (ri-inv f)
⊸l-ri-inv {Γ} {Δ} h f = trans (cong (ri*-inv {Γ = Γ ++ Δ} [] (⊸l-ri h f)) uip) (⊸l-ri*-inv [] h f (sym (++ru Δ)))

∨l-ri-inv : ∀ {Γ A B C} (f : just A ∣ Γ ⊢ri C) (g : just B ∣ Γ ⊢ri C) → ri-inv (∨l-ri f g) ≡ ∨l-fs (ri-inv f) (ri-inv g)
∨l-ri-inv {Γ} f g = ∨l-ri*-inv [] f g (sym (++ru Γ))

ri*-eq : ∀ {S Γ A} (f : S ∣ Γ ⊢ri A) {fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)}
  → ri-inv f ≡ fs → f ≡ ri*₀ A fs
ri*-eq {A = A} f e = trans (sym (ri*₀ri-inv f)) (cong (ri*₀ A) e)

Il-ri* : ∀ {Γ} (C : Fma) (fs : All (λ x → (-) ∣ (Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → Il-ri (ri*₀ {Γ = Γ} C fs) ≡ ri*₀ {Γ = Γ} C (Il-fs {Γ = Γ} fs)
Il-ri* {Γ} C fs = ri*-eq {Γ = Γ} _ (trans (Il-ri-inv {Γ} (ri*₀ {Γ = Γ} C fs)) (cong (Il-fs {Γ = Γ}) (ri-inv-ri*₀ {Γ = Γ} C fs)))

⊗l-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just A) ∣ (B ∷ Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → ⊗l-ri (ri*₀ {Γ = B ∷ Γ} C fs) ≡ ri*₀ {Γ = Γ} C (⊗l-fs {Γ} {A} {B} fs)
⊗l-ri* {Γ} {A} {B} C fs = ri*-eq {Γ = Γ} _ (trans (⊗l-ri-inv {Γ} {A} {B} (ri*₀ {Γ = B ∷ Γ} C fs)) (cong (⊗l-fs {Γ} {A} {B}) (ri-inv-ri*₀ {Γ = B ∷ Γ} C fs)))

pass-ri* : ∀ {Γ A} (C : Fma) (fs : All (λ x → (just A) ∣ (Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → pass-ri (ri*₀ {Γ = Γ} C fs) ≡ ri*₀ {Γ = A ∷ Γ} C (pass-fs {Γ} {A} fs)
pass-ri* {Γ} {A} C fs = ri*-eq {Γ = A ∷ Γ} _ (trans (pass-ri-inv {Γ} {A} (ri*₀ {Γ = Γ} C fs)) (cong (pass-fs {Γ} {A}) (ri-inv-ri*₀ {Γ = Γ} C fs)))

∧l₁-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just A) ∣ (Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → ∧l₁-ri {B = B} (ri*₀ {Γ = Γ} C fs) ≡ ri*₀ {Γ = Γ} C (∧l₁-fs {Γ} {A} {B} fs)
∧l₁-ri* {Γ} {A} {B} C fs = ri*-eq {Γ = Γ} _ (trans (∧l₁-ri-inv {Γ} {A} {B} (ri*₀ {Γ = Γ} C fs)) (cong (∧l₁-fs {Γ} {A} {B}) (ri-inv-ri*₀ {Γ = Γ} C fs)))

∧l₂-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just B) ∣ (Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → ∧l₂-ri {A = A} (ri*₀ {Γ = Γ} C fs) ≡ ri*₀ {Γ = Γ} C (∧l₂-fs {Γ} {A} {B} fs)
∧l₂-ri* {Γ} {A} {B} C fs = ri*-eq {Γ = Γ} _ (trans (∧l₂-ri-inv {Γ} {A} {B} (ri*₀ {Γ = Γ} C fs)) (cong (∧l₂-fs {Γ} {A} {B}) (ri-inv-ri*₀ {Γ = Γ} C fs)))

⊸l-ri* : ∀ {Γ Δ A B} (C : Fma) (h : - ∣ Γ ⊢ri A) (fs : All (λ x → (just B) ∣ (Δ) ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → ⊸l-ri h (ri*₀ {Γ = Δ} C fs) ≡ ri*₀ {Γ = Γ ++ Δ} C (⊸l-fs {Γ} {Δ} {A} {B} h fs)
⊸l-ri* {Γ} {Δ} {A} {B} C h fs = ri*-eq {Γ = Γ ++ Δ} _ (trans (⊸l-ri-inv {Γ} {Δ} {A} {B} h (ri*₀ {Γ = Δ} C fs)) (cong (⊸l-fs {Γ} {Δ} {A} {B} h) (ri-inv-ri*₀ {Γ = Δ} C fs)))

∨l-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C)) (gs : All (λ x → (just B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → ∨l-ri (ri*₀ {Γ = Γ} C fs) (ri*₀ {Γ = Γ} C gs) ≡ ri*₀ {Γ = Γ} C (∨l-fs fs gs)
∨l-ri* {Γ} C fs gs = ri*-eq {Γ = Γ} _ (trans (∨l-ri-inv {Γ} (ri*₀ {Γ = Γ} C fs) (ri*₀ {Γ = Γ} C gs)) (cong₂ ∨l-fs (ri-inv-ri*₀ {Γ = Γ} C fs) (ri-inv-ri*₀ {Γ = Γ} C gs)))

-- Validity lemmas used by FocusEmb to rule out a common left rule.

notOK-P : ∀ {ts} → LA.All (λ t → t ≡ P) ts → isOK ts → ⊥
notOK-P LA.[] ()
notOK-P (refl LA.∷ ps) ok = notOK-P ps ok

isOKC₁-only : ∀ {ts} → LA.All (λ t → t ≡ C₁) ts → isOKC₁ ts → ⊥
isOKC₁-only LA.[] ok = ok
isOKC₁-only (refl LA.∷ ps) ok = isOKC₁-only ps ok

notOK-C₁ : ∀ {ts} → LA.All (λ t → t ≡ C₁) ts → isOK ts → ⊥
notOK-C₁ LA.[] ()
notOK-C₁ (refl LA.∷ ps) ok = isOKC₁-only ps ok

isOKC₂-only : ∀ {ts} → LA.All (λ t → t ≡ C₂) ts → isOKC₂ ts → ⊥
isOKC₂-only LA.[] ok = ok
isOKC₂-only (refl LA.∷ ps) ok = isOKC₂-only ps ok

notOK-C₂ : ∀ {ts} → LA.All (λ t → t ≡ C₂) ts → isOK ts → ⊥
notOK-C₂ LA.[] ()
notOK-C₂ (refl LA.∷ ps) ok = isOKC₂-only ps ok

notOK-⊸l-tail : ∀ {A Γ ts} (f : - ∣ Γ ⊢ri A) → LA.All (λ t → t ≡ ⊸l Γ f) ts → isOK⊸l Γ f ts → ⊥
notOK-⊸l-tail f LA.[] ()
notOK-⊸l-tail {Γ = Γ} f (refl LA.∷ ps) ok
  rewrite length≟-refl Γ | eq-ri-refl f = notOK-⊸l-tail f ps ok

notOK-only⊸l : ∀ {A Γ ts} (f : - ∣ Γ ⊢ri A) → LA.All (λ t → t ≡ ⊸l Γ f) ts → isOK ts → ⊥
notOK-only⊸l f LA.[] ()
notOK-only⊸l f (refl LA.∷ ps) ok = notOK-⊸l-tail f ps ok

notOK-pass : ∀ {A Γ Φ} (fs : All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → isOK (tags-fs ((-) , tt) (A ∷ Γ) (pass-fs fs)) → ⊥
notOK-pass fs = notOK-P (tags-onlyP fs)

notOK-∧l₁ : ∀ {A B Γ Φ} (fs : All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → isOK (tags-fs ((just (A ∧ B)) , tt) (Γ) (∧l₁-fs fs)) → ⊥
notOK-∧l₁ {B = B} fs = notOK-C₁ (tags-onlyC₁ {B = B} fs)

notOK-∧l₂ : ∀ {A B Γ Φ} (fs : All (λ x → (just B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → isOK (tags-fs ((just (A ∧ B)) , tt) (Γ) (∧l₂-fs fs)) → ⊥
notOK-∧l₂ {A = A} fs = notOK-C₂ (tags-onlyC₂ {A = A} fs)

notOK-⊸l : ∀ {A B Γ Δ Φ} (h : - ∣ Γ ⊢ri A) (fs : All (λ x → (just B) ∣ Δ ++ proj₁ x ⊢li proj₂ x) Φ) → isOK (tags-fs (just (A ⊸ B) , tt) (Γ ++ Δ) (⊸l-fs {Δ = Δ} h fs)) → ⊥
notOK-⊸l f fs = notOK-only⊸l f (tags-only⊸l (all⊸l f fs refl refl refl))
