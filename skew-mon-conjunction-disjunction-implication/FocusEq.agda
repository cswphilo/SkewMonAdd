{-# OPTIONS --safe #-}

module FocusEq (At : Set) where

open import Data.List.Base hiding (head)
open import Agda.Builtin.Maybe
open import Data.Product.Base
open import Agda.Builtin.Unit
open import Data.Empty
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality.Core hiding (_≗_)

open import Utilities
open import Fma At
open import SeqCalc At
open import FocusSeqCalc At
open import FocusSeqCalcProperties At
open import Focus At
open import FocusProperties At

≟ri-refl : ∀ {S Γ A} (f : S ∣ Γ ⊢ri A) → (f ≟ri f) ≡ yes refl
≟ri-refl f with f ≟ri f
... | yes p rewrite uip {p = p} {refl} = refl
... | no n = ⊥-elim (n refl)

check-focus-pass : ∀ {A Γ Φ} (fs : All (λ x → just A ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → check-focus { - , tt} {A ∷ Γ} (pass-fs fs) ≡ casepass (allpass fs refl refl refl)
check-focus-pass {Φ = leaf (Ω , C)} (leaf f) = refl
check-focus-pass {A} {Γ} (node fs gs) rewrite check-focus-pass {A} {Γ} fs | check-focus-pass {A} {Γ} gs = refl

check-focus-∧l₁ : ∀ {A B Γ Φ} (fs : All (λ x → just A ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → check-focus {just (A ∧ B) , tt} {Γ} (∧l₁-fs fs) ≡ case1 (all∧l₁ fs refl refl)
check-focus-∧l₁ {Φ = leaf (Ω , C)} (leaf f) = refl
check-focus-∧l₁ {A} {B} {Γ} (node fs gs) rewrite check-focus-∧l₁ {A} {B} {Γ} fs | check-focus-∧l₁ {A} {B} {Γ} gs = refl

check-focus-∧l₂ : ∀ {A B Γ Φ} (fs : All (λ x → just B ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → check-focus {just (A ∧ B) , tt} {Γ} (∧l₂-fs fs) ≡ case2 (all∧l₂ fs refl refl)
check-focus-∧l₂ {Φ = leaf (Ω , C)} (leaf f) = refl
check-focus-∧l₂ {A} {B} {Γ} (node fs gs) rewrite check-focus-∧l₂ {A} {B} {Γ} fs | check-focus-∧l₂ {A} {B} {Γ} gs = refl

old-eq : ∀ {A Λ Γ Ω Δ t} {h : - ∣ Λ ⊢ri A} {Ξ Ξ'} (e : Ξ ≡ Ξ')
  {p : Γ ≡ Λ ++ Ξ} {p' : Γ ≡ Λ ++ Ξ'} {q : Δ ≡ Ξ ++ Ω} {q' : Δ ≡ Ξ' ++ Ω} {r r' : t ≡ ⊸l Λ h}
  → _≡_ {A = Check⊸l h Γ Ω Δ t} (old Ξ p q r) (old Ξ' p' q' r')
old-eq refl {p} {p'} {q} {q'} {r} {r'} rewrite uip {p = p} {p'} | uip {p = q} {q'} | uip {p = r} {r'} = refl

check-⊸l-old : ∀ {A B Γ Δ Ω C} (h : - ∣ Γ ⊢ri A) (f : just B ∣ Δ ++ Ω ⊢li C) →
  Σ (tag-f (Γ ++ Δ) Ω (⊸l (++ass Γ) h f) refl ≡ ⊸l Γ h)
    (λ t → check-⊸l (Γ ++ Δ) Ω (++ass Γ) h f refl ≡ old Δ refl refl t)
check-⊸l-old {Γ = Γ} {Δ} {Ω = []} h f = refl , old-eq (++ru Δ)
check-⊸l-old {Γ = Γ} {Δ} {D ∷ Ω} h f rewrite cases++-inj₂ Δ Γ Ω D (sym (++ass Γ)) = refl , refl

check-focus-⊸l-all : ∀ {A B Γ Δ Φ} (h : - ∣ Γ ⊢ri A) (fs : All (λ x → just B ∣ Δ ++ proj₁ x ⊢li proj₂ x) Φ)
  → check-focus {just (A ⊸ B) , tt} {Γ ++ Δ} (⊸l-fs {Δ = Δ} h fs) ≡ case⊸l (all⊸l h fs refl refl refl)
check-focus-⊸l-all {Γ = Γ} {Δ} {leaf (Ω , C)} h (leaf f) rewrite proj₂ (check-⊸l-old {Γ = Γ} {Δ} {Ω} h f) = cong (λ e → case⊸l (all⊸l h (leaf f) refl refl e)) uip
check-focus-⊸l-all {A} {B} {Γ} {Δ} h (node fs gs)
  rewrite check-focus-⊸l-all {A} {B} {Γ} {Δ} h fs | check-focus-⊸l-all {A} {B} {Γ} {Δ} h gs | split≟-refl Γ Δ | ≟ri-refl h = refl

Il-inv-fs-Il-fs : ∀ {Γ Φ} (fs : All (λ x → - ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) → Il-inv-fs (Il-fs {Γ = Γ} fs) ≡ fs
Il-inv-fs-Il-fs (leaf f) = refl
Il-inv-fs-Il-fs (node fs gs) = cong₂ node (Il-inv-fs-Il-fs fs) (Il-inv-fs-Il-fs gs)

⊗l-inv-fs-⊗l-fs : ∀ {Γ A B Φ} (fs : All (λ x → just A ∣ (B ∷ Γ) ++ proj₁ x ⊢li proj₂ x) Φ) → ⊗l-inv-fs (⊗l-fs {Γ = Γ} fs) ≡ fs
⊗l-inv-fs-⊗l-fs (leaf f) = refl
⊗l-inv-fs-⊗l-fs (node fs gs) = cong₂ node (⊗l-inv-fs-⊗l-fs fs) (⊗l-inv-fs-⊗l-fs gs)

∨l-inv-fs₁-∨l-fs : ∀ {Γ A B Φ} (fs : All (λ x → just A ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) (gs : All (λ x → just B ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → ∨l-inv-fs₁ (∨l-fs fs gs) ≡ fs
∨l-inv-fs₁-∨l-fs (leaf f) (leaf g) = refl
∨l-inv-fs₁-∨l-fs (node fs gs) (node hs ks) = cong₂ node (∨l-inv-fs₁-∨l-fs fs hs) (∨l-inv-fs₁-∨l-fs gs ks)

∨l-inv-fs₂-∨l-fs : ∀ {Γ A B Φ} (fs : All (λ x → just A ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) (gs : All (λ x → just B ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → ∨l-inv-fs₂ (∨l-fs fs gs) ≡ gs
∨l-inv-fs₂-∨l-fs (leaf f) (leaf g) = refl
∨l-inv-fs₂-∨l-fs (node fs gs) (node hs ks) = cong₂ node (∨l-inv-fs₂-∨l-fs fs hs) (∨l-inv-fs₂-∨l-fs gs ks)

gen⊗r-li-head : ∀ {S Γ Δ A B}
  (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (e : headAll fs ≡ f) (g : - ∣ Δ ⊢ri B)
  → gen⊗r-li A (headAll fs) fs refl g ≡ gen⊗r-li A f fs e g
gen⊗r-li-head f fs refl g = refl

gen⊗r-li-fs : ∀ {S Γ Δ A B}
  (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  (fs gs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  (e : headAll fs ≡ f) (e' : headAll gs ≡ f) → fs ≡ gs → (g : - ∣ Δ ⊢ri B)
  → gen⊗r-li A f fs e g ≡ gen⊗r-li A f gs e' g
gen⊗r-li-fs f fs .fs e e' refl g rewrite uip {p = e} {e'} = refl

gen⊗rpass-li : ∀ {Γ D Ξ A B} → (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (g : - ∣ Ξ ⊢ri B)
  → gen⊗r-li A (headAll (pass-fs fs)) (pass-fs fs) refl g ≡ f2li (pass (gen⊗r-li A (headAll fs) fs refl g))
gen⊗rpass-li {Γ} {D} {A = A} {B} fs g =
  trans (gen⊗r-li-head (f2li (pass (headAll fs))) (pass-fs fs) (headAll-map (λ f → f2li (pass f)) fs) g) aux
  where
  aux : gen⊗r-li A (f2li (pass (headAll fs))) (pass-fs fs) (headAll-map (λ f → f2li (pass f)) fs) g ≡ f2li (pass (gen⊗r-li A (headAll fs) fs refl g))
  aux rewrite check-focus-pass {D} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (pass f)) fs)) (headAll-map (λ f → f2li (pass f)) fs)} {refl} = refl

gen⊗r∧l₁-li : ∀ {Γ D E Ξ A B} → (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (g : - ∣ Ξ ⊢ri B)
  → gen⊗r-li A (headAll (∧l₁-fs {B = E} fs)) (∧l₁-fs {B = E} fs) refl g ≡ f2li (∧l₁ (gen⊗r-li A (headAll fs) fs refl g))
gen⊗r∧l₁-li {Γ} {D} {E} {A = A} {B} fs g =
  trans (gen⊗r-li-head (f2li (∧l₁ (headAll fs))) (∧l₁-fs {B = E} fs) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs) g) aux
  where
  aux : gen⊗r-li A (f2li (∧l₁ (headAll fs))) (∧l₁-fs {B = E} fs) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs) g ≡ f2li (∧l₁ (gen⊗r-li A (headAll fs) fs refl g))
  aux rewrite check-focus-∧l₁ {D} {E} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)} {refl} = refl

gen⊗r∧l₂-li : ∀ {Γ D E Ξ A B} → (fs : All (λ x → just E ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (g : - ∣ Ξ ⊢ri B)
  → gen⊗r-li A (headAll (∧l₂-fs {A = D} fs)) (∧l₂-fs {A = D} fs) refl g ≡ f2li (∧l₂ (gen⊗r-li A (headAll fs) fs refl g))
gen⊗r∧l₂-li {Γ} {D} {E} {A = A} {B} fs g =
  trans (gen⊗r-li-head (f2li (∧l₂ (headAll fs))) (∧l₂-fs {A = D} fs) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs) g) aux
  where
  aux : gen⊗r-li A (f2li (∧l₂ (headAll fs))) (∧l₂-fs {A = D} fs) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs) g ≡ f2li (∧l₂ (gen⊗r-li A (headAll fs) fs refl g))
  aux rewrite check-focus-∧l₂ {D} {E} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)} {refl} = refl

gen⊗r⊸l-li : ∀ {Γ Δ D E Ξ A B} → (h : - ∣ Γ ⊢ri D) (fs : All (λ x → just E ∣ Δ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (g : - ∣ Ξ ⊢ri B)
  → gen⊗r-li {Γ = Γ ++ Δ} A (headAll (⊸l-fs {Δ = Δ} h fs)) (⊸l-fs {Δ = Δ} h fs) refl g ≡ f2li (⊸l (++ass Γ) h (gen⊗r-li {Γ = Δ} A (headAll fs) fs refl g))
gen⊗r⊸l-li {Γ} {Δ} {D} {E} {A = A} {B} h fs g =
  trans (gen⊗r-li-head {Γ = Γ ++ Δ} (f2li (⊸l (++ass Γ) h (headAll fs))) (⊸l-fs {Δ = Δ} h fs) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs) g) aux
  where
  aux : gen⊗r-li {Γ = Γ ++ Δ} A (f2li (⊸l (++ass Γ) h (headAll fs))) (⊸l-fs {Δ = Δ} h fs) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs) g ≡ f2li (⊸l (++ass Γ) h (gen⊗r-li {Γ = Δ} A (headAll fs) fs refl g))
  aux rewrite check-focus-⊸l-all {D} {E} {Γ} {Δ} h fs | uip {p = trans (sym (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)} {refl} = refl

gen⊗rIl-li : ∀ {Γ A B Δ} (fs : All (λ x → - ∣ (Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (g : - ∣ Δ ⊢ri B)
  → gen⊗r-li A (headAll (Il-fs {Γ = Γ} fs)) (Il-fs {Γ = Γ} fs) refl g ≡ Il (gen⊗r-li A (headAll fs) fs refl g)
gen⊗rIl-li {Γ} {A = A} {B} fs g =
  trans (gen⊗r-li-head (Il (headAll fs)) (Il-fs {Γ = Γ} fs) (headAll-map Il fs) g)
    (cong Il (gen⊗r-li-fs (headAll fs) (Il-inv-fs (Il-fs {Γ = Γ} fs)) fs (trans (headAll-map Il-inv (Il-fs {Γ = Γ} fs)) (cong Il-inv (headAll-map Il fs))) refl (Il-inv-fs-Il-fs {Γ} fs) g))

gen⊗r⊗l-li : ∀ {Γ D E A B Δ} (fs : All (λ x → just D ∣ (E ∷ Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (g : - ∣ Δ ⊢ri B)
  → gen⊗r-li A (headAll (⊗l-fs {Γ = Γ} fs)) (⊗l-fs {Γ = Γ} fs) refl g ≡ ⊗l (gen⊗r-li A (headAll fs) fs refl g)
gen⊗r⊗l-li {Γ} {D} {E} {A = A} {B} fs g =
  trans (gen⊗r-li-head (⊗l (headAll fs)) (⊗l-fs {Γ = Γ} fs) (headAll-map ⊗l fs) g)
    (cong ⊗l (gen⊗r-li-fs (headAll fs) (⊗l-inv-fs (⊗l-fs {Γ = Γ} fs)) fs (trans (headAll-map ⊗l-inv (⊗l-fs {Γ = Γ} fs)) (cong ⊗l-inv (headAll-map ⊗l fs))) refl (⊗l-inv-fs-⊗l-fs {Γ} fs) g))

gen⊗r∨l-li : ∀ {Γ D E A B Δ} (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  (gs : All (λ x → just E ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (g : - ∣ Δ ⊢ri B)
  → gen⊗r-li A (headAll (∨l-fs fs gs)) (∨l-fs fs gs) refl g ≡ ∨l (gen⊗r-li A (headAll fs) fs refl g) (gen⊗r-li A (headAll gs) gs refl g)
gen⊗r∨l-li {Γ} {D} {E} {A} {B} fs gs g =
  trans (gen⊗r-li-head (∨l (headAll fs) (headAll gs)) (∨l-fs fs gs) (headAll-map2 ∨l fs gs) g)
    (cong₂ ∨l
      (gen⊗r-li-fs (headAll fs) (∨l-inv-fs₁ (∨l-fs fs gs)) fs (trans (headAll-map ∨l-inv₁ (∨l-fs fs gs)) (cong ∨l-inv₁ (headAll-map2 ∨l fs gs))) refl (∨l-inv-fs₁-∨l-fs fs gs) g)
      (gen⊗r-li-fs (headAll gs) (∨l-inv-fs₂ (∨l-fs fs gs)) gs (trans (headAll-map ∨l-inv₂ (∨l-fs fs gs)) (cong ∨l-inv₂ (headAll-map2 ∨l fs gs))) refl (∨l-inv-fs₂-∨l-fs fs gs) g))

gen∨r₁-li-head : ∀ {S Γ A B}
  (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (e : headAll fs ≡ f)
  → gen∨r₁-li {B = B} A (headAll fs) fs refl ≡ gen∨r₁-li {B = B} A f fs e
gen∨r₁-li-head f fs refl = refl

gen∨r₁-li-fs : ∀ {S Γ A B}
  (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  (fs gs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  (e : headAll fs ≡ f) (e' : headAll gs ≡ f) → fs ≡ gs
  → gen∨r₁-li {B = B} A f fs e ≡ gen∨r₁-li {B = B} A f gs e'
gen∨r₁-li-fs f fs .fs e e' refl rewrite uip {p = e} {e'} = refl

gen∨r₁pass-li : ∀ {Γ D  A B} → (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → gen∨r₁-li {B = B} A (headAll (pass-fs fs)) (pass-fs fs) refl ≡ f2li (pass (gen∨r₁-li {B = B} A (headAll fs) fs refl))
gen∨r₁pass-li {Γ} {D} {A = A} {B} fs =
  trans (gen∨r₁-li-head (f2li (pass (headAll fs))) (pass-fs fs) (headAll-map (λ f → f2li (pass f)) fs)) aux
  where
  aux : gen∨r₁-li {B = B} A (f2li (pass (headAll fs))) (pass-fs fs) (headAll-map (λ f → f2li (pass f)) fs) ≡ f2li (pass (gen∨r₁-li {B = B} A (headAll fs) fs refl))
  aux rewrite check-focus-pass {D} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (pass f)) fs)) (headAll-map (λ f → f2li (pass f)) fs)} {refl} = refl

gen∨r₁∧l₁-li : ∀ {Γ D E  A B} → (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → gen∨r₁-li {B = B} A (headAll (∧l₁-fs {B = E} fs)) (∧l₁-fs {B = E} fs) refl ≡ f2li (∧l₁ (gen∨r₁-li {B = B} A (headAll fs) fs refl))
gen∨r₁∧l₁-li {Γ} {D} {E} {A = A} {B} fs =
  trans (gen∨r₁-li-head (f2li (∧l₁ (headAll fs))) (∧l₁-fs {B = E} fs) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)) aux
  where
  aux : gen∨r₁-li {B = B} A (f2li (∧l₁ (headAll fs))) (∧l₁-fs {B = E} fs) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs) ≡ f2li (∧l₁ (gen∨r₁-li {B = B} A (headAll fs) fs refl))
  aux rewrite check-focus-∧l₁ {D} {E} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)} {refl} = refl

gen∨r₁∧l₂-li : ∀ {Γ D E  A B} → (fs : All (λ x → just E ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → gen∨r₁-li {B = B} A (headAll (∧l₂-fs {A = D} fs)) (∧l₂-fs {A = D} fs) refl ≡ f2li (∧l₂ (gen∨r₁-li {B = B} A (headAll fs) fs refl))
gen∨r₁∧l₂-li {Γ} {D} {E} {A = A} {B} fs =
  trans (gen∨r₁-li-head (f2li (∧l₂ (headAll fs))) (∧l₂-fs {A = D} fs) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)) aux
  where
  aux : gen∨r₁-li {B = B} A (f2li (∧l₂ (headAll fs))) (∧l₂-fs {A = D} fs) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs) ≡ f2li (∧l₂ (gen∨r₁-li {B = B} A (headAll fs) fs refl))
  aux rewrite check-focus-∧l₂ {D} {E} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)} {refl} = refl

gen∨r₁⊸l-li : ∀ {Γ Δ D E  A B} → (h : - ∣ Γ ⊢ri D) (fs : All (λ x → just E ∣ Δ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → gen∨r₁-li {Γ = Γ ++ Δ} {B = B} A (headAll (⊸l-fs {Δ = Δ} h fs)) (⊸l-fs {Δ = Δ} h fs) refl ≡ f2li (⊸l refl h (gen∨r₁-li {Γ = Δ} {B = B} A (headAll fs) fs refl))
gen∨r₁⊸l-li {Γ} {Δ} {D} {E} {A = A} {B} h fs =
  trans (gen∨r₁-li-head {Γ = Γ ++ Δ} (f2li (⊸l (++ass Γ) h (headAll fs))) (⊸l-fs {Δ = Δ} h fs) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)) aux
  where
  aux : gen∨r₁-li {Γ = Γ ++ Δ} {B = B} A (f2li (⊸l (++ass Γ) h (headAll fs))) (⊸l-fs {Δ = Δ} h fs) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs) ≡ f2li (⊸l refl h (gen∨r₁-li {Γ = Δ} {B = B} A (headAll fs) fs refl))
  aux rewrite check-focus-⊸l-all {D} {E} {Γ} {Δ} h fs | uip {p = trans (sym (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)} {refl} = refl

gen∨r₁Il-li : ∀ {Γ A B} (fs : All (λ x → - ∣ (Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → gen∨r₁-li {B = B} A (headAll (Il-fs {Γ = Γ} fs)) (Il-fs {Γ = Γ} fs) refl ≡ Il (gen∨r₁-li {B = B} A (headAll fs) fs refl)
gen∨r₁Il-li {Γ} {A = A} {B} fs =
  trans (gen∨r₁-li-head (Il (headAll fs)) (Il-fs {Γ = Γ} fs) (headAll-map Il fs))
    (cong Il (gen∨r₁-li-fs (headAll fs) (Il-inv-fs (Il-fs {Γ = Γ} fs)) fs (trans (headAll-map Il-inv (Il-fs {Γ = Γ} fs)) (cong Il-inv (headAll-map Il fs))) refl (Il-inv-fs-Il-fs {Γ} fs)))

gen∨r₁⊗l-li : ∀ {Γ D E A B} (fs : All (λ x → just D ∣ (E ∷ Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → gen∨r₁-li {B = B} A (headAll (⊗l-fs {Γ = Γ} fs)) (⊗l-fs {Γ = Γ} fs) refl ≡ ⊗l (gen∨r₁-li {B = B} A (headAll fs) fs refl)
gen∨r₁⊗l-li {Γ} {D} {E} {A = A} {B} fs =
  trans (gen∨r₁-li-head (⊗l (headAll fs)) (⊗l-fs {Γ = Γ} fs) (headAll-map ⊗l fs))
    (cong ⊗l (gen∨r₁-li-fs (headAll fs) (⊗l-inv-fs (⊗l-fs {Γ = Γ} fs)) fs (trans (headAll-map ⊗l-inv (⊗l-fs {Γ = Γ} fs)) (cong ⊗l-inv (headAll-map ⊗l fs))) refl (⊗l-inv-fs-⊗l-fs {Γ} fs)))

gen∨r₁∨l-li : ∀ {Γ D E A B} (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  (gs : All (λ x → just E ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → gen∨r₁-li {B = B} A (headAll (∨l-fs fs gs)) (∨l-fs fs gs) refl ≡ ∨l (gen∨r₁-li {B = B} A (headAll fs) fs refl) (gen∨r₁-li {B = B} A (headAll gs) gs refl)
gen∨r₁∨l-li {Γ} {D} {E} {A} {B} fs gs =
  trans (gen∨r₁-li-head (∨l (headAll fs) (headAll gs)) (∨l-fs fs gs) (headAll-map2 ∨l fs gs))
    (cong₂ ∨l
      (gen∨r₁-li-fs (headAll fs) (∨l-inv-fs₁ (∨l-fs fs gs)) fs (trans (headAll-map ∨l-inv₁ (∨l-fs fs gs)) (cong ∨l-inv₁ (headAll-map2 ∨l fs gs))) refl (∨l-inv-fs₁-∨l-fs fs gs))
      (gen∨r₁-li-fs (headAll gs) (∨l-inv-fs₂ (∨l-fs fs gs)) gs (trans (headAll-map ∨l-inv₂ (∨l-fs fs gs)) (cong ∨l-inv₂ (headAll-map2 ∨l fs gs))) refl (∨l-inv-fs₂-∨l-fs fs gs)))

gen∨r₂-li-head : ∀ {S Γ A B}
  (f : S ∣ Γ ++ proj₁ (head (impconj [] B)) ⊢li proj₂ (head (impconj [] B)))
  (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B)) (e : headAll fs ≡ f)
  → gen∨r₂-li {A = A} B (headAll fs) fs refl ≡ gen∨r₂-li {A = A} B f fs e
gen∨r₂-li-head f fs refl = refl

gen∨r₂-li-fs : ∀ {S Γ A B}
  (f : S ∣ Γ ++ proj₁ (head (impconj [] B)) ⊢li proj₂ (head (impconj [] B)))
  (fs gs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  (e : headAll fs ≡ f) (e' : headAll gs ≡ f) → fs ≡ gs
  → gen∨r₂-li {A = A} B f fs e ≡ gen∨r₂-li {A = A} B f gs e'
gen∨r₂-li-fs f fs .fs e e' refl rewrite uip {p = e} {e'} = refl

gen∨r₂pass-li : ∀ {Γ D  A B} → (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → gen∨r₂-li {A = A} B (headAll (pass-fs fs)) (pass-fs fs) refl ≡ f2li (pass (gen∨r₂-li {A = A} B (headAll fs) fs refl))
gen∨r₂pass-li {Γ} {D} {A = A} {B} fs =
  trans (gen∨r₂-li-head (f2li (pass (headAll fs))) (pass-fs fs) (headAll-map (λ f → f2li (pass f)) fs)) aux
  where
  aux : gen∨r₂-li {A = A} B (f2li (pass (headAll fs))) (pass-fs fs) (headAll-map (λ f → f2li (pass f)) fs) ≡ f2li (pass (gen∨r₂-li {A = A} B (headAll fs) fs refl))
  aux rewrite check-focus-pass {D} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (pass f)) fs)) (headAll-map (λ f → f2li (pass f)) fs)} {refl} = refl

gen∨r₂∧l₁-li : ∀ {Γ D E  A B} → (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → gen∨r₂-li {A = A} B (headAll (∧l₁-fs {B = E} fs)) (∧l₁-fs {B = E} fs) refl ≡ f2li (∧l₁ (gen∨r₂-li {A = A} B (headAll fs) fs refl))
gen∨r₂∧l₁-li {Γ} {D} {E} {A = A} {B} fs =
  trans (gen∨r₂-li-head (f2li (∧l₁ (headAll fs))) (∧l₁-fs {B = E} fs) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)) aux
  where
  aux : gen∨r₂-li {A = A} B (f2li (∧l₁ (headAll fs))) (∧l₁-fs {B = E} fs) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs) ≡ f2li (∧l₁ (gen∨r₂-li {A = A} B (headAll fs) fs refl))
  aux rewrite check-focus-∧l₁ {D} {E} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)) (headAll-map (λ f → f2li (∧l₁ {B = E} f)) fs)} {refl} = refl

gen∨r₂∧l₂-li : ∀ {Γ D E  A B} → (fs : All (λ x → just E ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → gen∨r₂-li {A = A} B (headAll (∧l₂-fs {A = D} fs)) (∧l₂-fs {A = D} fs) refl ≡ f2li (∧l₂ (gen∨r₂-li {A = A} B (headAll fs) fs refl))
gen∨r₂∧l₂-li {Γ} {D} {E} {A = A} {B} fs =
  trans (gen∨r₂-li-head (f2li (∧l₂ (headAll fs))) (∧l₂-fs {A = D} fs) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)) aux
  where
  aux : gen∨r₂-li {A = A} B (f2li (∧l₂ (headAll fs))) (∧l₂-fs {A = D} fs) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs) ≡ f2li (∧l₂ (gen∨r₂-li {A = A} B (headAll fs) fs refl))
  aux rewrite check-focus-∧l₂ {D} {E} {Γ} fs | uip {p = trans (sym (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)) (headAll-map (λ f → f2li (∧l₂ {A = D} f)) fs)} {refl} = refl

gen∨r₂⊸l-li : ∀ {Γ Δ D E  A B} → (h : - ∣ Γ ⊢ri D) (fs : All (λ x → just E ∣ Δ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → gen∨r₂-li {Γ = Γ ++ Δ} {A = A} B (headAll (⊸l-fs {Δ = Δ} h fs)) (⊸l-fs {Δ = Δ} h fs) refl ≡ f2li (⊸l refl h (gen∨r₂-li {Γ = Δ} {A = A} B (headAll fs) fs refl))
gen∨r₂⊸l-li {Γ} {Δ} {D} {E} {A = A} {B} h fs =
  trans (gen∨r₂-li-head {Γ = Γ ++ Δ} (f2li (⊸l (++ass Γ) h (headAll fs))) (⊸l-fs {Δ = Δ} h fs) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)) aux
  where
  aux : gen∨r₂-li {Γ = Γ ++ Δ} {A = A} B (f2li (⊸l (++ass Γ) h (headAll fs))) (⊸l-fs {Δ = Δ} h fs) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs) ≡ f2li (⊸l refl h (gen∨r₂-li {Γ = Δ} {A = A} B (headAll fs) fs refl))
  aux rewrite check-focus-⊸l-all {D} {E} {Γ} {Δ} h fs | uip {p = trans (sym (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)) (headAll-map (λ {x} f → f2li (⊸l (++ass Γ {Δ} {proj₁ x}) h f)) fs)} {refl} = refl

gen∨r₂Il-li : ∀ {Γ A B} (fs : All (λ x → - ∣ (Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → gen∨r₂-li {A = A} B (headAll (Il-fs {Γ = Γ} fs)) (Il-fs {Γ = Γ} fs) refl ≡ Il (gen∨r₂-li {A = A} B (headAll fs) fs refl)
gen∨r₂Il-li {Γ} {A = A} {B} fs =
  trans (gen∨r₂-li-head (Il (headAll fs)) (Il-fs {Γ = Γ} fs) (headAll-map Il fs))
    (cong Il (gen∨r₂-li-fs (headAll fs) (Il-inv-fs (Il-fs {Γ = Γ} fs)) fs (trans (headAll-map Il-inv (Il-fs {Γ = Γ} fs)) (cong Il-inv (headAll-map Il fs))) refl (Il-inv-fs-Il-fs {Γ} fs)))

gen∨r₂⊗l-li : ∀ {Γ D E A B} (fs : All (λ x → just D ∣ (E ∷ Γ) ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → gen∨r₂-li {A = A} B (headAll (⊗l-fs {Γ = Γ} fs)) (⊗l-fs {Γ = Γ} fs) refl ≡ ⊗l (gen∨r₂-li {A = A} B (headAll fs) fs refl)
gen∨r₂⊗l-li {Γ} {D} {E} {A = A} {B} fs =
  trans (gen∨r₂-li-head (⊗l (headAll fs)) (⊗l-fs {Γ = Γ} fs) (headAll-map ⊗l fs))
    (cong ⊗l (gen∨r₂-li-fs (headAll fs) (⊗l-inv-fs (⊗l-fs {Γ = Γ} fs)) fs (trans (headAll-map ⊗l-inv (⊗l-fs {Γ = Γ} fs)) (cong ⊗l-inv (headAll-map ⊗l fs))) refl (⊗l-inv-fs-⊗l-fs {Γ} fs)))

gen∨r₂∨l-li : ∀ {Γ D E A B} (fs : All (λ x → just D ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  (gs : All (λ x → just E ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → gen∨r₂-li {A = A} B (headAll (∨l-fs fs gs)) (∨l-fs fs gs) refl ≡ ∨l (gen∨r₂-li {A = A} B (headAll fs) fs refl) (gen∨r₂-li {A = A} B (headAll gs) gs refl)
gen∨r₂∨l-li {Γ} {D} {E} {A} {B} fs gs =
  trans (gen∨r₂-li-head (∨l (headAll fs) (headAll gs)) (∨l-fs fs gs) (headAll-map2 ∨l fs gs))
    (cong₂ ∨l
      (gen∨r₂-li-fs (headAll fs) (∨l-inv-fs₁ (∨l-fs fs gs)) fs (trans (headAll-map ∨l-inv₁ (∨l-fs fs gs)) (cong ∨l-inv₁ (headAll-map2 ∨l fs gs))) refl (∨l-inv-fs₁-∨l-fs fs gs))
      (gen∨r₂-li-fs (headAll gs) (∨l-inv-fs₂ (∨l-fs fs gs)) gs (trans (headAll-map ∨l-inv₂ (∨l-fs fs gs)) (cong ∨l-inv₂ (headAll-map2 ∨l fs gs))) refl (∨l-inv-fs₂-∨l-fs fs gs)))

⊗rpass-ri : ∀ {Γ Δ A B D} (f : just D ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (pass-ri f) g ≡ pass-ri (⊗r-ri f g)
⊗rpass-ri {Γ} {A = A} {D = D} f g rewrite pass-ri-inv {Γ} {D} f = cong li2ri (gen⊗rpass-li (ri-inv {Γ = Γ} f) g)

⊗rIl-ri : ∀ {Γ Δ A B} (f : (-) ∣ (Γ) ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (Il-ri f) g ≡ Il-ri (⊗r-ri f g)
⊗rIl-ri {Γ} {A = A} f g rewrite Il-ri-inv {Γ} f = cong li2ri (gen⊗rIl-li (ri-inv {Γ = Γ} f) g)

⊗r⊗l-ri : ∀ {Γ Δ A B D E} (f : (just D) ∣ (E ∷ Γ) ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (⊗l-ri f) g ≡ ⊗l-ri (⊗r-ri f g)
⊗r⊗l-ri {Γ} {A = A} {D = D} {E = E} f g rewrite ⊗l-ri-inv {Γ} {D} {E} f = cong li2ri (gen⊗r⊗l-li (ri-inv {Γ = E ∷ Γ} f) g)

⊗r∧l₁-ri : ∀ {Γ Δ A B D E} (f : (just D) ∣ (Γ) ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (∧l₁-ri {B = E} f) g ≡ ∧l₁-ri {B = E} (⊗r-ri f g)
⊗r∧l₁-ri {Γ} {A = A} {D = D} {E = E} f g rewrite ∧l₁-ri-inv {Γ} {D} {E} f = cong li2ri (gen⊗r∧l₁-li (ri-inv {Γ = Γ} f) g)

⊗r∧l₂-ri : ∀ {Γ Δ A B D E} (f : (just E) ∣ (Γ) ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (∧l₂-ri {A = D} f) g ≡ ∧l₂-ri {A = D} (⊗r-ri f g)
⊗r∧l₂-ri {Γ} {A = A} {D = D} {E = E} f g rewrite ∧l₂-ri-inv {Γ} {D} {E} f = cong li2ri (gen⊗r∧l₂-li (ri-inv {Γ = Γ} f) g)

⊗r⊸l-ri : ∀ {Γ Δ Λ A B D E} (h : - ∣ Γ ⊢ri D) (f : just E ∣ Δ ⊢ri A) (g : - ∣ Λ ⊢ri B)
  → ⊗r-ri (⊸l-ri h f) g ≡ subst-ri (sym (++ass Γ)) (⊸l-ri h (⊗r-ri f g))
⊗r⊸l-ri {Γ} {Δ} {A = A} {D = D} {E} h f g rewrite ⊸l-ri-inv {Γ} {Δ} {D} {E} h f = trans (cong li2ri (gen⊗r⊸l-li h (ri-inv {Γ = Δ} f) g)) (sym (subst-ri-f2li-⊸l (++ass Γ) h (gen⊗r-li A (headAll (ri-inv f)) (ri-inv f) refl g)))

⊗r∨l-ri : ∀ {Γ Δ A B D E} (f : just D ∣ Γ ⊢ri A) (f' : just E ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (∨l-ri f f') g ≡ ∨l-ri (⊗r-ri f g) (⊗r-ri f' g)
⊗r∨l-ri {Γ} {D = D} {E} f f' g rewrite ∨l-ri-inv {Γ} f f' = cong li2ri (gen⊗r∨l-li (ri-inv {Γ = Γ} f) (ri-inv {Γ = Γ} f') g)

∨r₁pass-ri : ∀ {Γ A B D} (f : (just D) ∣ (Γ) ⊢ri A)
  → ∨r₁-ri {B = B} (pass-ri f) ≡ pass-ri (∨r₁-ri {B = B} f)
∨r₁pass-ri {Γ} {A = A} {D = D} f rewrite pass-ri-inv {Γ} {D} f = cong li2ri (gen∨r₁pass-li (ri-inv {Γ = Γ} f))

∨r₁Il-ri : ∀ {Γ A B} (f : (-) ∣ (Γ) ⊢ri A)
  → ∨r₁-ri {B = B} (Il-ri f) ≡ Il-ri (∨r₁-ri {B = B} f)
∨r₁Il-ri {Γ} {A = A} f rewrite Il-ri-inv {Γ} f = cong li2ri (gen∨r₁Il-li (ri-inv {Γ = Γ} f))

∨r₁⊗l-ri : ∀ {Γ A B D E} (f : (just D) ∣ (E ∷ Γ) ⊢ri A)
  → ∨r₁-ri {B = B} (⊗l-ri f) ≡ ⊗l-ri (∨r₁-ri {B = B} f)
∨r₁⊗l-ri {Γ} {A = A} {D = D} {E = E} f rewrite ⊗l-ri-inv {Γ} {D} {E} f = cong li2ri (gen∨r₁⊗l-li (ri-inv {Γ = E ∷ Γ} f))

∨r₁∧l₁-ri : ∀ {Γ A B D E} (f : (just D) ∣ (Γ) ⊢ri A)
  → ∨r₁-ri {B = B} (∧l₁-ri {B = E} f) ≡ ∧l₁-ri {B = E} (∨r₁-ri {B = B} f)
∨r₁∧l₁-ri {Γ} {A = A} {D = D} {E = E} f rewrite ∧l₁-ri-inv {Γ} {D} {E} f = cong li2ri (gen∨r₁∧l₁-li (ri-inv {Γ = Γ} f))

∨r₁∧l₂-ri : ∀ {Γ A B D E} (f : (just E) ∣ (Γ) ⊢ri A)
  → ∨r₁-ri {B = B} (∧l₂-ri {A = D} f) ≡ ∧l₂-ri {A = D} (∨r₁-ri {B = B} f)
∨r₁∧l₂-ri {Γ} {A = A} {D = D} {E = E} f rewrite ∧l₂-ri-inv {Γ} {D} {E} f = cong li2ri (gen∨r₁∧l₂-li (ri-inv {Γ = Γ} f))

∨r₁⊸l-ri : ∀ {Γ Δ A B D E} (h : - ∣ Γ ⊢ri D) (f : just E ∣ Δ ⊢ri A)
  → ∨r₁-ri {B = B} (⊸l-ri h f) ≡ ⊸l-ri h (∨r₁-ri {B = B} f)
∨r₁⊸l-ri {Γ} {Δ} {A = A} {D = D} {E} h f rewrite ⊸l-ri-inv {Γ} {Δ} {D} {E} h f = cong li2ri (gen∨r₁⊸l-li h (ri-inv {Γ = Δ} f))

∨r₁∨l-ri : ∀ {Γ A B D E} (f : just D ∣ Γ ⊢ri A) (f' : just E ∣ Γ ⊢ri A)
  → ∨r₁-ri {B = B} (∨l-ri f f') ≡ ∨l-ri (∨r₁-ri {B = B} f) (∨r₁-ri {B = B} f')
∨r₁∨l-ri {Γ} {D = D} {E} f f' rewrite ∨l-ri-inv {Γ} f f' = cong li2ri (gen∨r₁∨l-li (ri-inv {Γ = Γ} f) (ri-inv {Γ = Γ} f'))

∨r₂pass-ri : ∀ {Γ A B D} (f : (just D) ∣ (Γ) ⊢ri B)
  → ∨r₂-ri {A = A} (pass-ri f) ≡ pass-ri (∨r₂-ri {A = A} f)
∨r₂pass-ri {Γ} {B = B} {D = D} f rewrite pass-ri-inv {Γ} {D} f = cong li2ri (gen∨r₂pass-li (ri-inv {Γ = Γ} f))

∨r₂Il-ri : ∀ {Γ A B} (f : (-) ∣ (Γ) ⊢ri B)
  → ∨r₂-ri {A = A} (Il-ri f) ≡ Il-ri (∨r₂-ri {A = A} f)
∨r₂Il-ri {Γ} {B = B} f rewrite Il-ri-inv {Γ} f = cong li2ri (gen∨r₂Il-li (ri-inv {Γ = Γ} f))

∨r₂⊗l-ri : ∀ {Γ A B D E} (f : (just D) ∣ (E ∷ Γ) ⊢ri B)
  → ∨r₂-ri {A = A} (⊗l-ri f) ≡ ⊗l-ri (∨r₂-ri {A = A} f)
∨r₂⊗l-ri {Γ} {B = B} {D = D} {E = E} f rewrite ⊗l-ri-inv {Γ} {D} {E} f = cong li2ri (gen∨r₂⊗l-li (ri-inv {Γ = E ∷ Γ} f))

∨r₂∧l₁-ri : ∀ {Γ A B D E} (f : (just D) ∣ (Γ) ⊢ri B)
  → ∨r₂-ri {A = A} (∧l₁-ri {B = E} f) ≡ ∧l₁-ri {B = E} (∨r₂-ri {A = A} f)
∨r₂∧l₁-ri {Γ} {B = B} {D = D} {E = E} f rewrite ∧l₁-ri-inv {Γ} {D} {E} f = cong li2ri (gen∨r₂∧l₁-li (ri-inv {Γ = Γ} f))

∨r₂∧l₂-ri : ∀ {Γ A B D E} (f : (just E) ∣ (Γ) ⊢ri B)
  → ∨r₂-ri {A = A} (∧l₂-ri {A = D} f) ≡ ∧l₂-ri {A = D} (∨r₂-ri {A = A} f)
∨r₂∧l₂-ri {Γ} {B = B} {D = D} {E = E} f rewrite ∧l₂-ri-inv {Γ} {D} {E} f = cong li2ri (gen∨r₂∧l₂-li (ri-inv {Γ = Γ} f))

∨r₂⊸l-ri : ∀ {Γ Δ A B D E} (h : - ∣ Γ ⊢ri D) (f : just E ∣ Δ ⊢ri B)
  → ∨r₂-ri {A = A} (⊸l-ri h f) ≡ ⊸l-ri h (∨r₂-ri {A = A} f)
∨r₂⊸l-ri {Γ} {Δ} {B = B} {D = D} {E} h f rewrite ⊸l-ri-inv {Γ} {Δ} {D} {E} h f = cong li2ri (gen∨r₂⊸l-li h (ri-inv {Γ = Δ} f))

∨r₂∨l-ri : ∀ {Γ A B D E} (f : just D ∣ Γ ⊢ri B) (f' : just E ∣ Γ ⊢ri B)
  → ∨r₂-ri {A = A} (∨l-ri f f') ≡ ∨l-ri (∨r₂-ri {A = A} f) (∨r₂-ri {A = A} f')
∨r₂∨l-ri {Γ} {D = D} {E} f f' rewrite ∨l-ri-inv {Γ} f f' = cong li2ri (gen∨r₂∨l-li (ri-inv {Γ = Γ} f) (ri-inv {Γ = Γ} f'))

focus-subst : ∀ {S Γ Δ A} (p : Γ ≡ Δ) (f : S ∣ Γ ⊢ A) → focus (subst-cxt p f) ≡ subst-ri p (focus f)
focus-subst refl f = refl

eqfocus : ∀ {S Γ A} {f g : S ∣ Γ ⊢ A} → f ≗ g → focus f ≡ focus g
eqfocus refl = refl
eqfocus (~ p) = sym (eqfocus p)
eqfocus (p ∙ q) = trans (eqfocus p) (eqfocus q)
eqfocus (pass p) = cong pass-ri (eqfocus p)
eqfocus (Il p) = cong Il-ri (eqfocus p)
eqfocus (⊗l p) = cong ⊗l-ri (eqfocus p)
eqfocus (⊗r p q) = cong₂ ⊗r-ri (eqfocus p) (eqfocus q)
eqfocus (⊸r p) = cong ⊸r (eqfocus p)
eqfocus (⊸l p q) = cong₂ ⊸l-ri (eqfocus p) (eqfocus q)
eqfocus (∧r p q) = cong₂ ∧r (eqfocus p) (eqfocus q)
eqfocus (∧l₁ p) = cong ∧l₁-ri (eqfocus p)
eqfocus (∧l₂ p) = cong ∧l₂-ri (eqfocus p)
eqfocus (∨r₁ p) = cong ∨r₁-ri (eqfocus p)
eqfocus (∨r₂ p) = cong ∨r₂-ri (eqfocus p)
eqfocus (∨l p q) = cong₂ ∨l-ri (eqfocus p) (eqfocus q)
eqfocus axI = refl
eqfocus ax⊗ = refl
eqfocus ax⊸ = refl
eqfocus ax∧ = refl
eqfocus ax∨ = refl
eqfocus (⊗rpass {f = f} {g}) = ⊗rpass-ri (focus f) (focus g)
eqfocus (⊗rIl {f = f} {g}) = ⊗rIl-ri (focus f) (focus g)
eqfocus (⊗r⊗l {f = f} {g}) = ⊗r⊗l-ri (focus f) (focus g)
eqfocus (⊗r∧l₁ {f = f} {g}) = ⊗r∧l₁-ri (focus f) (focus g)
eqfocus (⊗r∧l₂ {f = f} {g}) = ⊗r∧l₂-ri (focus f) (focus g)
eqfocus (⊗r∨l {f = f} {f'} {g}) = ⊗r∨l-ri (focus f) (focus f') (focus g)
eqfocus (⊗r⊸l {Γ} {f = f} {g} {h}) = trans (⊗r⊸l-ri (focus f) (focus g) (focus h)) (sym (focus-subst (sym (++ass Γ)) (⊸l f (⊗r g h))))
eqfocus ∧rpass = refl
eqfocus ∧rIl = refl
eqfocus ∧r⊗l = refl
eqfocus ∧r∧l₁ = refl
eqfocus ∧r∧l₂ = refl
eqfocus ∧r∨l = refl
eqfocus ∧r⊸l = refl
eqfocus (∨r₁pass {f = f}) = ∨r₁pass-ri (focus f)
eqfocus (∨r₁Il {f = f}) = ∨r₁Il-ri (focus f)
eqfocus (∨r₁⊗l {f = f}) = ∨r₁⊗l-ri (focus f)
eqfocus (∨r₁∧l₁ {f = f}) = ∨r₁∧l₁-ri (focus f)
eqfocus (∨r₁∧l₂ {f = f}) = ∨r₁∧l₂-ri (focus f)
eqfocus (∨r₁∨l {f = f} {g}) = ∨r₁∨l-ri (focus f) (focus g)
eqfocus (∨r₁⊸l {f = f} {g}) = ∨r₁⊸l-ri (focus f) (focus g)
eqfocus (∨r₂pass {f = f}) = ∨r₂pass-ri (focus f)
eqfocus (∨r₂Il {f = f}) = ∨r₂Il-ri (focus f)
eqfocus (∨r₂⊗l {f = f}) = ∨r₂⊗l-ri (focus f)
eqfocus (∨r₂∧l₁ {f = f}) = ∨r₂∧l₁-ri (focus f)
eqfocus (∨r₂∧l₂ {f = f}) = ∨r₂∧l₂-ri (focus f)
eqfocus (∨r₂∨l {f = f} {g}) = ∨r₂∨l-ri (focus f) (focus g)
eqfocus (∨r₂⊸l {f = f} {g}) = ∨r₂⊸l-ri (focus f) (focus g)
eqfocus ⊸rpass = refl
eqfocus ⊸rIl = refl
eqfocus ⊸r⊗l = refl
eqfocus (⊸r⊸l {Γ} {f = f} {g}) = cong ⊸r (focus-subst (sym (++ass Γ)) (⊸l f g))
eqfocus ⊸r∧l₁ = refl
eqfocus ⊸r∧l₂ = refl
eqfocus ⊸r∨l = refl
