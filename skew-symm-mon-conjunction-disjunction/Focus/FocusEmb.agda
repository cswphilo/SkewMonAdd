{-# OPTIONS --safe #-}

module Focus.FocusEmb (At : Set) where

open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
open import Focus.Tags
open import Focus.FocusedCalc At
open import Focus.Maps At

-- Valid trees have no common left choice to commute outwards.
check-focus-ok : ∀ {S Γ Φ} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ)
  (ok : isOK (tags-fs S fs)) → check-focus {S} fs ≡ caseok ok
check-focus-ok {S} fs ok with check-focus {S} fs
... | case1 (all∧l₁ {B = B} gs refl refl) =
  ⊥-elim (notOK-onlyC₁ (tags-fs _ (f2li-fs (∧l₁-f-fs {B = B} gs))) (tags-onlyC₁ gs) ok)
... | case2 (all∧l₂ {A = A} gs refl refl) =
  ⊥-elim (notOK-onlyC₂ (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} gs))) (tags-onlyC₂ gs) ok)
... | casepass (allPass p gs refl refl) =
  ⊥-elim (notOK-onlyP (pick-index p) (tags-fs _ (f2li-fs (pass-f-fs p gs))) (tags-onlyP p gs) ok)
... | caseok ok' = cong caseok (isProp-isOK (tags-fs S fs))

-- Valid right introductions are already in normal form.
-- check-focus-ok excludes commuting a shared left rule; uniqueness of isOK
-- witnesses identifies the reconstructed side condition with the original one.
⊗r-li-eq : (S : Irr) {Γ Δ Ξ : Cxt} (v : LView (irr S) Γ) {A B : Fma} (fs : All (λ C → irr S ∣ Γ ⊢li C) (toTree A)) (p : Part Γ Δ Ξ) (g : - ∣ Δ ⊢ri B)
  → (ok : isOK (tags-ri S (∧r*-ri A fs)))
  → ⊗r-li v fs p g ≡ f2li (⊗r p (∧r*-ri A fs) g ok)
⊗r-li-eq (just (` X) , _) atom fs p g ok = trans
  (cong (λ ch → f2li (⊗r-li-irr atom fs ch p g))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (⊗req p refl refl))
⊗r-li-eq ( - , _) empty fs p g ok = trans
  (cong (λ ch → f2li (⊗r-li-irr empty fs ch p g))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (⊗req p refl refl))
⊗r-li-eq ( - , _) (pass v) fs p g ok = trans
  (cong (λ ch → f2li (⊗r-li-irr (pass v) fs ch p g))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (⊗req p refl refl))
⊗r-li-eq (just (D ∧ E) , _) (∧l v w) fs p g ok = trans
  (cong (λ ch → f2li (⊗r-li-irr (∧l v w) fs ch p g))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (⊗req p refl refl))

⊗r-ri-eq : (S : Irr) {Γ Δ Ξ : Cxt} {A B : Fma} (f : irr S ∣ Γ ⊢ri A) (p : Part Γ Δ Ξ) (g : - ∣ Δ ⊢ri B) (ok : isOK (tags-ri S f))
  → ⊗r-ri p f g ≡ li2ri (f2li (⊗r p f g ok))
⊗r-ri-eq S {Γ} f p g ok = cong li2ri
  (trans (⊗r-li-eq S (view-ant (irr S) Γ) (∧r*-ri-inv f) p g
            (subst (λ f → isOK (tags-ri S f)) (sym (∧r*∧r*-ri-inv f)) ok))
         (cong f2li (⊗req p (∧r*∧r*-ri-inv f) refl)))

∨r₁-li-eq : (S : Irr) {Γ : Cxt} (v : LView (irr S) Γ) {A B : Fma} (fs : All (λ C → irr S ∣ Γ ⊢li C) (toTree A))
  → (ok : isOK (tags-ri S (∧r*-ri A fs)))
  → ∨r₁-li v {B = B} fs ≡ f2li (∨r₁ (∧r*-ri A fs) ok)
∨r₁-li-eq (just (` X) , _) atom fs ok = trans
  (cong (λ ch → f2li (∨r₁-li-irr atom fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₁eq refl))
∨r₁-li-eq ( - , _) empty fs ok = trans
  (cong (λ ch → f2li (∨r₁-li-irr empty fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₁eq refl))
∨r₁-li-eq ( - , _) (pass v) fs ok = trans
  (cong (λ ch → f2li (∨r₁-li-irr (pass v) fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₁eq refl))
∨r₁-li-eq (just (D ∧ E) , _) (∧l v w) fs ok = trans
  (cong (λ ch → f2li (∨r₁-li-irr (∧l v w) fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₁eq refl))

∨r₁-ri-eq : (S : Irr) {Γ : Cxt} {A B : Fma} (f : irr S ∣ Γ ⊢ri A) (ok : isOK (tags-ri S f))
  → ∨r₁-ri {B = B} f ≡ li2ri (f2li (∨r₁ f ok))
∨r₁-ri-eq S {Γ} f ok = cong li2ri
  (trans (∨r₁-li-eq S (view-ant (irr S) Γ) (∧r*-ri-inv f)
            (subst (λ f → isOK (tags-ri S f)) (sym (∧r*∧r*-ri-inv f)) ok))
         (cong f2li (∨r₁eq (∧r*∧r*-ri-inv f))))

∨r₂-li-eq : (S : Irr) {Γ : Cxt} (v : LView (irr S) Γ) {A B : Fma} (fs : All (λ C → irr S ∣ Γ ⊢li C) (toTree B))
  → (ok : isOK (tags-ri S (∧r*-ri B fs)))
  → ∨r₂-li v {A = A} fs ≡ f2li (∨r₂ (∧r*-ri B fs) ok)
∨r₂-li-eq (just (` X) , _) atom fs ok = trans
  (cong (λ ch → f2li (∨r₂-li-irr atom fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₂eq refl))
∨r₂-li-eq ( - , _) empty fs ok = trans
  (cong (λ ch → f2li (∨r₂-li-irr empty fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₂eq refl))
∨r₂-li-eq ( - , _) (pass v) fs ok = trans
  (cong (λ ch → f2li (∨r₂-li-irr (pass v) fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₂eq refl))
∨r₂-li-eq (just (D ∧ E) , _) (∧l v w) fs ok = trans
  (cong (λ ch → f2li (∨r₂-li-irr (∧l v w) fs ch))
    (check-focus-ok fs (subst isOK (sym (tags-ri∧r*-ri _ fs)) ok)))
  (cong f2li (∨r₂eq refl))

∨r₂-ri-eq : (S : Irr) {Γ : Cxt} {A B : Fma} (f : irr S ∣ Γ ⊢ri B) (ok : isOK (tags-ri S f))
  → ∨r₂-ri {A = A} f ≡ li2ri (f2li (∨r₂ f ok))
∨r₂-ri-eq S {Γ} f ok = cong li2ri
  (trans (∨r₂-li-eq S (view-ant (irr S) Γ) (∧r*-ri-inv f)
            (subst (λ f → isOK (tags-ri S f)) (sym (∧r*∧r*-ri-inv f)) ok))
         (cong f2li (∨r₂eq (∧r*∧r*-ri-inv f))))

-- Focusing after embedding is the identity in each phase.
-- These three proofs are mutually recursive on focused derivations;
-- the right-rule cases use the fixed-point lemmas above.
focusemb-f : ∀ {S Γ C} (f : S ∣ Γ ⊢f C) → focus (emb-f f) ≡ li2ri (f2li f)
focusemb-li : ∀ {S Γ C} (f : S ∣ Γ ⊢li C) → focus (emb-li f) ≡ li2ri f
focusemb-ri : ∀ {S Γ C} (f : S ∣ Γ ⊢ri C) → focus (emb-ri f) ≡ f

focusemb-f ax = refl
focusemb-f Ir = refl
focusemb-f (pass p f) = cong (pass-ri p) (focusemb-li f)
focusemb-f (∧l₁ f) = cong ∧l₁-ri (focusemb-li f)
focusemb-f (∧l₂ f) = cong ∧l₂-ri (focusemb-li f)
focusemb-f (⊗r p f g ok) =
  trans (cong₂ (⊗r-ri p) (focusemb-ri f) (focusemb-ri g)) (⊗r-ri-eq _ f p g ok)
focusemb-f (∨r₁ f ok) = trans (cong ∨r₁-ri (focusemb-ri f)) (∨r₁-ri-eq _ f ok)
focusemb-f (∨r₂ f ok) = trans (cong ∨r₂-ri (focusemb-ri f)) (∨r₂-ri-eq _ f ok)

focusemb-li (⊗l f) = cong ⊗l-ri (focusemb-li f)
focusemb-li (Il f) = cong Il-ri (focusemb-li f)
focusemb-li (∨l {C = (` X , _)} f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
focusemb-li (∨l {C = (I , _)} f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
focusemb-li (∨l {C = (A ⊗ B , _)} f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
focusemb-li (∨l {C = (A ∨ B , _)} f g) = cong₂ ∨l-ri (focusemb-li f) (focusemb-li g)
focusemb-li (f2li f) = focusemb-f f

focusemb-ri (∧r f g) = cong₂ ∧r (focusemb-ri f) (focusemb-ri g)
focusemb-ri (li2ri f) = focusemb-li f
