{-# OPTIONS --safe #-}

module FocusEmb (At : Set) where

open import Data.List.Base hiding (head)
open import Data.Product.Base
open import Data.Empty
open import Relation.Binary.PropositionalEquality.Core

open import Utilities
open import Fma At
open import FocusSeqCalc At
open import FocusSeqCalcProperties At
open import Focus At
open import FocusProperties At
open import Emb At

gen⊗r-li-ok : ∀ {S Γ Δ B} (A : Fma) (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢f proj₂ (head (impconj [] A)))
  → (fs : All (λ x → irr S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (e : headAll fs ≡ f2li f) (g : - ∣ Δ ⊢ri B)
  → .(isOK (tags-fs S Γ fs)) → .{ok : isOK (tags-ri S (ri*₀ {Γ = Γ} A fs))}
  → gen⊗r-li A (f2li f) fs e g ≡ f2li (⊗r refl (ri*₀ {Γ = Γ} A fs) g ok)
gen⊗r-li-ok {S} {Γ} A f fs e g ok with check-focus {S} {Γ} fs
... | casepass (allpass {A = D} {Γ' = Γ'} gs refl refl refl) = ⊥-elim-irr (notOK-pass {D} {Γ'} gs ok)
... | case1 (all∧l₁ {A = D} {B = E} gs refl refl) = ⊥-elim-irr (notOK-∧l₁ {D} {E} {Γ} gs ok)
... | case2 (all∧l₂ {A = D} {B = E} gs refl refl) = ⊥-elim-irr (notOK-∧l₂ {D} {E} {Γ} gs ok)
... | case⊸l (all⊸l {A = D} {B = E} {Γ' = Γ'} {Δ = Δ'} h gs refl refl refl) = ⊥-elim-irr (notOK-⊸l {D} {E} {Γ'} {Δ'} h gs ok)
... | caseok ok' = refl

gen∨r₁-li-ok : ∀ {S Γ B} (A : Fma) (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢f proj₂ (head (impconj [] A)))
  → (fs : All (λ x → irr S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (e : headAll fs ≡ f2li f)
  → .(isOK (tags-fs S Γ fs)) → .{ok : isOK (tags-ri S (ri*₀ {Γ = Γ} A fs))}
  → gen∨r₁-li {B = B} A (f2li f) fs e ≡ f2li (∨r₁ {B = B} (ri*₀ {Γ = Γ} A fs) ok)
gen∨r₁-li-ok {S} {Γ} A f fs e ok with check-focus {S} {Γ} fs
... | casepass (allpass {A = D} {Γ' = Γ'} gs refl refl refl) = ⊥-elim-irr (notOK-pass {D} {Γ'} gs ok)
... | case1 (all∧l₁ {A = D} {B = E} gs refl refl) = ⊥-elim-irr (notOK-∧l₁ {D} {E} {Γ} gs ok)
... | case2 (all∧l₂ {A = D} {B = E} gs refl refl) = ⊥-elim-irr (notOK-∧l₂ {D} {E} {Γ} gs ok)
... | case⊸l (all⊸l {A = D} {B = E} {Γ' = Γ'} {Δ = Δ'} h gs refl refl refl) = ⊥-elim-irr (notOK-⊸l {D} {E} {Γ'} {Δ'} h gs ok)
... | caseok ok' = refl

gen∨r₂-li-ok : ∀ {S Γ A} (B : Fma) (f : S ∣ Γ ++ proj₁ (head (impconj [] B)) ⊢f proj₂ (head (impconj [] B)))
  → (fs : All (λ x → irr S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B)) (e : headAll fs ≡ f2li f)
  → .(isOK (tags-fs S Γ fs)) → .{ok : isOK (tags-ri S (ri*₀ {Γ = Γ} B fs))}
  → gen∨r₂-li {A = A} B (f2li f) fs e ≡ f2li (∨r₂ {A = A} (ri*₀ {Γ = Γ} B fs) ok)
gen∨r₂-li-ok {S} {Γ} B f fs e ok with check-focus {S} {Γ} fs
... | casepass (allpass {A = D} {Γ' = Γ'} gs refl refl refl) = ⊥-elim-irr (notOK-pass {D} {Γ'} gs ok)
... | case1 (all∧l₁ {A = D} {B = E} gs refl refl) = ⊥-elim-irr (notOK-∧l₁ {D} {E} {Γ} gs ok)
... | case2 (all∧l₂ {A = D} {B = E} gs refl refl) = ⊥-elim-irr (notOK-∧l₂ {D} {E} {Γ} gs ok)
... | case⊸l (all⊸l {A = D} {B = E} {Γ' = Γ'} {Δ = Δ'} h gs refl refl refl) = ⊥-elim-irr (notOK-⊸l {D} {E} {Γ'} {Δ'} h gs ok)
... | caseok ok' = refl

⊗r-ri-ok : ∀ {S Γ Δ A B} (f : irr S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) .(ok : isOK (tags-ri S f))
  → ⊗r-ri f g ≡ li2ri (f2li (⊗r refl f g ok))
⊗r-ri-ok {S , p} {Γ} {A = A} {B} f g ok = aux (ri-inv {Γ = Γ} f) (ri*₀ri-inv {Γ = Γ} f) (subst isOK (sym (tags-ri-inv₀ (S , p) f)) ok)
  where
  aux-head : (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
    → (h : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A))) (d : headAll fs ≡ h)
    → ri*₀ {Γ = Γ} A fs ≡ f → .(isOK (tags-fs (S , p) Γ fs))
    → li2ri (gen⊗r-li A h fs d g) ≡ li2ri (f2li (⊗r refl f g ok))
  aux-head fs (f2li {S = .S , q} h) d e ok' with isIrr-unique S q p
  ... | refl = trans (cong li2ri (gen⊗r-li-ok {S , p} {Γ} A h fs d g ok' {isOK-ri* {S , p} {Γ} A fs ok'}))
    (cong (λ f → li2ri (f2li f)) (⊗req e refl))

  aux : (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) → ri*₀ {Γ = Γ} A fs ≡ f → .(isOK (tags-fs (S , p) Γ fs))
    → li2ri (gen⊗r-li A (headAll fs) fs refl g) ≡ li2ri (f2li (⊗r refl f g ok))
  aux fs e ok' = aux-head fs (headAll fs) refl e ok'

∨r₁-ri-ok : ∀ {S Γ A B} (f : irr S ∣ Γ ⊢ri A) .(ok : isOK (tags-ri S f))
  → ∨r₁-ri {B = B} f ≡ li2ri (f2li (∨r₁ {B = B} f ok))
∨r₁-ri-ok {S , p} {Γ} {A = A} {B} f ok = aux (ri-inv {Γ = Γ} f) (ri*₀ri-inv {Γ = Γ} f) (subst isOK (sym (tags-ri-inv₀ (S , p) f)) ok)
  where
  aux-head : (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
    → (h : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A))) (d : headAll fs ≡ h)
    → ri*₀ {Γ = Γ} A fs ≡ f → .(isOK (tags-fs (S , p) Γ fs))
    → li2ri (gen∨r₁-li {B = B} A h fs d) ≡ li2ri (f2li (∨r₁ {B = B} f ok))
  aux-head fs (f2li {S = .S , q} h) d e ok' with isIrr-unique S q p
  ... | refl = trans (cong li2ri (gen∨r₁-li-ok {S , p} {Γ} A h fs d ok' {isOK-ri* {S , p} {Γ} A fs ok'}))
    (cong (λ f → li2ri (f2li f)) (∨r₁eq e))

  aux : (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) → ri*₀ {Γ = Γ} A fs ≡ f → .(isOK (tags-fs (S , p) Γ fs))
    → li2ri (gen∨r₁-li {B = B} A (headAll fs) fs refl) ≡ li2ri (f2li (∨r₁ {B = B} f ok))
  aux fs e ok' = aux-head fs (headAll fs) refl e ok'

∨r₂-ri-ok : ∀ {S Γ A B} (f : irr S ∣ Γ ⊢ri B) .(ok : isOK (tags-ri S f))
  → ∨r₂-ri {A = A} f ≡ li2ri (f2li (∨r₂ {A = A} f ok))
∨r₂-ri-ok {S , p} {Γ} {A = A} {B} f ok = aux (ri-inv {Γ = Γ} f) (ri*₀ri-inv {Γ = Γ} f) (subst isOK (sym (tags-ri-inv₀ (S , p) f)) ok)
  where
  aux-head : (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
    → (h : S ∣ Γ ++ proj₁ (head (impconj [] B)) ⊢li proj₂ (head (impconj [] B))) (d : headAll fs ≡ h)
    → ri*₀ {Γ = Γ} B fs ≡ f → .(isOK (tags-fs (S , p) Γ fs))
    → li2ri (gen∨r₂-li {A = A} B h fs d) ≡ li2ri (f2li (∨r₂ {A = A} f ok))
  aux-head fs (f2li {S = .S , q} h) d e ok' with isIrr-unique S q p
  ... | refl = trans (cong li2ri (gen∨r₂-li-ok {S , p} {Γ} B h fs d ok' {isOK-ri* {S , p} {Γ} B fs ok'}))
    (cong (λ f → li2ri (f2li f)) (∨r₂eq e))

  aux : (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B)) → ri*₀ {Γ = Γ} B fs ≡ f → .(isOK (tags-fs (S , p) Γ fs))
    → li2ri (gen∨r₂-li {A = A} B (headAll fs) fs refl) ≡ li2ri (f2li (∨r₂ {A = A} f ok))
  aux fs e ok' = aux-head fs (headAll fs) refl e ok'

focus-emb-ri : ∀ {S Γ A} (f : S ∣ Γ ⊢ri A) → focus (emb-ri f) ≡ f
focus-emb-li : ∀ {S Γ A} (f : S ∣ Γ ⊢li A) → focus (emb-li f) ≡ li2ri f
focus-emb-f : ∀ {S Γ A} (f : S ∣ Γ ⊢f A) → focus (emb-f f) ≡ li2ri (f2li f)

focus-emb-ri (∧r f g) = cong₂ ∧r (focus-emb-ri f) (focus-emb-ri g)
focus-emb-ri (⊸r f) = cong ⊸r (focus-emb-ri f)
focus-emb-ri (li2ri f) = focus-emb-li f

focus-emb-li (Il f) = cong Il-ri (focus-emb-li f)
focus-emb-li (⊗l f) = cong ⊗l-ri (focus-emb-li f)
focus-emb-li (∨l f g) = trans (cong₂ ∨l-ri (focus-emb-li f) (focus-emb-li g)) (∨l-ri-li2ri f g)
focus-emb-li (f2li f) = focus-emb-f f

focus-emb-f ax = refl
focus-emb-f Ir = refl
focus-emb-f (pass f) = cong pass-ri (focus-emb-li f)
focus-emb-f (∧l₁ f) = cong ∧l₁-ri (focus-emb-li f)
focus-emb-f (∧l₂ f) = cong ∧l₂-ri (focus-emb-li f)
focus-emb-f (⊸l refl f g) = cong₂ ⊸l-ri (focus-emb-ri f) (focus-emb-li g)
focus-emb-f (⊗r refl f g ok) = trans (cong₂ ⊗r-ri (focus-emb-ri f) (focus-emb-ri g)) (⊗r-ri-ok f g ok)
focus-emb-f (∨r₁ f ok) = trans (cong ∨r₁-ri (focus-emb-ri f)) (∨r₁-ri-ok f ok)
focus-emb-f (∨r₂ f ok) = trans (cong ∨r₂-ri (focus-emb-ri f)) (∨r₂-ri-ok f ok)
