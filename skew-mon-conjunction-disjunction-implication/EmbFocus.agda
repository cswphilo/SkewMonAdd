{-# OPTIONS --safe #-}

module EmbFocus (At : Set) where

open import Data.List.Base hiding (head)
open import Agda.Builtin.Maybe
open import Data.Product.Base
open import Agda.Builtin.Unit
open import Relation.Binary.PropositionalEquality.Core hiding (_≗_)

open import Utilities
open import Fma At
open import FocusSeqCalc At
open import FocusSeqCalcProperties At
open import Focus At
open import FocusProperties At
open import Emb At
open import FocusEq At
open import FocusEmb At
open import SeqCalc At

emb-subst-ri : ∀ {S Γ Δ A} (p : Γ ≡ Δ) (f : S ∣ Γ ⊢ri A) → emb-ri (subst-ri p f) ≡ subst-cxt p (emb-ri f)
emb-subst-ri refl f = refl

emb-⊸l : ∀ {Γ Δ Λ A B C} (p : Λ ≡ Γ ++ Δ) (h : - ∣ Γ ⊢ri A) (f : just B ∣ Δ ⊢li C)
  → emb-f (⊸l p h f) ≡ subst-cxt (sym p) (⊸l (emb-ri h) (emb-li f))
emb-⊸l refl h f = refl

subst-cxt-cong : ∀ {S Γ Δ A} (p : Γ ≡ Δ) {f g : S ∣ Γ ⊢ A} → f ≗ g → subst-cxt p f ≗ subst-cxt p g
subst-cxt-cong refl e = e

embIl-ri : ∀ {Γ C} (f : - ∣ Γ ⊢ri C) → emb-ri (Il-ri f) ≗ Il (emb-ri f)
embIl-ri (∧r f g) = ∧r (embIl-ri f) (embIl-ri g) ∙ ∧rIl
embIl-ri (⊸r f) = ⊸r (embIl-ri f) ∙ ⊸rIl
embIl-ri (li2ri f) = refl

emb⊗l-ri : ∀ {Γ A B C} (f : just A ∣ B ∷ Γ ⊢ri C) → emb-ri (⊗l-ri f) ≗ ⊗l (emb-ri f)
emb⊗l-ri (∧r f g) = ∧r (emb⊗l-ri f) (emb⊗l-ri g) ∙ ∧r⊗l
emb⊗l-ri (⊸r f) = ⊸r (emb⊗l-ri f) ∙ ⊸r⊗l
emb⊗l-ri (li2ri f) = refl

embpass-ri : ∀ {Γ A C} (f : just A ∣ Γ ⊢ri C) → emb-ri (pass-ri f) ≗ pass (emb-ri f)
embpass-ri (∧r f g) = ∧r (embpass-ri f) (embpass-ri g) ∙ ∧rpass
embpass-ri (⊸r f) = ⊸r (embpass-ri f) ∙ ⊸rpass
embpass-ri (li2ri f) = refl

emb∧l₁-ri : ∀ {Γ A B C} (f : just A ∣ Γ ⊢ri C) → emb-ri (∧l₁-ri {B = B} f) ≗ ∧l₁ (emb-ri f)
emb∧l₁-ri (∧r f g) = ∧r (emb∧l₁-ri f) (emb∧l₁-ri g) ∙ ∧r∧l₁
emb∧l₁-ri (⊸r f) = ⊸r (emb∧l₁-ri f) ∙ ⊸r∧l₁
emb∧l₁-ri (li2ri f) = refl

emb∧l₂-ri : ∀ {Γ A B C} (f : just B ∣ Γ ⊢ri C) → emb-ri (∧l₂-ri {A = A} f) ≗ ∧l₂ (emb-ri f)
emb∧l₂-ri (∧r f g) = ∧r (emb∧l₂-ri f) (emb∧l₂-ri g) ∙ ∧r∧l₂
emb∧l₂-ri (⊸r f) = ⊸r (emb∧l₂-ri f) ∙ ⊸r∧l₂
emb∧l₂-ri (li2ri f) = refl

emb∨l-ri : ∀ {Γ A B C} (f : just A ∣ Γ ⊢ri C) (g : just B ∣ Γ ⊢ri C)
  → emb-ri (∨l-ri f g) ≗ ∨l (emb-ri f) (emb-ri g)
emb∨l-ri (∧r f g) (∧r f' g') = ∧r (emb∨l-ri f f') (emb∨l-ri g g') ∙ ∧r∨l
emb∨l-ri (⊸r f) (⊸r g) = ⊸r (emb∨l-ri f g) ∙ ⊸r∨l
emb∨l-ri (li2ri {C = ` X , tt} f) (li2ri g) = refl
emb∨l-ri (li2ri {C = I , tt} f) (li2ri g) = refl
emb∨l-ri (li2ri {C = A ⊗ B , tt} f) (li2ri g) = refl
emb∨l-ri (li2ri {C = A ∨ B , tt} f) (li2ri g) = refl

emb⊸l-ri : ∀ {Γ Δ A B C} (f : - ∣ Γ ⊢ri A) (g : just B ∣ Δ ⊢ri C)
  → emb-ri (⊸l-ri f g) ≗ ⊸l (emb-ri f) (emb-ri g)
emb⊸l-ri f (∧r g h) = ∧r (emb⊸l-ri f g) (emb⊸l-ri f h) ∙ ∧r⊸l
emb⊸l-ri {Γ} f (⊸r g) = ⊸r (≡to≗ (emb-subst-ri (sym (++ass Γ)) (⊸l-ri f g)) ∙ subst-cxt-cong (sym (++ass Γ)) (emb⊸l-ri f g)) ∙ ⊸r⊸l
emb⊸l-ri f (li2ri g) = refl

Il-fs-inv : ∀ {Γ Φ} (fs : All (λ x → (just I) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) → Il-fs (Il-inv-fs fs) ≡ fs
Il-fs-inv (leaf (Il f)) = refl
Il-fs-inv (node fs gs) = cong₂ node (Il-fs-inv fs) (Il-fs-inv gs)

⊗l-fs-inv : ∀ {Γ A B Φ} (fs : All (λ x → (just (A ⊗ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) → ⊗l-fs (⊗l-inv-fs fs) ≡ fs
⊗l-fs-inv (leaf (⊗l f)) = refl
⊗l-fs-inv (node fs gs) = cong₂ node (⊗l-fs-inv fs) (⊗l-fs-inv gs)

∨l-fs-inv : ∀ {Γ A B Φ} (fs : All (λ x → (just (A ∨ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) → ∨l-fs (∨l-inv-fs₁ fs) (∨l-inv-fs₂ fs) ≡ fs
∨l-fs-inv (leaf (∨l f g)) = refl
∨l-fs-inv (node fs gs) = cong₂ node (∨l-fs-inv fs) (∨l-fs-inv gs)

embIl-ri* : ∀ {Γ} (C : Fma) (fs : All (λ x → (just I) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → emb-ri (ri*₀ C fs) ≗ Il (emb-ri (ri*₀ C (Il-inv-fs fs)))
embIl-ri* {Γ} C fs =
  ≡to≗ (sym (cong (λ gs → emb-ri (ri*₀ {S = just I} {Γ = Γ} C gs)) (Il-fs-inv fs)))
  ∙ ≡to≗ (cong emb-ri (sym (Il-ri* {Γ} C (Il-inv-fs fs))))
  ∙ embIl-ri (ri*₀ C (Il-inv-fs fs))

emb⊗l-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just (A ⊗ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → emb-ri (ri*₀ C fs) ≗ ⊗l (emb-ri (ri*₀ {Γ = B ∷ Γ} C (⊗l-inv-fs fs)))
emb⊗l-ri* {Γ} {A} {B} C fs =
  ≡to≗ (sym (cong (λ gs → emb-ri (ri*₀ {S = just (A ⊗ B)} {Γ = Γ} C gs)) (⊗l-fs-inv fs)))
  ∙ ≡to≗ (cong emb-ri (sym (⊗l-ri* {Γ} {A} {B} C (⊗l-inv-fs fs))))
  ∙ emb⊗l-ri (ri*₀ {Γ = B ∷ Γ} C (⊗l-inv-fs fs))

emb∨l-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just (A ∨ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → emb-ri (ri*₀ C fs) ≗ ∨l (emb-ri (ri*₀ C (∨l-inv-fs₁ fs))) (emb-ri (ri*₀ C (∨l-inv-fs₂ fs)))
emb∨l-ri* {Γ} {A} {B} C fs =
  ≡to≗ (sym (cong (λ gs → emb-ri (ri*₀ {S = just (A ∨ B)} {Γ = Γ} C gs)) (∨l-fs-inv fs)))
  ∙ ≡to≗ (cong emb-ri (sym (∨l-ri* {Γ} C (∨l-inv-fs₁ fs) (∨l-inv-fs₂ fs))))
  ∙ emb∨l-ri (ri*₀ C (∨l-inv-fs₁ fs)) (ri*₀ C (∨l-inv-fs₂ fs))

embpass-ri* : ∀ {Γ A} (C : Fma) (fs : All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → emb-ri (ri*₀ {Γ = A ∷ Γ} C (pass-fs fs)) ≗ pass (emb-ri (ri*₀ C fs))
embpass-ri* {Γ} {A} C fs = ≡to≗ (cong emb-ri (sym (pass-ri* {Γ} {A} C fs))) ∙ embpass-ri (ri*₀ C fs)

emb∧l₁-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → emb-ri (ri*₀ C (∧l₁-fs {B = B} fs)) ≗ ∧l₁ (emb-ri (ri*₀ C fs))
emb∧l₁-ri* {Γ} {A} {B} C fs = ≡to≗ (cong emb-ri (sym (∧l₁-ri* {Γ} {A} {B} C fs))) ∙ emb∧l₁-ri (ri*₀ C fs)

emb∧l₂-ri* : ∀ {Γ A B} (C : Fma) (fs : All (λ x → (just B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → emb-ri (ri*₀ C (∧l₂-fs {A = A} fs)) ≗ ∧l₂ (emb-ri (ri*₀ C fs))
emb∧l₂-ri* {Γ} {A} {B} C fs = ≡to≗ (cong emb-ri (sym (∧l₂-ri* {Γ} {A} {B} C fs))) ∙ emb∧l₂-ri (ri*₀ C fs)

emb⊸l-ri* : ∀ {Γ Δ A B} (C : Fma) (h : - ∣ Γ ⊢ri A) (fs : All (λ x → (just B) ∣ Δ ++ proj₁ x ⊢li proj₂ x) (impconj [] C))
  → emb-ri (ri*₀ {Γ = Γ ++ Δ} C (⊸l-fs {Δ = Δ} h fs)) ≗ ⊸l (emb-ri h) (emb-ri (ri*₀ {Γ = Δ} C fs))
emb⊸l-ri* {Γ} {Δ} C h fs = ≡to≗ (cong emb-ri (sym (⊸l-ri* {Γ} {Δ} C h fs))) ∙ emb⊸l-ri h (ri*₀ {Γ = Δ} C fs)


embgen⊗r-li : ∀ {S Γ Δ B} (A : Fma) (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  → (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (e : headAll fs ≡ f) (g : - ∣ Δ ⊢ri B)
  → emb-li (gen⊗r-li A (headAll fs) fs refl g) ≗ ⊗r (emb-ri (ri*₀ {Γ = Γ} A fs)) (emb-ri g)
embgen⊗r-li {Γ = Γ} A (Il f) fs e g =
  ≡to≗ (cong emb-li (gen⊗r-li-head (Il f) fs e g))
  ∙ Il (≡to≗ (cong emb-li (sym (gen⊗r-li-head f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e)) g))) ∙ embgen⊗r-li {Γ = Γ} A f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e)) g) ∙ (~ ⊗rIl)
  ∙ ⊗r (~ embIl-ri* {Γ} A fs) refl
embgen⊗r-li {Γ = Γ} A (⊗l {A = D} {B = E} f) fs e g =
  ≡to≗ (cong emb-li (gen⊗r-li-head (⊗l f) fs e g))
  ∙ ⊗l (≡to≗ (cong emb-li (sym (gen⊗r-li-head f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e)) g))) ∙ embgen⊗r-li {Γ = E ∷ Γ} A f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e)) g) ∙ (~ ⊗r⊗l)
  ∙ ⊗r (~ emb⊗l-ri* {Γ} {D} {E} A fs) refl
embgen⊗r-li {Γ = Γ} A (∨l {A = D} {B = E} f f') fs e g =
  ≡to≗ (cong emb-li (gen⊗r-li-head (∨l f f') fs e g))
  ∙ ∨l
    (≡to≗ (cong emb-li (sym (gen⊗r-li-head f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e)) g))) ∙ embgen⊗r-li {Γ = Γ} A f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e)) g)
    (≡to≗ (cong emb-li (sym (gen⊗r-li-head f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e)) g))) ∙ embgen⊗r-li {Γ = Γ} A f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e)) g) ∙ (~ ⊗r∨l)
  ∙ ⊗r (~ emb∨l-ri* {Γ} {D} {E} A fs) refl
embgen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g with check-focus {S} {Γ} fs
... | casepass (allpass {A = D} {Γ' = Γ'} gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (pass f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen⊗rpass-li gs g))
  ∙ pass (embgen⊗r-li {Γ = Γ'} A k gs d g) ∙ (~ ⊗rpass)
  ∙ ⊗r (~ embpass-ri* {Γ'} {D} A gs) refl
embgen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | case1 (all∧l₁ {A = D} {B = E} gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₁ f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen⊗r∧l₁-li gs g))
  ∙ ∧l₁ (embgen⊗r-li {Γ = Γ} A k gs d g) ∙ (~ ⊗r∧l₁)
  ∙ ⊗r (~ emb∧l₁-ri* {Γ} {D} {E} A gs) refl
embgen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | case2 (all∧l₂ {A = D} {B = E} gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₂ f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen⊗r∧l₂-li gs g))
  ∙ ∧l₂ (embgen⊗r-li {Γ = Γ} A k gs d g) ∙ (~ ⊗r∧l₂)
  ∙ ⊗r (~ emb∧l₂-ri* {Γ} {D} {E} A gs) refl
embgen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | case⊸l (all⊸l {A = D} {B = E} {Γ' = Γ'} {Δ = Δ'} h gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ {x} f → f2li (⊸l (++ass Γ' {Δ'} {proj₁ x}) h f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen⊗r⊸l-li h gs g))
  ∙ ≡to≗ (emb-⊸l (++ass Γ') h (gen⊗r-li A (headAll gs) gs refl g))
  ∙ subst-cxt-cong (sym (++ass Γ')) (⊸l refl (embgen⊗r-li {Γ = Δ'} A k gs d g)) ∙ (~ ⊗r⊸l)
  ∙ ⊗r (~ emb⊸l-ri* {Γ'} {Δ'} {D} {E} A h gs) refl
embgen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | caseok ok =
  ≡to≗ (cong emb-li (trans (gen⊗r-li-head (f2li f) fs e g) (gen⊗r-li-ok A f fs e g ok {isOK-ri* A fs ok})))

embgen∨r₁-li : ∀ {S Γ B} (A : Fma) (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  → (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) (e : headAll fs ≡ f)
  → emb-li (gen∨r₁-li {B = B} A (headAll fs) fs refl) ≗ ∨r₁ {B = B} (emb-ri (ri*₀ {Γ = Γ} A fs))
embgen∨r₁-li {Γ = Γ} A (Il f) fs e =
  ≡to≗ (cong emb-li (gen∨r₁-li-head (Il f) fs e))
  ∙ Il (≡to≗ (cong emb-li (sym (gen∨r₁-li-head f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e))))) ∙ embgen∨r₁-li {Γ = Γ} A f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e))) ∙ (~ ∨r₁Il)
  ∙ ∨r₁ (~ embIl-ri* {Γ} A fs)
embgen∨r₁-li {Γ = Γ} A (⊗l {A = D} {B = E} f) fs e =
  ≡to≗ (cong emb-li (gen∨r₁-li-head (⊗l f) fs e))
  ∙ ⊗l (≡to≗ (cong emb-li (sym (gen∨r₁-li-head f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e))))) ∙ embgen∨r₁-li {Γ = E ∷ Γ} A f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e))) ∙ (~ ∨r₁⊗l)
  ∙ ∨r₁ (~ emb⊗l-ri* {Γ} {D} {E} A fs)
embgen∨r₁-li {Γ = Γ} A (∨l {A = D} {B = E} f f') fs e =
  ≡to≗ (cong emb-li (gen∨r₁-li-head (∨l f f') fs e))
  ∙ ∨l
    (≡to≗ (cong emb-li (sym (gen∨r₁-li-head f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e))))) ∙ embgen∨r₁-li {Γ = Γ} A f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e)))
    (≡to≗ (cong emb-li (sym (gen∨r₁-li-head f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e))))) ∙ embgen∨r₁-li {Γ = Γ} A f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e))) ∙ (~ ∨r₁∨l)
  ∙ ∨r₁ (~ emb∨l-ri* {Γ} {D} {E} A fs)
embgen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e with check-focus {S} {Γ} fs
... | casepass (allpass {A = D} {Γ' = Γ'} gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (pass f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₁pass-li gs))
  ∙ pass (embgen∨r₁-li {Γ = Γ'} A k gs d) ∙ (~ ∨r₁pass)
  ∙ ∨r₁ (~ embpass-ri* {Γ'} {D} A gs)
embgen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | case1 (all∧l₁ {A = D} {B = E} gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₁ f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₁∧l₁-li gs))
  ∙ ∧l₁ (embgen∨r₁-li {Γ = Γ} A k gs d) ∙ (~ ∨r₁∧l₁)
  ∙ ∨r₁ (~ emb∧l₁-ri* {Γ} {D} {E} A gs)
embgen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | case2 (all∧l₂ {A = D} {B = E} gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₂ f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₁∧l₂-li gs))
  ∙ ∧l₂ (embgen∨r₁-li {Γ = Γ} A k gs d) ∙ (~ ∨r₁∧l₂)
  ∙ ∨r₁ (~ emb∧l₂-ri* {Γ} {D} {E} A gs)
embgen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | case⊸l (all⊸l {A = D} {B = E} {Γ' = Γ'} {Δ = Δ'} h gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ {x} f → f2li (⊸l (++ass Γ' {Δ'} {proj₁ x}) h f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₁⊸l-li h gs))
  ∙ ⊸l refl (embgen∨r₁-li {Γ = Δ'} A k gs d) ∙ (~ ∨r₁⊸l)
  ∙ ∨r₁ (~ emb⊸l-ri* {Γ'} {Δ'} {D} {E} A h gs)
embgen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | caseok ok =
  ≡to≗ (cong emb-li (trans (gen∨r₁-li-head (f2li f) fs e) (gen∨r₁-li-ok A f fs e ok {isOK-ri* A fs ok})))

embgen∨r₂-li : ∀ {S Γ A} (B : Fma) (f : S ∣ Γ ++ proj₁ (head (impconj [] B)) ⊢li proj₂ (head (impconj [] B)))
  → (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B)) (e : headAll fs ≡ f)
  → emb-li (gen∨r₂-li {A = A} B (headAll fs) fs refl) ≗ ∨r₂ {A = A} (emb-ri (ri*₀ {Γ = Γ} B fs))
embgen∨r₂-li {Γ = Γ} B (Il f) fs e =
  ≡to≗ (cong emb-li (gen∨r₂-li-head (Il f) fs e))
  ∙ Il (≡to≗ (cong emb-li (sym (gen∨r₂-li-head f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e))))) ∙ embgen∨r₂-li {Γ = Γ} B f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e))) ∙ (~ ∨r₂Il)
  ∙ ∨r₂ (~ embIl-ri* {Γ} B fs)
embgen∨r₂-li {Γ = Γ} B (⊗l {A = D} {B = E} f) fs e =
  ≡to≗ (cong emb-li (gen∨r₂-li-head (⊗l f) fs e))
  ∙ ⊗l (≡to≗ (cong emb-li (sym (gen∨r₂-li-head f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e))))) ∙ embgen∨r₂-li {Γ = E ∷ Γ} B f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e))) ∙ (~ ∨r₂⊗l)
  ∙ ∨r₂ (~ emb⊗l-ri* {Γ} {D} {E} B fs)
embgen∨r₂-li {Γ = Γ} B (∨l {A = D} {B = E} f f') fs e =
  ≡to≗ (cong emb-li (gen∨r₂-li-head (∨l f f') fs e))
  ∙ ∨l
    (≡to≗ (cong emb-li (sym (gen∨r₂-li-head f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e))))) ∙ embgen∨r₂-li {Γ = Γ} B f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e)))
    (≡to≗ (cong emb-li (sym (gen∨r₂-li-head f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e))))) ∙ embgen∨r₂-li {Γ = Γ} B f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e))) ∙ (~ ∨r₂∨l)
  ∙ ∨r₂ (~ emb∨l-ri* {Γ} {D} {E} B fs)
embgen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e with check-focus {S} {Γ} fs
... | casepass (allpass {A = D} {Γ' = Γ'} gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (pass f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₂pass-li gs))
  ∙ pass (embgen∨r₂-li {Γ = Γ'} B k gs d) ∙ (~ ∨r₂pass)
  ∙ ∨r₂ (~ embpass-ri* {Γ'} {D} B gs)
embgen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | case1 (all∧l₁ {A = D} {B = E} gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₁ f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₂∧l₁-li gs))
  ∙ ∧l₁ (embgen∨r₂-li {Γ = Γ} B k gs d) ∙ (~ ∨r₂∧l₁)
  ∙ ∨r₂ (~ emb∧l₁-ri* {Γ} {D} {E} B gs)
embgen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | case2 (all∧l₂ {A = D} {B = E} gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₂ f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₂∧l₂-li gs))
  ∙ ∧l₂ (embgen∨r₂-li {Γ = Γ} B k gs d) ∙ (~ ∨r₂∧l₂)
  ∙ ∨r₂ (~ emb∧l₂-ri* {Γ} {D} {E} B gs)
embgen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | case⊸l (all⊸l {A = D} {B = E} {Γ' = Γ'} {Δ = Δ'} h gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ {x} f → f2li (⊸l (++ass Γ' {Δ'} {proj₁ x}) h f)) gs)) e
... | k | refl =
  ≡to≗ (cong emb-li (gen∨r₂⊸l-li h gs))
  ∙ ⊸l refl (embgen∨r₂-li {Γ = Δ'} B k gs d) ∙ (~ ∨r₂⊸l)
  ∙ ∨r₂ (~ emb⊸l-ri* {Γ'} {Δ'} {D} {E} B h gs)
embgen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | caseok ok =
  ≡to≗ (cong emb-li (trans (gen∨r₂-li-head (f2li f) fs e) (gen∨r₂-li-ok B f fs e ok {isOK-ri* B fs ok})))

emb⊗r-ri : ∀ {S Γ Δ A B} (f : S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → emb-ri (⊗r-ri f g) ≗ ⊗r (emb-ri f) (emb-ri g)
emb⊗r-ri {Γ = Γ} {A = A} f g with ri-inv {Γ = Γ} f | ri*₀ri-inv {Γ = Γ} f
... | fs | e = embgen⊗r-li A (headAll fs) fs refl g ∙ ⊗r (≡to≗ (cong emb-ri e)) refl

emb∨r₁-ri : ∀ {S Γ A B} (f : S ∣ Γ ⊢ri A)
  → emb-ri (∨r₁-ri {B = B} f) ≗ ∨r₁ (emb-ri f)
emb∨r₁-ri {Γ = Γ} {A = A} f with ri-inv {Γ = Γ} f | ri*₀ri-inv {Γ = Γ} f
... | fs | e = embgen∨r₁-li A (headAll fs) fs refl ∙ ∨r₁ (≡to≗ (cong emb-ri e))

emb∨r₂-ri : ∀ {S Γ A B} (f : S ∣ Γ ⊢ri B)
  → emb-ri (∨r₂-ri {A = A} f) ≗ ∨r₂ (emb-ri f)
emb∨r₂-ri {Γ = Γ} {B = B} f with ri-inv {Γ = Γ} f | ri*₀ri-inv {Γ = Γ} f
... | fs | e = embgen∨r₂-li B (headAll fs) fs refl ∙ ∨r₂ (≡to≗ (cong emb-ri e))

embax-ri : (A : Fma) → emb-ri (ax-ri {A}) ≗ ax
embax-ri (` X) = refl
embax-ri I = ~ axI
embax-ri (A ⊗ B) =
  emb⊗l-ri (⊗r-ri ax-ri (pass-ri ax-ri))
  ∙ ⊗l (emb⊗r-ri ax-ri (pass-ri ax-ri) ∙ ⊗r (embax-ri A) (embpass-ri ax-ri ∙ pass (embax-ri B)))
  ∙ (~ ax⊗)
embax-ri (A ⊸ B) =
  ⊸r (emb⊸l-ri (pass-ri ax-ri) ax-ri ∙ ⊸l (embpass-ri ax-ri ∙ pass (embax-ri A)) (embax-ri B))
  ∙ (~ ax⊸)
embax-ri (A ∧ B) =
  ∧r (emb∧l₁-ri ax-ri ∙ ∧l₁ (embax-ri A)) (emb∧l₂-ri ax-ri ∙ ∧l₂ (embax-ri B))
  ∙ (~ ax∧)
embax-ri (A ∨ B) =
  emb∨l-ri (∨r₁-ri ax-ri) (∨r₂-ri ax-ri)
  ∙ ∨l (emb∨r₁-ri ax-ri ∙ ∨r₁ (embax-ri A)) (emb∨r₂-ri ax-ri ∙ ∨r₂ (embax-ri B))
  ∙ (~ ax∨)

embfocus : ∀ {S Γ A} (f : S ∣ Γ ⊢ A) → emb-ri (focus f) ≗ f
embfocus (ax {A}) = embax-ri A
embfocus (pass f) = embpass-ri (focus f) ∙ pass (embfocus f)
embfocus Ir = refl
embfocus (Il f) = embIl-ri (focus f) ∙ Il (embfocus f)
embfocus (⊗l f) = emb⊗l-ri (focus f) ∙ ⊗l (embfocus f)
embfocus (⊗r f g) = emb⊗r-ri (focus f) (focus g) ∙ ⊗r (embfocus f) (embfocus g)
embfocus (⊸r f) = ⊸r (embfocus f)
embfocus (⊸l f g) = emb⊸l-ri (focus f) (focus g) ∙ ⊸l (embfocus f) (embfocus g)
embfocus (∧r f g) = ∧r (embfocus f) (embfocus g)
embfocus (∧l₁ f) = emb∧l₁-ri (focus f) ∙ ∧l₁ (embfocus f)
embfocus (∧l₂ f) = emb∧l₂-ri (focus f) ∙ ∧l₂ (embfocus f)
embfocus (∨r₁ f) = emb∨r₁-ri (focus f) ∙ ∨r₁ (embfocus f)
embfocus (∨r₂ f) = emb∨r₂-ri (focus f) ∙ ∨r₂ (embfocus f)
embfocus (∨l f g) = emb∨l-ri (focus f) (focus g) ∙ ∨l (embfocus f) (embfocus g)
