{-# OPTIONS --safe #-}

module Focus (At : Set) where

open import Data.List.Base hiding (head)
open import Data.List.Relation.Unary.All as LA using ()
open import Agda.Builtin.Maybe
open import Data.Product.Base
open import Data.Sum.Base
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Bool.Base hiding (_∧_; _∨_)
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality.Core hiding (_≗_)

open import Utilities
open import Fma At
open import SeqCalc At
open import FocusSeqCalc At
open import FocusSeqCalcProperties At


Il-ri : ∀ {Γ C} → - ∣ Γ ⊢ri C → just I ∣ Γ ⊢ri C
Il-ri (∧r f g) = ∧r (Il-ri f) (Il-ri g)
Il-ri (⊸r f) = ⊸r (Il-ri f)
Il-ri (li2ri f) = li2ri (Il f)

⊗l-ri : ∀ {Γ A B C} → just A ∣ B ∷ Γ ⊢ri C → just (A ⊗ B) ∣ Γ ⊢ri C
⊗l-ri (∧r f g) = ∧r (⊗l-ri f) (⊗l-ri g)
⊗l-ri (⊸r f) = ⊸r (⊗l-ri f)
⊗l-ri (li2ri f) = li2ri (⊗l f)

∨l-ri : ∀ {Γ A B C} → just A ∣ Γ ⊢ri C → just B ∣ Γ ⊢ri C → just (A ∨ B) ∣ Γ ⊢ri C
∨l-ri (∧r f g) (∧r f' g') = ∧r (∨l-ri f f') (∨l-ri g g')
∨l-ri (⊸r f) (⊸r g) = ⊸r (∨l-ri f g)
∨l-ri (li2ri {C = ` X , tt} f) (li2ri g) = li2ri (∨l f g)
∨l-ri (li2ri {C = I , tt} f) (li2ri g) = li2ri (∨l f g)
∨l-ri (li2ri {C = A ⊗ B , tt} f) (li2ri g) = li2ri (∨l f g)
∨l-ri (li2ri {C = A ∨ B , tt} f) (li2ri g) = li2ri (∨l f g)

pass-ri : ∀ {Γ A C} → just A ∣ Γ ⊢ri C → - ∣ A ∷ Γ ⊢ri C
pass-ri (∧r f g) = ∧r (pass-ri f) (pass-ri g)
pass-ri (⊸r f) = ⊸r (pass-ri f)
pass-ri (li2ri f) = li2ri (f2li (pass f))

∧l₁-ri : ∀ {Γ A B C} → just A ∣ Γ ⊢ri C → just (A ∧ B) ∣ Γ ⊢ri C
∧l₁-ri (∧r f g) = ∧r (∧l₁-ri f) (∧l₁-ri g)
∧l₁-ri (⊸r f) = ⊸r (∧l₁-ri f)
∧l₁-ri (li2ri f) = li2ri (f2li (∧l₁ f))

∧l₂-ri : ∀ {Γ A B C} → just B ∣ Γ ⊢ri C → just (A ∧ B) ∣ Γ ⊢ri C
∧l₂-ri (∧r f g) = ∧r (∧l₂-ri f) (∧l₂-ri g)
∧l₂-ri (⊸r f) = ⊸r (∧l₂-ri f)
∧l₂-ri (li2ri f) = li2ri (f2li (∧l₂ f))

⊸l-ri : ∀ {Γ Δ A B C} → - ∣ Γ ⊢ri A → just B ∣ Δ ⊢ri C → just (A ⊸ B) ∣ Γ ++ Δ ⊢ri C
⊸l-ri f (∧r g h) = ∧r (⊸l-ri f g) (⊸l-ri f h)
⊸l-ri {Γ = Γ} f (⊸r g) = ⊸r (subst-ri (sym (++ass Γ)) (⊸l-ri f g))
⊸l-ri f (li2ri g) = li2ri (f2li (⊸l refl f g))

Ir-ri : - ∣ [] ⊢ri I
Ir-ri = li2ri (f2li Ir)

ri* : ∀ {S Γ} (Ω : Cxt) (A : Fma) → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj Ω A) → S ∣ Γ ++ Ω ⊢ri A
ri* {Γ = Γ} Ω (A ∧ B) (node fs gs) = ∧r (ri* {Γ = Γ} Ω A fs) (ri* {Γ = Γ} Ω B gs)
ri* {Γ = Γ} Ω (A ⊸ B) fs = ⊸r (subst-ri (sym (++ass Γ)) (ri* {Γ = Γ} (Ω ++ A ∷ []) B fs))
ri* Ω (` X) (leaf f) = li2ri f
ri* Ω I (leaf f) = li2ri f
ri* Ω (A ⊗ B) (leaf f) = li2ri f
ri* Ω (A ∨ B) (leaf f) = li2ri f

ri*ri*-inv : ∀ {S Γ Λ A} (Ω : Cxt) (f : S ∣ Λ ⊢ri A) (eq : Λ ≡ Γ ++ Ω)
  → ri* {Γ = Γ} Ω A (ri*-inv Ω f eq) ≡ subst-ri eq f
ri*ri*-inv Ω (∧r f g) eq = trans (cong₂ ∧r (ri*ri*-inv Ω f eq) (ri*ri*-inv Ω g eq)) (sym (subst-ri-∧r eq f g))
ri*ri*-inv {Γ = Γ} Ω (⊸r {A = A} f) eq =
  trans (cong ⊸r (trans (cong (subst-ri (sym (++ass Γ))) (ri*ri*-inv (Ω ++ [ A ]) f (trans (cong (_++ [ A ]) eq) (++ass Γ))))
    (subst-ri-compose (trans (cong (_++ [ A ]) eq) (++ass Γ)) (sym (++ass Γ)) (cong (_++ [ A ]) eq) f))) (sym (subst-ri-⊸r eq f))
ri*ri*-inv Ω (li2ri {C = ` X , tt} f) eq = sym (subst-ri-li2ri eq f)
ri*ri*-inv Ω (li2ri {C = I , tt} f) eq = sym (subst-ri-li2ri eq f)
ri*ri*-inv Ω (li2ri {C = A ⊗ B , tt} f) eq = sym (subst-ri-li2ri eq f)
ri*ri*-inv Ω (li2ri {C = A ∨ B , tt} f) eq = sym (subst-ri-li2ri eq f)

ri*-inv-ri* : ∀ {S Γ} (Ω : Cxt) (A : Fma) (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj Ω A))
  → ri*-inv {Γ = Γ} Ω (ri* {Γ = Γ} Ω A fs) refl ≡ fs
ri*-inv-ri* {S} {Γ} Ω (A ∧ B) (node fs gs) = cong₂ node (ri*-inv-ri* {S} {Γ} Ω A fs) (ri*-inv-ri* {S} {Γ} Ω B gs)
ri*-inv-ri* {S} {Γ} Ω (A ⊸ B) fs =
  trans (ri*-inv-subst (Ω ++ [ A ]) (sym (++ass Γ)) (ri* {Γ = Γ} (Ω ++ [ A ]) B fs) (++ass Γ))
    (trans (cong (ri*-inv {Γ = Γ} (Ω ++ [ A ]) (ri* {Γ = Γ} (Ω ++ [ A ]) B fs)) (uip {p = trans (sym (++ass Γ)) (++ass Γ)} {refl}))
      (ri*-inv-ri* {S} {Γ} (Ω ++ [ A ]) B fs))
ri*-inv-ri* Ω (` X) (leaf f) = refl
ri*-inv-ri* Ω I (leaf f) = refl
ri*-inv-ri* Ω (A ⊗ B) (leaf f) = refl
ri*-inv-ri* Ω (A ∨ B) (leaf f) = refl

ri*₀ : ∀ {S Γ} (A : Fma) → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A) → S ∣ Γ ⊢ri A
ri*₀ {Γ = Γ} A fs = subst-ri (++ru Γ) (ri* {Γ = Γ} [] A fs)

ri*₀ri-inv : ∀ {S Γ A} (f : S ∣ Γ ⊢ri A) → ri*₀ A (ri-inv f) ≡ f
ri*₀ri-inv {Γ = Γ} f = trans (cong (subst-ri (++ru Γ)) (ri*ri*-inv [] f (sym (++ru Γ)))) (subst-ri-compose (sym (++ru Γ)) (++ru Γ) refl f)

ri-inv-ri*₀ : ∀ {S Γ} (A : Fma) (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)) → ri-inv (ri*₀ A fs) ≡ fs
ri-inv-ri*₀ {Γ = Γ} A fs = trans (ri*-inv-subst [] (++ru Γ) (ri* {Γ = Γ} [] A fs) (sym (++ru Γ)))
  (trans (cong (ri*-inv {Γ = Γ} [] (ri* {Γ = Γ} [] A fs)) (uip {p = trans (++ru Γ) (sym (++ru Γ))} {refl})) (ri*-inv-ri* [] A fs))

pass-fs : ∀ {Γ A Φ} → All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → - ∣ (A ∷ Γ) ++ proj₁ x ⊢li proj₂ x) Φ
pass-fs = mapAll (λ f → f2li (pass f))

∧l₁-fs : ∀ {Γ A B Φ} → All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just (A ∧ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
∧l₁-fs = mapAll (λ f → f2li (∧l₁ f))

∧l₂-fs : ∀ {Γ A B Φ} → All (λ x → (just B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just (A ∧ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
∧l₂-fs = mapAll (λ f → f2li (∧l₂ f))

⊸l-fs : ∀ {Γ Δ A B Φ} → - ∣ Γ ⊢ri A → All (λ x → (just B) ∣ Δ ++ proj₁ x ⊢li proj₂ x) Φ
  → All (λ x → (just (A ⊸ B)) ∣ (Γ ++ Δ) ++ proj₁ x ⊢li proj₂ x) Φ
⊸l-fs {Γ = Γ} f = mapAll (λ g → f2li (⊸l (++ass Γ) f g))

record Allpass {S : Irr} {Γ : Cxt} {Φ : Tree (Cxt × Pos)} (fs : All (λ x → (irr S) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) : Set where
  constructor allpass
  field
    {A} : Fma
    {Γ'} : Cxt
    gs : All (λ x → (just A) ∣ Γ' ++ proj₁ x ⊢li proj₂ x) Φ
    eqS : irr S ≡ -
    eqΓ : Γ ≡ A ∷ Γ'
    eqf : subst₂ (λ S Γ → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) eqS eqΓ fs ≡ pass-fs gs

record All∧l₁ {S : Irr} {Γ : Cxt} {Φ : Tree (Cxt × Pos)} (fs : All (λ x → (irr S) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) : Set where
  constructor all∧l₁
  field
    {A B} : Fma
    gs : All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
    eqS : irr S ≡ just (A ∧ B)
    eqf : subst (λ S → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) eqS fs ≡ ∧l₁-fs gs

record All∧l₂ {S : Irr} {Γ : Cxt} {Φ : Tree (Cxt × Pos)} (fs : All (λ x → (irr S) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) : Set where
  constructor all∧l₂
  field
    {A B} : Fma
    gs : All (λ x → (just B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
    eqS : irr S ≡ just (A ∧ B)
    eqf : subst (λ S → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) eqS fs ≡ ∧l₂-fs gs

record All⊸l {S : Irr} {Γ : Cxt} {Φ : Tree (Cxt × Pos)} (fs : All (λ x → (irr S) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) : Set where
  constructor all⊸l
  field
    {A B} : Fma
    {Γ' Δ} : Cxt
    f : - ∣ Γ' ⊢ri A
    gs : All (λ x → (just B) ∣ Δ ++ proj₁ x ⊢li proj₂ x) Φ
    eqS : irr S ≡ just (A ⊸ B)
    eqΓ : Γ ≡ Γ' ++ Δ
    eqf : subst₂ (λ S Γ → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) eqS eqΓ fs ≡ ⊸l-fs f gs

data CheckFocus {S : Irr} {Γ : Cxt} {Φ : Tree (Cxt × Pos)}
  (fs : All (λ x → irr S ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) : Set where
  casepass : Allpass {S} {Γ} fs → CheckFocus fs
  case1 : All∧l₁ {S} {Γ} fs → CheckFocus fs
  case2 : All∧l₂ {S} {Γ} fs → CheckFocus fs
  case⊸l : All⊸l {S} {Γ} fs → CheckFocus fs
  caseok : isOK (tags-fs S Γ fs) → CheckFocus fs

data Check⊸l {A : Fma} {Λ : Cxt} (h : - ∣ Λ ⊢ri A) (Γ Ω Δ : Cxt) (t : Tag) : Set where
  new : t ≡ • → Check⊸l h Γ Ω Δ t
  old : (Ξ : Cxt) → Γ ≡ Λ ++ Ξ → Δ ≡ Ξ ++ Ω → t ≡ ⊸l Λ h → Check⊸l h Γ Ω Δ t

check-⊸l : ∀ {A B Λ Δ Θ C} (Γ Ω : Cxt) (p : Θ ≡ Λ ++ Δ) (h : - ∣ Λ ⊢ri A)
  (k : just B ∣ Δ ⊢li C) (eq : Θ ≡ Γ ++ Ω) → Check⊸l h Γ Ω Δ (tag-f Γ Ω (⊸l p h k) eq)
check-⊸l {Δ = Δ} Γ [] p h k eq = old Δ (trans (sym (++ru Γ)) (trans (sym eq) p)) (sym (++ru Δ)) refl
check-⊸l {Λ = Λ} {Δ} Γ (D ∷ Ω) p h k refl with cases++ Γ Λ Ω Δ (sym p)
... | inj₁ (Ξ , refl , refl) = new refl
... | inj₂ (Ξ , refl , refl) = old Ξ refl refl refl

tags-nonempty : ∀ S Γ {Φ} (fs : All (λ x → irr S ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) → tags-fs S Γ fs ≡ [] → ⊥
tags-nonempty S Γ (leaf (f2li f)) ()
tags-nonempty S Γ (node fs gs) eq = tags-nonempty S Γ fs (empty++1 (tags-fs S Γ fs) {ys = tags-fs S Γ gs} eq)

tags-onlyP : ∀ {A Γ Φ} (fs : All (λ x → just A ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → LA.All (λ t → t ≡ P) (tags-fs (- , tt) (A ∷ Γ) (pass-fs fs))
tags-onlyP (leaf f) = refl LA.∷ LA.[]
tags-onlyP (node fs gs) = All++ (tags-onlyP fs) (tags-onlyP gs)

tags-onlyC₁ : ∀ {A B Γ Φ} (fs : All (λ x → just A ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → LA.All (λ t → t ≡ C₁) (tags-fs (just (A ∧ B) , tt) (Γ) (∧l₁-fs fs))
tags-onlyC₁ (leaf f) = refl LA.∷ LA.[]
tags-onlyC₁ (node fs gs) = All++ (tags-onlyC₁ fs) (tags-onlyC₁ gs)

tags-onlyC₂ : ∀ {A B Γ Φ} (fs : All (λ x → just B ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → LA.All (λ t → t ≡ C₂) (tags-fs (just (A ∧ B) , tt) (Γ) (∧l₂-fs fs))
tags-onlyC₂ (leaf f) = refl LA.∷ LA.[]
tags-onlyC₂ (node fs gs) = All++ (tags-onlyC₂ fs) (tags-onlyC₂ gs)

tags-only⊸l : ∀ {S Γ Φ fs} (r : All⊸l {S} {Γ} {Φ} fs) →
  LA.All (λ t → t ≡ ⊸l (All⊸l.Γ' r) (All⊸l.f r)) (tags-fs S Γ fs)
tags-only⊸l {Φ = leaf ([] , _)} (all⊸l h (leaf g) refl refl refl) = refl LA.∷ LA.[]
tags-only⊸l {Φ = leaf ((D ∷ Ω) , _)} (all⊸l {Γ' = Λ} {Δ} h (leaf g) refl refl refl)
  rewrite cases++-inj₂ Δ Λ Ω D (sym (++ass Λ)) = refl LA.∷ LA.[]
tags-only⊸l (all⊸l h (node fs gs) refl refl refl) =
  All++ (tags-only⊸l (all⊸l h fs refl refl refl)) (tags-only⊸l (all⊸l h gs refl refl refl))

isOKC₁++1 : ∀ ts {us} → isOKC₁ ts → isOKC₁ (ts ++ us)
isOKC₁++1 (C₁ ∷ ts) {us} ok = isOKC₁++1 ts {us} ok
isOKC₁++1 (C₂ ∷ ts) ok = tt
isOKC₁++1 (R ∷ ts) ok = tt
isOKC₁++1 (• ∷ ts) ok = tt

isOKC₁-prefix : ∀ {ts us} → LA.All (λ t → t ≡ C₁) ts → isOKC₁ us → isOKC₁ (ts ++ us)
isOKC₁-prefix LA.[] ok = ok
isOKC₁-prefix {us = us} (refl LA.∷ ps) ok = isOKC₁-prefix {us = us} ps ok

isOK-C₁-prefix : ∀ {ts us} → LA.All (λ t → t ≡ C₁) ts → (ts ≡ [] → ⊥) → isOKC₁ us → isOK (ts ++ us)
isOK-C₁-prefix LA.[] ne ok = ⊥-elim (ne refl)
isOK-C₁-prefix {us = us} (refl LA.∷ ps) ne ok = isOKC₁-prefix {us = us} ps ok

isOKC₁-opposite : ∀ {ts} → LA.All (λ t → t ≡ C₂) ts → (ts ≡ [] → ⊥) → isOKC₁ ts
isOKC₁-opposite LA.[] ne = ⊥-elim (ne refl)
isOKC₁-opposite (refl LA.∷ ps) ne = tt

isOK-toC₁-fs : ∀ {A B Γ Φ ts} (fs : All (λ x → just (A ∧ B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → isOK (tags-fs (just (A ∧ B) , tt) Γ fs ++ ts) → isOKC₁ (tags-fs (just (A ∧ B) , tt) Γ fs ++ ts)
isOK-toC₁-fs {A} {B} {Γ} {ts = ts} (node fs gs) ok rewrite ++ass (tags-fs (just (A ∧ B) , tt) Γ fs) {tags-fs (just (A ∧ B) , tt) Γ gs} {ts} = isOK-toC₁-fs {ts = tags-fs (just (A ∧ B) , tt) Γ gs ++ ts} fs ok
isOK-toC₁-fs (leaf (f2li (∧l₁ f))) ok = ok
isOK-toC₁-fs (leaf (f2li (∧l₂ f))) ok = tt
isOK-toC₁-fs (leaf (f2li (⊗r p f g valid))) ok = tt
isOK-toC₁-fs (leaf (f2li (∨r₁ f valid))) ok = tt
isOK-toC₁-fs (leaf (f2li (∨r₂ f valid))) ok = tt

isOKC₂++1 : ∀ ts {us} → isOKC₂ ts → isOKC₂ (ts ++ us)
isOKC₂++1 (C₂ ∷ ts) {us} ok = isOKC₂++1 ts {us} ok
isOKC₂++1 (C₁ ∷ ts) ok = tt
isOKC₂++1 (R ∷ ts) ok = tt
isOKC₂++1 (• ∷ ts) ok = tt

isOKC₂-prefix : ∀ {ts us} → LA.All (λ t → t ≡ C₂) ts → isOKC₂ us → isOKC₂ (ts ++ us)
isOKC₂-prefix LA.[] ok = ok
isOKC₂-prefix {us = us} (refl LA.∷ ps) ok = isOKC₂-prefix {us = us} ps ok

isOK-C₂-prefix : ∀ {ts us} → LA.All (λ t → t ≡ C₂) ts → (ts ≡ [] → ⊥) → isOKC₂ us → isOK (ts ++ us)
isOK-C₂-prefix LA.[] ne ok = ⊥-elim (ne refl)
isOK-C₂-prefix {us = us} (refl LA.∷ ps) ne ok = isOKC₂-prefix {us = us} ps ok

isOKC₂-opposite : ∀ {ts} → LA.All (λ t → t ≡ C₁) ts → (ts ≡ [] → ⊥) → isOKC₂ ts
isOKC₂-opposite LA.[] ne = ⊥-elim (ne refl)
isOKC₂-opposite (refl LA.∷ ps) ne = tt

isOK-toC₂-fs : ∀ {A B Γ Φ ts} (fs : All (λ x → just (A ∧ B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ)
  → isOK (tags-fs (just (A ∧ B) , tt) Γ fs ++ ts) → isOKC₂ (tags-fs (just (A ∧ B) , tt) Γ fs ++ ts)
isOK-toC₂-fs {A} {B} {Γ} {ts = ts} (node fs gs) ok rewrite ++ass (tags-fs (just (A ∧ B) , tt) Γ fs) {tags-fs (just (A ∧ B) , tt) Γ gs} {ts} = isOK-toC₂-fs {ts = tags-fs (just (A ∧ B) , tt) Γ gs ++ ts} fs ok
isOK-toC₂-fs (leaf (f2li (∧l₁ f))) ok = tt
isOK-toC₂-fs (leaf (f2li (∧l₂ f))) ok = ok
isOK-toC₂-fs (leaf (f2li (⊗r p f g valid))) ok = tt
isOK-toC₂-fs (leaf (f2li (∨r₁ f valid))) ok = tt
isOK-toC₂-fs (leaf (f2li (∨r₂ f valid))) ok = tt

isOK⊸l++1 : ∀ {A Γ} (h : - ∣ Γ ⊢ri A) ts {us} → isOK⊸l Γ h ts → isOK⊸l Γ h (ts ++ us)
isOK⊸l++1 h (R ∷ ts) ok = tt
isOK⊸l++1 h (• ∷ ts) ok = tt
isOK⊸l++1 {Γ = Γ} h (⊸l Δ g ∷ ts) {us} ok with length≟ Γ Δ
... | no _ = tt
... | yes _ with eq-ri h g
...   | false = tt
...   | true = isOK⊸l++1 h ts {us} ok

isOK++1 : ∀ ts {us} → isOK ts → isOK (ts ++ us)
isOK++1 (R ∷ ts) ok = tt
isOK++1 (• ∷ ts) ok = tt
isOK++1 (P ∷ ts) {us} ok = isOK++1 ts {us} ok
isOK++1 (C₁ ∷ ts) {us} ok = isOKC₁++1 ts {us} ok
isOK++1 (C₂ ∷ ts) {us} ok = isOKC₂++1 ts {us} ok
isOK++1 (⊸l Γ h ∷ ts) {us} ok = isOK⊸l++1 h ts {us} ok

isOK-P-prefix : ∀ {ts us} → LA.All (λ t → t ≡ P) ts → isOK us → isOK (ts ++ us)
isOK-P-prefix LA.[] ok = ok
isOK-P-prefix {us = us} (refl LA.∷ ps) ok = isOK-P-prefix {us = us} ps ok

isOK⊸l-prefix : ∀ {A Γ ts us} (h : - ∣ Γ ⊢ri A) → LA.All (λ t → t ≡ ⊸l Γ h) ts
  → isOK⊸l Γ h us → isOK⊸l Γ h (ts ++ us)
isOK⊸l-prefix h LA.[] ok = ok
isOK⊸l-prefix {Γ = Γ} {us = us} h (refl LA.∷ ps) ok rewrite length≟-refl Γ | eq-ri-refl h = isOK⊸l-prefix {us = us} h ps ok

isOK-⊸l-prefix : ∀ {A Γ ts us} (h : - ∣ Γ ⊢ri A) → LA.All (λ t → t ≡ ⊸l Γ h) ts
  → (ts ≡ [] → ⊥) → isOK⊸l Γ h us → isOK (ts ++ us)
isOK-⊸l-prefix h LA.[] ne ok = ⊥-elim (ne refl)
isOK-⊸l-prefix {us = us} h (refl LA.∷ ps) ne ok = isOK⊸l-prefix {us = us} h ps ok

isOK-to⊸l-fs : ∀ {A B Λ Δ Φ ts} (h : - ∣ Λ ⊢ri A)
  (fs : All (λ x → just (A ⊸ B) ∣ (Λ ++ Δ) ++ proj₁ x ⊢li proj₂ x) Φ)
  → isOK (tags-fs (just (A ⊸ B) , tt) (Λ ++ Δ) fs ++ ts)
  → isOK⊸l Λ h (tags-fs (just (A ⊸ B) , tt) (Λ ++ Δ) fs ++ ts)
isOK-to⊸l-fs {A} {B} {Λ} {Δ} {ts = ts} h (node fs gs) ok rewrite ++ass (tags-fs (just (A ⊸ B) , tt) (Λ ++ Δ) fs) {tags-fs (just (A ⊸ B) , tt) (Λ ++ Δ) gs} {ts} = isOK-to⊸l-fs {Δ = Δ} {ts = tags-fs (just (A ⊸ B) , tt) (Λ ++ Δ) gs ++ ts} h fs ok
isOK-to⊸l-fs h (leaf (f2li (⊗r p f g valid))) ok = tt
isOK-to⊸l-fs h (leaf (f2li (∨r₁ f valid))) ok = tt
isOK-to⊸l-fs h (leaf (f2li (∨r₂ f valid))) ok = tt
isOK-to⊸l-fs {Λ = Λ} {Δ} {leaf (Ω , _)} {ts} h (leaf (f2li (⊸l {Γ = Λ′} p g k))) ok
  with check-⊸l (Λ ++ Δ) Ω p g k refl
... | new t rewrite t = tt
... | old Ξ q r t rewrite t with length≟ Λ Λ′
...   | no _ = tt
...   | yes len with split-at-length Λ Λ′ {Δ} {Ξ} q len
...     | refl , refl with eq-ri h g in e
...       | false = tt
...       | true with eq-ri-sound h g e
...         | refl = ok

isOK-⊸l-different : ∀ {A Λ Δ Λ′ Δ′ ts} (h : - ∣ Λ ⊢ri A) (g : - ∣ Λ′ ⊢ri A)
  → Λ ++ Δ ≡ Λ′ ++ Δ′ → LA.All (λ t → t ≡ ⊸l Λ′ g) ts → (ts ≡ [] → ⊥)
  → (⊸l Λ h ≡ ⊸l Λ′ g → ⊥) → isOK⊸l Λ h ts
isOK-⊸l-different h g p LA.[] ne different = ⊥-elim (ne refl)
isOK-⊸l-different {Λ = Λ} {Δ} {Λ′} {Δ′} h g p (refl LA.∷ ps) ne different with length≟ Λ Λ′
... | no _ = tt
... | yes len with split-at-length Λ Λ′ {Δ} {Δ′} p len
...   | refl , refl with eq-ri h g in e
...     | false = tt
...     | true with eq-ri-sound h g e
...       | refl = ⊥-elim (different refl)

check-leaf : ∀ {S Γ Ω C Λ} (f : irr S ∣ Λ ⊢li C) (eq : Λ ≡ Γ ++ Ω)
  → CheckFocus {S} {Γ} {leaf (Ω , C)} (leaf (subst-li eq f))
check-leaf (f2li (⊗r p f g ok)) refl = caseok tt
check-leaf (f2li (∨r₁ f ok)) refl = caseok tt
check-leaf (f2li (∨r₂ f ok)) refl = caseok tt
check-leaf (f2li (∧l₁ f)) refl = case1 (all∧l₁ (leaf f) refl refl)
check-leaf (f2li (∧l₂ f)) refl = case2 (all∧l₂ (leaf f) refl refl)
check-leaf {Γ = []} (f2li ax) refl = caseok tt
check-leaf {Γ = A ∷ Γ} (f2li ax) ()
check-leaf {Γ = []} (f2li Ir) refl = caseok tt
check-leaf {Γ = A ∷ Γ} (f2li Ir) ()
check-leaf {Γ = []} (f2li (pass f)) refl = caseok tt
check-leaf {Γ = A ∷ Γ} (f2li (pass f)) refl = casepass (allpass (leaf f) refl refl refl)
check-leaf {S} {Γ} {Ω} (f2li (⊸l p h k)) refl with check-⊸l Γ Ω p h k refl
... | new t = caseok (subst (λ t → isOK [ t ]) (sym t) tt)
check-leaf (f2li (⊸l {Γ = Λ} p h k)) refl | old Δ refl refl t = case⊸l (all⊸l h (leaf k) refl refl (cong (λ q → leaf (f2li (⊸l q h k))) (uip {p = p} {++ass Λ})))

-- Classify leaves and combine the two classifications at each node.
check-focus : {S : Irr} {Γ : Cxt} {Φ : Tree (Cxt × Pos)}
  → (fs : All (λ x → irr S ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ) → CheckFocus {S} {Γ} fs
check-focus {S} {Γ} {leaf (Ω , C)} (leaf f) = check-leaf {S} {Γ} {Ω} f refl
check-focus {S} {Γ} (node fs gs) with check-focus {S} {Γ} fs | check-focus {S} {Γ} gs
... | casepass (allpass hs refl refl refl) | casepass (allpass ks refl refl refl) = casepass (allpass (node hs ks) refl refl refl)
... | case1 (all∧l₁ hs refl refl) | case1 (all∧l₁ ks refl refl) = case1 (all∧l₁ (node hs ks) refl refl)
... | case2 (all∧l₂ hs refl refl) | case2 (all∧l₂ ks refl refl) = case2 (all∧l₂ (node hs ks) refl refl)
... | case1 (all∧l₁ hs refl refl) | case2 (all∧l₂ ks refl refl) =
  caseok (isOK-C₁-prefix {us = tags-fs S Γ gs} (tags-onlyC₁ hs) (tags-nonempty S Γ fs) (isOKC₁-opposite (tags-onlyC₂ ks) (tags-nonempty S Γ gs)))
... | case2 (all∧l₂ hs refl refl) | case1 (all∧l₁ ks refl refl) =
  caseok (isOK-C₂-prefix {us = tags-fs S Γ gs} (tags-onlyC₂ hs) (tags-nonempty S Γ fs) (isOKC₂-opposite (tags-onlyC₁ ks) (tags-nonempty S Γ gs)))
... | caseok ok | _ = caseok (isOK++1 (tags-fs S Γ fs) {tags-fs S Γ gs} ok)
... | casepass (allpass hs refl refl refl) | caseok ok = caseok (isOK-P-prefix {us = tags-fs S Γ gs} (tags-onlyP hs) ok)
... | case1 (all∧l₁ hs refl refl) | caseok ok = caseok (isOK-C₁-prefix {us = tags-fs S Γ gs} (tags-onlyC₁ hs) (tags-nonempty S Γ fs) (subst isOKC₁ (++ru (tags-fs S Γ gs)) (isOK-toC₁-fs {ts = []} gs (subst isOK (sym (++ru (tags-fs S Γ gs))) ok))))
... | case2 (all∧l₂ hs refl refl) | caseok ok = caseok (isOK-C₂-prefix {us = tags-fs S Γ gs} (tags-onlyC₂ hs) (tags-nonempty S Γ fs) (subst isOKC₂ (++ru (tags-fs S Γ gs)) (isOK-toC₂-fs {ts = []} gs (subst isOK (sym (++ru (tags-fs S Γ gs))) ok))))
... | case⊸l r@(all⊸l {Γ' = Λ} {Δ = Δ} h hs refl refl refl) | caseok ok = caseok (isOK-⊸l-prefix {us = tags-fs S Γ gs} h (tags-only⊸l r) (tags-nonempty S Γ fs) (subst (isOK⊸l Λ h) (++ru (tags-fs S Γ gs)) (isOK-to⊸l-fs {Δ = Δ} {ts = []} h gs (subst isOK (sym (++ru (tags-fs S Γ gs))) ok))))
... | case⊸l r@(all⊸l {Γ' = Λ} {Δ} h hs refl refl refl) | case⊸l r′@(all⊸l {Γ' = Λ′} {Δ′} g ks refl p e)
  with split≟ Λ Δ Λ′ Δ′ p
...   | no different = caseok (isOK-⊸l-prefix {us = tags-fs S Γ gs} h (tags-only⊸l r) (tags-nonempty S Γ fs)
  (isOK-⊸l-different {Δ = Δ} {Δ′ = Δ′} h g p (tags-only⊸l r′) (tags-nonempty S Γ gs) (λ { refl → different (refl , ++canc Λ p) })))
...   | yes (refl , refl) with h ≟ri g
...     | no different = caseok (isOK-⊸l-prefix {us = tags-fs S Γ gs} h (tags-only⊸l r) (tags-nonempty S Γ fs)
  (isOK-⊸l-different {Δ = Δ} {Δ′ = Δ} h g p (tags-only⊸l r′) (tags-nonempty S Γ gs) (λ { refl → different refl })))
check-focus (node fs gs) | case⊸l (all⊸l h hs refl refl refl) | case⊸l (all⊸l _ ks refl refl refl) | yes (refl , refl) | yes refl =
  case⊸l (all⊸l h (node hs ks) refl refl refl)

Il-inv : ∀ {Γ C} → just I ∣ Γ ⊢li C → - ∣ Γ ⊢li C
Il-inv (Il f) = f

⊗l-inv : ∀ {Γ A B C} → just (A ⊗ B) ∣ Γ ⊢li C → just A ∣ B ∷ Γ ⊢li C
⊗l-inv (⊗l f) = f

∨l-inv₁ : ∀ {Γ A B C} → just (A ∨ B) ∣ Γ ⊢li C → just A ∣ Γ ⊢li C
∨l-inv₁ (∨l f g) = f

∨l-inv₂ : ∀ {Γ A B C} → just (A ∨ B) ∣ Γ ⊢li C → just B ∣ Γ ⊢li C
∨l-inv₂ (∨l f g) = g

Il-inv-fs : ∀ {Γ Φ} → All (λ x → (just I) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → - ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
Il-inv-fs = mapAll Il-inv

⊗l-inv-fs : ∀ {Γ A B Φ} → All (λ x → (just (A ⊗ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just A) ∣ (B ∷ Γ) ++ proj₁ x ⊢li proj₂ x) Φ
⊗l-inv-fs = mapAll ⊗l-inv

∨l-inv-fs₁ : ∀ {Γ A B Φ} → All (λ x → (just (A ∨ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just A) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
∨l-inv-fs₁ = mapAll ∨l-inv₁

∨l-inv-fs₂ : ∀ {Γ A B Φ} → All (λ x → (just (A ∨ B)) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → All (λ x → (just B) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ
∨l-inv-fs₂ = mapAll ∨l-inv₂

isOK-ri* : ∀ {S Γ} (A : Fma) (fs : All (λ x → irr S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → isOK (tags-fs S Γ fs) → isOK (tags-ri S (ri*₀ A fs))
isOK-ri* {S} {Γ} A fs = subst isOK (trans (sym (cong (tags-fs S Γ) (ri-inv-ri*₀ A fs))) (tags-ri-inv₀ S (ri*₀ A fs)))

-- The first derivation exposes the decreasing argument for the admissible rules;
-- its equality with headAll fs keeps it tied to the whole premise tree.
gen⊗r-li : ∀ {S Γ Δ B} (A : Fma)
  → (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  → (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → headAll fs ≡ f → - ∣ Δ ⊢ri B → S ∣ Γ ++ Δ ⊢li (A ⊗ B , tt)
gen⊗r-li A (Il f) fs e g = Il (gen⊗r-li A f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e)) g)
gen⊗r-li A (⊗l f) fs e g = ⊗l (gen⊗r-li A f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e)) g)
gen⊗r-li A (∨l f f') fs e g = ∨l (gen⊗r-li A f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e)) g) (gen⊗r-li A f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e)) g)
gen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g with check-focus {S} {Γ} fs
... | casepass (allpass gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (pass f)) gs)) e
... | k | refl = f2li (pass (gen⊗r-li A k gs d g))
gen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | case1 (all∧l₁ gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₁ f)) gs)) e
... | k | refl = f2li (∧l₁ (gen⊗r-li A k gs d g))
gen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | case2 (all∧l₂ gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₂ f)) gs)) e
... | k | refl = f2li (∧l₂ (gen⊗r-li A k gs d g))
gen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | case⊸l (all⊸l {Γ' = Λ} h gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (⊸l (++ass Λ) h f)) gs)) e
... | k | refl = f2li (⊸l (++ass Λ) h (gen⊗r-li A k gs d g))
gen⊗r-li {Γ = Γ} A (f2li {S} f) fs e g | caseok ok = f2li (⊗r refl (ri*₀ {Γ = Γ} A fs) g (isOK-ri* A fs ok))

gen∨r₁-li : ∀ {S Γ B} (A : Fma)
  → (f : S ∣ Γ ++ proj₁ (head (impconj [] A)) ⊢li proj₂ (head (impconj [] A)))
  → (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A))
  → headAll fs ≡ f → S ∣ Γ ⊢li (A ∨ B , tt)
gen∨r₁-li A (Il f) fs e = Il (gen∨r₁-li A f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e)))
gen∨r₁-li A (⊗l f) fs e = ⊗l (gen∨r₁-li A f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e)))
gen∨r₁-li A (∨l f f') fs e = ∨l (gen∨r₁-li A f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e))) (gen∨r₁-li A f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e)))
gen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e with check-focus {S} {Γ} fs
... | casepass (allpass gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (pass f)) gs)) e
... | k | refl = f2li (pass (gen∨r₁-li A k gs d))
gen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | case1 (all∧l₁ gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₁ f)) gs)) e
... | k | refl = f2li (∧l₁ (gen∨r₁-li A k gs d))
gen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | case2 (all∧l₂ gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₂ f)) gs)) e
... | k | refl = f2li (∧l₂ (gen∨r₁-li A k gs d))
gen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | case⊸l (all⊸l {Γ' = Λ} h gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (⊸l (++ass Λ) h f)) gs)) e
... | k | refl = f2li (⊸l refl h (gen∨r₁-li A k gs d))
gen∨r₁-li {Γ = Γ} A (f2li {S} f) fs e | caseok ok = f2li (∨r₁ (ri*₀ {Γ = Γ} A fs) (isOK-ri* A fs ok))

gen∨r₂-li : ∀ {S Γ A} (B : Fma)
  → (f : S ∣ Γ ++ proj₁ (head (impconj [] B)) ⊢li proj₂ (head (impconj [] B)))
  → (fs : All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] B))
  → headAll fs ≡ f → S ∣ Γ ⊢li (A ∨ B , tt)
gen∨r₂-li B (Il f) fs e = Il (gen∨r₂-li B f (Il-inv-fs fs) (trans (headAll-map Il-inv fs) (cong Il-inv e)))
gen∨r₂-li B (⊗l f) fs e = ⊗l (gen∨r₂-li B f (⊗l-inv-fs fs) (trans (headAll-map ⊗l-inv fs) (cong ⊗l-inv e)))
gen∨r₂-li B (∨l f f') fs e = ∨l (gen∨r₂-li B f (∨l-inv-fs₁ fs) (trans (headAll-map ∨l-inv₁ fs) (cong ∨l-inv₁ e))) (gen∨r₂-li B f' (∨l-inv-fs₂ fs) (trans (headAll-map ∨l-inv₂ fs) (cong ∨l-inv₂ e)))
gen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e with check-focus {S} {Γ} fs
... | casepass (allpass gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (pass f)) gs)) e
... | k | refl = f2li (pass (gen∨r₂-li B k gs d))
gen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | case1 (all∧l₁ gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₁ f)) gs)) e
... | k | refl = f2li (∧l₁ (gen∨r₂-li B k gs d))
gen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | case2 (all∧l₂ gs refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (∧l₂ f)) gs)) e
... | k | refl = f2li (∧l₂ (gen∨r₂-li B k gs d))
gen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | case⊸l (all⊸l {Γ' = Λ} h gs refl refl refl) with headAll gs in d | trans (sym (headAll-map (λ f → f2li (⊸l (++ass Λ) h f)) gs)) e
... | k | refl = f2li (⊸l refl h (gen∨r₂-li B k gs d))
gen∨r₂-li {Γ = Γ} B (f2li {S} f) fs e | caseok ok = f2li (∨r₂ (ri*₀ {Γ = Γ} B fs) (isOK-ri* B fs ok))

⊗r-ri : ∀ {S Γ Δ A B} → S ∣ Γ ⊢ri A → - ∣ Δ ⊢ri B → S ∣ Γ ++ Δ ⊢ri A ⊗ B
⊗r-ri {Γ = Γ} {A = A} f g = let fs = ri-inv {Γ = Γ} f in li2ri (gen⊗r-li A (headAll fs) fs refl g)

∨r₁-ri : ∀ {S Γ A B} → S ∣ Γ ⊢ri A → S ∣ Γ ⊢ri A ∨ B
∨r₁-ri {Γ = Γ} {A = A} f = let fs = ri-inv {Γ = Γ} f in li2ri (gen∨r₁-li A (headAll fs) fs refl)

∨r₂-ri : ∀ {S Γ A B} → S ∣ Γ ⊢ri B → S ∣ Γ ⊢ri A ∨ B
∨r₂-ri {Γ = Γ} {B = B} f = let fs = ri-inv {Γ = Γ} f in li2ri (gen∨r₂-li B (headAll fs) fs refl)

ax-ri : ∀ {A} → just A ∣ [] ⊢ri A
ax-ri {` X} = li2ri (f2li ax)
ax-ri {I} = Il-ri Ir-ri
ax-ri {A ⊗ B} = ⊗l-ri (⊗r-ri ax-ri (pass-ri ax-ri))
ax-ri {A ⊸ B} = ⊸r (⊸l-ri (pass-ri ax-ri) ax-ri)
ax-ri {A ∧ B} = ∧r (∧l₁-ri ax-ri) (∧l₂-ri ax-ri)
ax-ri {A ∨ B} = ∨l-ri (∨r₁-ri ax-ri) (∨r₂-ri ax-ri)

focus : ∀ {S Γ A} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ri A
focus ax = ax-ri
focus (pass f) = pass-ri (focus f)
focus Ir = Ir-ri
focus (Il f) = Il-ri (focus f)
focus (⊗l f) = ⊗l-ri (focus f)
focus (⊗r f g) = ⊗r-ri (focus f) (focus g)
focus (⊸r f) = ⊸r (focus f)
focus (⊸l f g) = ⊸l-ri (focus f) (focus g)
focus (∧r f g) = ∧r (focus f) (focus g)
focus (∧l₁ f) = ∧l₁-ri (focus f)
focus (∧l₂ f) = ∧l₂-ri (focus f)
focus (∨r₁ f) = ∨r₁-ri (focus f)
focus (∨r₂ f) = ∨r₂-ri (focus f)
focus (∨l f g) = ∨l-ri (focus f) (focus g)
