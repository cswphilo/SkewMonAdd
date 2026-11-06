{-# OPTIONS --safe #-}

module Focus.WellDef (At : Set) where

open import Data.List
import Data.Nat
open import Data.Maybe hiding (map)
open import Data.Product hiding (map)
open import Data.Unit using (tt)
open import Data.Empty
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
import SeqCalc.ImplEq At as I
open I using (_∣_⊢_; _≗_)
open import Focus.Tags
open import Focus.FocusedCalc At
open import Focus.Maps At

-- The admissible right rules depend only on the antecedent, not on the
-- particular LView witnessing its possible left decompositions.
∨r₁-li-view : ∀ {S Γ A B} (v w : LView S Γ)
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A))
  → ∨r₁-li v {B = B} fs ≡ ∨r₁-li w fs
∨r₁-li-irr-view : ∀ {S} {i : isIrr S} { Γ A B} (v w : LView S Γ)
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) (ch : CheckFocus {S , i} fs)
  → ∨r₁-li-irr v {B = B} fs ch ≡ ∨r₁-li-irr w fs ch

∨r₁-li-view atom atom fs = cong f2li (∨r₁-li-irr-view atom atom fs (check-focus fs))
∨r₁-li-view empty empty fs = cong f2li (∨r₁-li-irr-view empty empty fs (check-focus fs))
∨r₁-li-view empty (pass w) fs = cong f2li (∨r₁-li-irr-view empty (pass w) fs (check-focus fs))
∨r₁-li-view (pass v) empty fs = cong f2li (∨r₁-li-irr-view (pass v) empty fs (check-focus fs))
∨r₁-li-view (pass v) (pass w) fs = cong f2li (∨r₁-li-irr-view (pass v) (pass w) fs (check-focus fs))
∨r₁-li-view (∧l v₁ v₂) (∧l w₁ w₂) fs = cong f2li (∨r₁-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (check-focus fs))
∨r₁-li-view (Il v) (Il w) fs = cong Il (∨r₁-li-view v w (Il-inv-fs fs))
∨r₁-li-view (⊗l v) (⊗l w) fs = cong ⊗l (∨r₁-li-view v w (⊗l-inv-fs fs))
∨r₁-li-view (∨l v₁ v₂) (∨l w₁ w₂) fs = cong₂ ∨l
  (∨r₁-li-view v₁ w₁ (∨l-inv-fs₁ fs))
  (∨r₁-li-view v₂ w₂ (∨l-inv-fs₂ fs))

∨r₁-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (case1 (all∧l₁ gs refl eqf)) =
  cong ∧l₁ (∨r₁-li-view v₁ w₁ gs)
∨r₁-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (case2 (all∧l₂ gs refl eqf)) =
  cong ∧l₂ (∨r₁-li-view v₂ w₂ gs)
∨r₁-li-irr-view (pass v) (pass w) fs (casepass (allPass q gs refl eqf)) =
  cong (pass q) (∨r₁-li-view (v q) (w q) gs)
∨r₁-li-irr-view empty w fs (casepass (allPass () gs refl eqf))
∨r₁-li-irr-view (pass v) empty fs (casepass (allPass () gs refl eqf))
∨r₁-li-irr-view atom atom fs (caseok ok) = refl
∨r₁-li-irr-view empty empty fs (caseok ok) = refl
∨r₁-li-irr-view empty (pass w) fs (caseok ok) = refl
∨r₁-li-irr-view (pass v) empty fs (caseok ok) = refl
∨r₁-li-irr-view (pass v) (pass w) fs (caseok ok) = refl
∨r₁-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (caseok ok) = refl

∨r₂-li-view : ∀ {S Γ A B} (v w : LView S Γ)
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree B))
  → ∨r₂-li v {A = A} fs ≡ ∨r₂-li w fs
∨r₂-li-irr-view : ∀ {S} {i : isIrr S} { Γ A B} (v w : LView S Γ)
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree B)) (ch : CheckFocus {S , i} fs)
  → ∨r₂-li-irr v {A = A} fs ch ≡ ∨r₂-li-irr w fs ch

∨r₂-li-view atom atom fs = cong f2li (∨r₂-li-irr-view atom atom fs (check-focus fs))
∨r₂-li-view empty empty fs = cong f2li (∨r₂-li-irr-view empty empty fs (check-focus fs))
∨r₂-li-view empty (pass w) fs = cong f2li (∨r₂-li-irr-view empty (pass w) fs (check-focus fs))
∨r₂-li-view (pass v) empty fs = cong f2li (∨r₂-li-irr-view (pass v) empty fs (check-focus fs))
∨r₂-li-view (pass v) (pass w) fs = cong f2li (∨r₂-li-irr-view (pass v) (pass w) fs (check-focus fs))
∨r₂-li-view (∧l v₁ v₂) (∧l w₁ w₂) fs = cong f2li (∨r₂-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (check-focus fs))
∨r₂-li-view (Il v) (Il w) fs = cong Il (∨r₂-li-view v w (Il-inv-fs fs))
∨r₂-li-view (⊗l v) (⊗l w) fs = cong ⊗l (∨r₂-li-view v w (⊗l-inv-fs fs))
∨r₂-li-view (∨l v₁ v₂) (∨l w₁ w₂) fs = cong₂ ∨l
  (∨r₂-li-view v₁ w₁ (∨l-inv-fs₁ fs))
  (∨r₂-li-view v₂ w₂ (∨l-inv-fs₂ fs))

∨r₂-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (case1 (all∧l₁ gs refl eqf)) =
  cong ∧l₁ (∨r₂-li-view v₁ w₁ gs)
∨r₂-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (case2 (all∧l₂ gs refl eqf)) =
  cong ∧l₂ (∨r₂-li-view v₂ w₂ gs)
∨r₂-li-irr-view (pass v) (pass w) fs (casepass (allPass q gs refl eqf)) =
  cong (pass q) (∨r₂-li-view (v q) (w q) gs)
∨r₂-li-irr-view empty w fs (casepass (allPass () gs refl eqf))
∨r₂-li-irr-view (pass v) empty fs (casepass (allPass () gs refl eqf))
∨r₂-li-irr-view atom atom fs (caseok ok) = refl
∨r₂-li-irr-view empty empty fs (caseok ok) = refl
∨r₂-li-irr-view empty (pass w) fs (caseok ok) = refl
∨r₂-li-irr-view (pass v) empty fs (caseok ok) = refl
∨r₂-li-irr-view (pass v) (pass w) fs (caseok ok) = refl
∨r₂-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (caseok ok) = refl

⊗r-li-view : ∀ {S Γ Δ Ξ A B} (v w : LView S Γ)
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) (p : Part Γ Δ Ξ) (g : - ∣ Δ ⊢ri B)
  → ⊗r-li v fs p g ≡ ⊗r-li w fs p g
⊗r-li-irr-view : ∀ {S} {i : isIrr S} { Γ Δ Ξ A B} (v w : LView S Γ)
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) (ch : CheckFocus {S , i} fs) (p : Part Γ Δ Ξ) (g : - ∣ Δ ⊢ri B)
  → ⊗r-li-irr v fs ch p g ≡ ⊗r-li-irr w fs ch p g

⊗r-li-view atom atom fs p g = cong f2li (⊗r-li-irr-view atom atom fs (check-focus fs) p g)
⊗r-li-view empty empty fs p g = cong f2li (⊗r-li-irr-view empty empty fs (check-focus fs) p g)
⊗r-li-view empty (pass w) fs p g = cong f2li (⊗r-li-irr-view empty (pass w) fs (check-focus fs) p g)
⊗r-li-view (pass v) empty fs p g = cong f2li (⊗r-li-irr-view (pass v) empty fs (check-focus fs) p g)
⊗r-li-view (pass v) (pass w) fs p g = cong f2li (⊗r-li-irr-view (pass v) (pass w) fs (check-focus fs) p g)
⊗r-li-view (∧l v₁ v₂) (∧l w₁ w₂) fs p g = cong f2li (⊗r-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (check-focus fs) p g)
⊗r-li-view (Il v) (Il w) fs p g = cong Il (⊗r-li-view v w (Il-inv-fs fs) p g)
⊗r-li-view (⊗l v) (⊗l w) fs p g = cong ⊗l (⊗r-li-view v w (⊗l-inv-fs fs) (left p) g)
⊗r-li-view (∨l v₁ v₂) (∨l w₁ w₂) fs p g = cong₂ ∨l
  (⊗r-li-view v₁ w₁ (∨l-inv-fs₁ fs) p g)
  (⊗r-li-view v₂ w₂ (∨l-inv-fs₂ fs) p g)

⊗r-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (case1 (all∧l₁ gs refl eqf)) p g =
  cong ∧l₁ (⊗r-li-view v₁ w₁ gs p g)
⊗r-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (case2 (all∧l₂ gs refl eqf)) p g =
  cong ∧l₂ (⊗r-li-view v₂ w₂ gs p g)
⊗r-li-irr-view (pass v) (pass w) fs (casepass (allPass q gs refl eqf)) p g =
  cong (pass (proj₁ (proj₂ (pull-left p q))))
    (⊗r-li-view (v q) (w q) gs (proj₂ (proj₂ (pull-left p q))) g)
⊗r-li-irr-view empty w fs (casepass (allPass () gs refl eqf)) p g
⊗r-li-irr-view (pass v) empty fs (casepass (allPass () gs refl eqf)) p g
⊗r-li-irr-view atom atom fs (caseok ok) p g = refl
⊗r-li-irr-view empty empty fs (caseok ok) p g = refl
⊗r-li-irr-view empty (pass w) fs (caseok ok) p g = refl
⊗r-li-irr-view (pass v) empty fs (caseok ok) p g = refl
⊗r-li-irr-view (pass v) (pass w) fs (caseok ok) p g = refl
⊗r-li-irr-view (∧l v₁ v₂) (∧l w₁ w₂) fs (caseok ok) p g = refl

-- Left rules acting on trees of positive conclusions.
Il-fs : ∀ {Γ Φ} → All (λ C → - ∣ Γ ⊢li C) Φ → All (λ C → just I ∣ Γ ⊢li C) Φ
Il-fs = mapAll Il

⊗l-fs : ∀ {A B Γ Φ} → All (λ C → just A ∣ B ∷ Γ ⊢li C) Φ → All (λ C → just (A ⊗ B) ∣ Γ ⊢li C) Φ
⊗l-fs = mapAll ⊗l

∨l-fs : ∀ {A B Γ Φ} → All (λ C → just A ∣ Γ ⊢li C) Φ → All (λ C → just B ∣ Γ ⊢li C) Φ → All (λ C → just (A ∨ B) ∣ Γ ⊢li C) Φ
∨l-fs = map2All ∨l

-- Exposing right-invertible premises commutes with each left rule.
∧r*invpass-ri : ∀ {Γ Δ A D} (p : Pick A Γ Δ) (f : just A ∣ Δ ⊢ri D)
  → ∧r*-ri-inv (pass-ri p f) ≡ f2li-fs (pass-f-fs p (∧r*-ri-inv f))
∧r*invpass-ri p (∧r f g) = cong₂ node (∧r*invpass-ri p f) (∧r*invpass-ri p g)
∧r*invpass-ri p (li2ri {C = (` X , _)} f) = refl
∧r*invpass-ri p (li2ri {C = (I , _)} f) = refl
∧r*invpass-ri p (li2ri {C = (A ⊗ B , _)} f) = refl
∧r*invpass-ri p (li2ri {C = (A ∨ B , _)} f) = refl

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
check-focus-allpass-node : ∀ {A Γ Δ Φ Ψ} (p : Pick A Γ Δ)
  (fs : All (λ C → just A ∣ Δ ⊢li C) Φ)
  (gs : All (λ C → just A ∣ Δ ⊢li C) Ψ)
  → check-focus-node (f2li-fs (pass-f-fs p fs)) (f2li-fs (pass-f-fs p gs))
      (casepass (allPass p fs refl refl)) (casepass (allPass p gs refl refl))
    ≡ casepass (allPass p (node fs gs) refl refl)
check-focus-allpass-node p fs gs with pick-index p Data.Nat.≟ pick-index p
... | no neq = ⊥-elim (neq refl)
... | yes refl with same-pick p p refl
... | refl = refl

check-focus-allpass : ∀ {A Γ Δ Φ} (p : Pick A Γ Δ) (fs : All (λ C → just A ∣ Δ ⊢li C) Φ)
  → check-focus (f2li-fs (pass-f-fs p fs)) ≡ casepass (allPass p fs refl refl)
check-focus-allpass p (leaf f) = refl
check-focus-allpass p (node fs gs) = trans
  (cong₂ (check-focus-node (f2li-fs (pass-f-fs p fs)) (f2li-fs (pass-f-fs p gs)))
    (check-focus-allpass p fs) (check-focus-allpass p gs))
  (check-focus-allpass-node p fs gs)

check-focus-all∧l₁ : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ)
  → check-focus (f2li-fs (∧l₁-f-fs {B = B} fs)) ≡ case1 (all∧l₁ fs refl refl)
check-focus-all∧l₁ (leaf f) = refl
check-focus-all∧l₁ {B = B} (node fs gs) =
  cong₂ (check-focus-node (f2li-fs (∧l₁-f-fs {B = B} fs)) (f2li-fs (∧l₁-f-fs {B = B} gs)))
    (check-focus-all∧l₁ {B = B} fs) (check-focus-all∧l₁ {B = B} gs)

check-focus-all∧l₂ : ∀ {A B Γ Φ} (fs : All (λ C → just B ∣ Γ ⊢li C) Φ)
  → check-focus (f2li-fs (∧l₂-f-fs {A = A} fs)) ≡ case2 (all∧l₂ fs refl refl)
check-focus-all∧l₂ (leaf f) = refl
check-focus-all∧l₂ {A = A} (node fs gs) =
  cong₂ (check-focus-node (f2li-fs (∧l₂-f-fs {A = A} fs)) (f2li-fs (∧l₂-f-fs {A = A} gs)))
    (check-focus-all∧l₂ {A = A} fs) (check-focus-all∧l₂ {A = A} gs)

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

-- A pass view with canonical children is convenient for comparing a
-- shared pass with a right introduction; view independence justifies it.
pass-view : (Γ : Cxt) → LView - Γ
pass-view Γ = pass (λ {A} {Δ} p → view-ant (just A) Δ)

∨r₁pass-li : ∀ {Γ Ω X D E} (q : Pick X Γ Ω)
  (fs : All (λ C → just X ∣ Ω ⊢li C) (toTree D))
  → ∨r₁-li (pass-view Γ) {B = E} (f2li-fs (pass-f-fs q fs))
    ≡ f2li (pass q (∨r₁-li (view-ant (just X) Ω) fs))
∨r₁pass-li {Γ} q fs =
  cong (λ ch → f2li (∨r₁-li-irr (pass-view Γ) (f2li-fs (pass-f-fs q fs)) ch))
    (check-focus-allpass q fs)

∨r₂pass-li : ∀ {Γ Ω X D E} (q : Pick X Γ Ω)
  (fs : All (λ C → just X ∣ Ω ⊢li C) (toTree E))
  → ∨r₂-li (pass-view Γ) {A = D} (f2li-fs (pass-f-fs q fs))
    ≡ f2li (pass q (∨r₂-li (view-ant (just X) Ω) fs))
∨r₂pass-li {Γ} q fs =
  cong (λ ch → f2li (∨r₂-li-irr (pass-view Γ) (f2li-fs (pass-f-fs q fs)) ch))
    (check-focus-allpass q fs)

⊗rpass-li : ∀ {Γ Δ Ξ Ω X D E} (p : Part Γ Δ Ξ) (q : Pick X Γ Ω)
  (fs : All (λ C → just X ∣ Ω ⊢li C) (toTree D)) (g : - ∣ Δ ⊢ri E)
  → ⊗r-li (pass-view Γ) (f2li-fs (pass-f-fs q fs)) p g
    ≡ f2li (pass (proj₁ (proj₂ (pull-left p q)))
        (⊗r-li (view-ant (just X) Ω) fs (proj₂ (proj₂ (pull-left p q))) g))
⊗rpass-li {Γ} p q fs g =
  cong (λ ch → f2li (⊗r-li-irr (pass-view Γ) (f2li-fs (pass-f-fs q fs)) ch p g))
    (check-focus-allpass q fs)

-- The admissible right introductions respect the left-rule conversions.
⊗rpass-ri : ∀ {Γ Δ Ξ Ω X D E} (p : Part Γ Δ Ξ) (q : Pick X Γ Ω)
  (f : just X ∣ Ω ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri p (pass-ri q f) g
    ≡ pass-ri (proj₁ (proj₂ (pull-left p q)))
        (⊗r-ri (proj₂ (proj₂ (pull-left p q))) f g)
⊗rpass-ri {Γ} p q f g = trans
  (cong (λ fs → li2ri (⊗r-li (view-ant - Γ) fs p g)) (∧r*invpass-ri q f))
  (trans (cong li2ri (⊗r-li-view (view-ant - Γ) (pass-view Γ)
      (f2li-fs (pass-f-fs q (∧r*-ri-inv f))) p g))
    (cong li2ri (⊗rpass-li p q (∧r*-ri-inv f) g)))

⊗rIl-ri : {Γ Δ Ξ : Cxt} {D E : Fma} (p : Part Γ Δ Ξ) (f : - ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri p (Il-ri f) g ≡ Il-ri (⊗r-ri p f g)
⊗rIl-ri {Γ = Γ} p f g = trans
  (cong (λ fs → li2ri (⊗r-li (view-ant (just I) Γ) fs p g))
    (∧r*invIl-ri f))
  (cong (λ fs → li2ri (Il (⊗r-li (view-ant - Γ) fs p g)))
    (Il-inv-fsIl-fs (∧r*-ri-inv f)))

⊗r⊗l-ri : {Γ Δ Ξ : Cxt} {A B D E : Fma} (p : Part Γ Δ Ξ) (f : just A ∣ B ∷ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri p (⊗l-ri f) g ≡ ⊗l-ri (⊗r-ri (left p) f g)
⊗r⊗l-ri {Γ = Γ} {A = A} {B = B} p f g = trans
  (cong (λ fs → li2ri (⊗r-li (view-ant (just (A ⊗ B)) Γ) fs p g))
    (∧r*inv⊗l-ri f))
  (cong (λ fs → li2ri (⊗l (⊗r-li (view-ant (just A) (B ∷ Γ)) fs (left p) g)))
    (⊗l-inv-fs⊗l-fs (∧r*-ri-inv f)))

⊗r∧l₁-ri : {Γ Δ Ξ : Cxt} {A B D E : Fma} (p : Part Γ Δ Ξ) (f : just A ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri p (∧l₁-ri {B = B} f) g ≡ ∧l₁-ri (⊗r-ri p f g)
⊗r∧l₁-ri {Γ = Γ} {A = A} {B = B} p f g = trans
  (cong (λ fs → li2ri (⊗r-li (view-ant (just (A ∧ B)) Γ) fs p g))
    (∧r*inv∧l₁-ri {B = B} f))
  (cong (λ ch → li2ri (f2li (⊗r-li-irr (view-ant (just (A ∧ B)) Γ)
      (f2li-fs (∧l₁-f-fs {B = B} (∧r*-ri-inv f))) ch p g)))
    (check-focus-all∧l₁ {B = B} (∧r*-ri-inv f)))

⊗r∧l₂-ri : {Γ Δ Ξ : Cxt} {A B D E : Fma} (p : Part Γ Δ Ξ) (f : just B ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri p (∧l₂-ri {A = A} f) g ≡ ∧l₂-ri (⊗r-ri p f g)
⊗r∧l₂-ri {Γ = Γ} {A = A} {B = B} p f g = trans
  (cong (λ fs → li2ri (⊗r-li (view-ant (just (A ∧ B)) Γ) fs p g))
    (∧r*inv∧l₂-ri {A = A} f))
  (cong (λ ch → li2ri (f2li (⊗r-li-irr (view-ant (just (A ∧ B)) Γ)
      (f2li-fs (∧l₂-f-fs {A = A} (∧r*-ri-inv f))) ch p g)))
    (check-focus-all∧l₂ {A = A} (∧r*-ri-inv f)))

⊗r∨l-ri : {Γ Δ Ξ : Cxt} {A B D E : Fma} (p : Part Γ Δ Ξ) (f : just A ∣ Γ ⊢ri D) (f' : just B ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri p (∨l-ri f f') g ≡ ∨l-ri (⊗r-ri p f g) (⊗r-ri p f' g)
⊗r∨l-ri {Γ = Γ} {A = A} {B = B} p f f′ g = trans
  (cong (λ fs → li2ri (⊗r-li (view-ant (just (A ∨ B)) Γ) fs p g))
    (∧r*-inv∨l-ri f f′))
  (cong₂ (λ fs gs → li2ri (∨l
      (⊗r-li (view-ant (just A) Γ) fs p g)
      (⊗r-li (view-ant (just B) Γ) gs p g)))
    (∨l-inv-fs₁∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f′))
    (∨l-inv-fs₂∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f′)))

∨r₁pass-ri : ∀ {Γ Ω X D E} (q : Pick X Γ Ω) (f : just X ∣ Ω ⊢ri D)
  → ∨r₁-ri {B = E} (pass-ri q f) ≡ pass-ri q (∨r₁-ri {B = E} f)
∨r₁pass-ri {Γ} q f = trans
  (cong (λ fs → li2ri (∨r₁-li (view-ant - Γ) fs)) (∧r*invpass-ri q f))
  (trans (cong li2ri (∨r₁-li-view (view-ant - Γ) (pass-view Γ)
      (f2li-fs (pass-f-fs q (∧r*-ri-inv f)))))
    (cong li2ri (∨r₁pass-li q (∧r*-ri-inv f))))

∨r₁Il-ri : {Γ : Cxt} {D E : Fma} (f : - ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (Il-ri f) ≡ Il-ri (∨r₁-ri {B = E} f)
∨r₁Il-ri {Γ = Γ} f = trans
  (cong (λ fs → li2ri (∨r₁-li (view-ant (just I) Γ) fs))
    (∧r*invIl-ri f))
  (cong (λ fs → li2ri (Il (∨r₁-li (view-ant - Γ) fs)))
    (Il-inv-fsIl-fs (∧r*-ri-inv f)))

∨r₁⊗l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ B ∷ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (⊗l-ri f) ≡ ⊗l-ri (∨r₁-ri {B = E} f)
∨r₁⊗l-ri {Γ = Γ} {A = A} {B = B} f = trans
  (cong (λ fs → li2ri (∨r₁-li (view-ant (just (A ⊗ B)) Γ) fs))
    (∧r*inv⊗l-ri f))
  (cong (λ fs → li2ri (⊗l (∨r₁-li (view-ant (just A) (B ∷ Γ)) fs)))
    (⊗l-inv-fs⊗l-fs (∧r*-ri-inv f)))

∨r₁∧l₁-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₁-ri {B = E} f)
∨r₁∧l₁-ri {Γ = Γ} {A = A} {B = B} f = trans
  (cong (λ fs → li2ri (∨r₁-li (view-ant (just (A ∧ B)) Γ) fs))
    (∧r*inv∧l₁-ri {B = B} f))
  (cong (λ ch → li2ri (f2li (∨r₁-li-irr (view-ant (just (A ∧ B)) Γ)
      (f2li-fs (∧l₁-f-fs {B = B} (∧r*-ri-inv f))) ch)))
    (check-focus-all∧l₁ {B = B} (∧r*-ri-inv f)))

∨r₁∧l₂-ri : {Γ : Cxt} {A B D E : Fma} (f : just B ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₁-ri {B = E} f)
∨r₁∧l₂-ri {Γ = Γ} {A = A} {B = B} f = trans
  (cong (λ fs → li2ri (∨r₁-li (view-ant (just (A ∧ B)) Γ) fs))
    (∧r*inv∧l₂-ri {A = A} f))
  (cong (λ ch → li2ri (f2li (∨r₁-li-irr (view-ant (just (A ∧ B)) Γ)
      (f2li-fs (∧l₂-f-fs {A = A} (∧r*-ri-inv f))) ch)))
    (check-focus-all∧l₂ {A = A} (∧r*-ri-inv f)))

∨r₁∨l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri D) (f' : just B ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∨l-ri f f') ≡ ∨l-ri (∨r₁-ri {B = E} f) (∨r₁-ri {B = E} f')
∨r₁∨l-ri {Γ = Γ} {A = A} {B = B} f f′ = trans
  (cong (λ fs → li2ri (∨r₁-li (view-ant (just (A ∨ B)) Γ) fs))
    (∧r*-inv∨l-ri f f′))
  (cong₂ (λ fs gs → li2ri (∨l
      (∨r₁-li (view-ant (just A) Γ) fs)
      (∨r₁-li (view-ant (just B) Γ) gs)))
    (∨l-inv-fs₁∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f′))
    (∨l-inv-fs₂∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f′)))

∨r₂pass-ri : ∀ {Γ Ω X D E} (q : Pick X Γ Ω) (f : just X ∣ Ω ⊢ri E)
  → ∨r₂-ri {A = D} (pass-ri q f) ≡ pass-ri q (∨r₂-ri {A = D} f)
∨r₂pass-ri {Γ} q f = trans
  (cong (λ fs → li2ri (∨r₂-li (view-ant - Γ) fs)) (∧r*invpass-ri q f))
  (trans (cong li2ri (∨r₂-li-view (view-ant - Γ) (pass-view Γ)
      (f2li-fs (pass-f-fs q (∧r*-ri-inv f)))))
    (cong li2ri (∨r₂pass-li q (∧r*-ri-inv f))))

∨r₂Il-ri : {Γ : Cxt} {D E : Fma} (f : - ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (Il-ri f) ≡ Il-ri (∨r₂-ri {A = D} f)
∨r₂Il-ri {Γ = Γ} f = trans
  (cong (λ fs → li2ri (∨r₂-li (view-ant (just I) Γ) fs))
    (∧r*invIl-ri f))
  (cong (λ fs → li2ri (Il (∨r₂-li (view-ant - Γ) fs)))
    (Il-inv-fsIl-fs (∧r*-ri-inv f)))

∨r₂⊗l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ B ∷ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (⊗l-ri f) ≡ ⊗l-ri (∨r₂-ri {A = D} f)
∨r₂⊗l-ri {Γ = Γ} {A = A} {B = B} f = trans
  (cong (λ fs → li2ri (∨r₂-li (view-ant (just (A ⊗ B)) Γ) fs))
    (∧r*inv⊗l-ri f))
  (cong (λ fs → li2ri (⊗l (∨r₂-li (view-ant (just A) (B ∷ Γ)) fs)))
    (⊗l-inv-fs⊗l-fs (∧r*-ri-inv f)))

∨r₂∧l₁-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₂-ri {A = D} f)
∨r₂∧l₁-ri {Γ = Γ} {A = A} {B = B} f = trans
  (cong (λ fs → li2ri (∨r₂-li (view-ant (just (A ∧ B)) Γ) fs))
    (∧r*inv∧l₁-ri {B = B} f))
  (cong (λ ch → li2ri (f2li (∨r₂-li-irr (view-ant (just (A ∧ B)) Γ)
      (f2li-fs (∧l₁-f-fs {B = B} (∧r*-ri-inv f))) ch)))
    (check-focus-all∧l₁ {B = B} (∧r*-ri-inv f)))

∨r₂∧l₂-ri : {Γ : Cxt} {A B D E : Fma} (f : just B ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₂-ri {A = D} f)
∨r₂∧l₂-ri {Γ = Γ} {A = A} {B = B} f = trans
  (cong (λ fs → li2ri (∨r₂-li (view-ant (just (A ∧ B)) Γ) fs))
    (∧r*inv∧l₂-ri {A = A} f))
  (cong (λ ch → li2ri (f2li (∨r₂-li-irr (view-ant (just (A ∧ B)) Γ)
      (f2li-fs (∧l₂-f-fs {A = A} (∧r*-ri-inv f))) ch)))
    (check-focus-all∧l₂ {A = A} (∧r*-ri-inv f)))

∨r₂∨l-ri : {Γ : Cxt} {A B D E : Fma} (f : just A ∣ Γ ⊢ri E) (f' : just B ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∨l-ri f f') ≡ ∨l-ri (∨r₂-ri {A = D} f) (∨r₂-ri {A = D} f')
∨r₂∨l-ri {Γ = Γ} {A = A} {B = B} f f′ = trans
  (cong (λ fs → li2ri (∨r₂-li (view-ant (just (A ∨ B)) Γ) fs))
    (∧r*-inv∨l-ri f f′))
  (cong₂ (λ fs gs → li2ri (∨l
      (∨r₂-li (view-ant (just A) Γ) fs)
      (∨r₂-li (view-ant (just B) Γ) gs)))
    (∨l-inv-fs₁∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f′))
    (∨l-inv-fs₂∨l-fs (∧r*-ri-inv f) (∧r*-ri-inv f′)))

-- Normalization identifies both sides of every implicit equation.
-- Exchange equations follow from their derivations in SeqCalc.ImplEq;
-- no separate exchange-coherence assumptions are needed.
eqfocus : ∀ {S Γ C} {f g : S ∣ Γ ⊢ C} → f ≗ g → focus f ≡ focus g
eqfocus I.refl = refl
eqfocus (I.~ eq) = sym (eqfocus eq)
eqfocus (eq I.∙ eq′) = trans (eqfocus eq) (eqfocus eq′)
eqfocus (I.pass p eq) = cong (pass-ri p) (eqfocus eq)
eqfocus (I.Il eq) = cong Il-ri (eqfocus eq)
eqfocus (I.⊗l eq) = cong ⊗l-ri (eqfocus eq)
eqfocus (I.⊗r p eq eq′) = cong₂ (⊗r-ri p) (eqfocus eq) (eqfocus eq′)
eqfocus (I.∧r eq eq′) = cong₂ ∧r (eqfocus eq) (eqfocus eq′)
eqfocus (I.∧l₁ eq) = cong ∧l₁-ri (eqfocus eq)
eqfocus (I.∧l₂ eq) = cong ∧l₂-ri (eqfocus eq)
eqfocus (I.∨r₁ eq) = cong ∨r₁-ri (eqfocus eq)
eqfocus (I.∨r₂ eq) = cong ∨r₂-ri (eqfocus eq)
eqfocus (I.∨l eq eq′) = cong₂ ∨l-ri (eqfocus eq) (eqfocus eq′)
eqfocus I.axI = refl
eqfocus I.ax⊗ = refl
eqfocus I.ax∧ = refl
eqfocus I.ax∨ = refl
eqfocus (I.⊗rpass p q {f = f} {g}) = ⊗rpass-ri p q (focus f) (focus g)
eqfocus (I.⊗rIl p {f = f} {g}) = ⊗rIl-ri p (focus f) (focus g)
eqfocus (I.⊗r⊗l p {f = f} {g}) = ⊗r⊗l-ri p (focus f) (focus g)
eqfocus (I.⊗r∧l₁ p {f = f} {g}) = ⊗r∧l₁-ri p (focus f) (focus g)
eqfocus (I.⊗r∧l₂ p {f = f} {g}) = ⊗r∧l₂-ri p (focus f) (focus g)
eqfocus (I.⊗r∨l p {f = f} {f′} {g}) = ⊗r∨l-ri p (focus f) (focus f′) (focus g)
eqfocus (I.∧rpass p) = refl
eqfocus I.∧rIl = refl
eqfocus I.∧r⊗l = refl
eqfocus I.∧r∧l₁ = refl
eqfocus I.∧r∧l₂ = refl
eqfocus I.∧r∨l = refl
eqfocus (I.∨r₁pass q {f = f}) = ∨r₁pass-ri q (focus f)
eqfocus (I.∨r₂pass q {f = f}) = ∨r₂pass-ri q (focus f)
eqfocus (I.∨r₁Il {f = f}) = ∨r₁Il-ri (focus f)
eqfocus (I.∨r₁⊗l {f = f}) = ∨r₁⊗l-ri (focus f)
eqfocus (I.∨r₁∧l₁ {f = f}) = ∨r₁∧l₁-ri (focus f)
eqfocus (I.∨r₁∧l₂ {f = f}) = ∨r₁∧l₂-ri (focus f)
eqfocus (I.∨r₁∨l {f = f} {g}) = ∨r₁∨l-ri (focus f) (focus g)
eqfocus (I.∨r₂Il {f = f}) = ∨r₂Il-ri (focus f)
eqfocus (I.∨r₂⊗l {f = f}) = ∨r₂⊗l-ri (focus f)
eqfocus (I.∨r₂∧l₁ {f = f}) = ∨r₂∧l₁-ri (focus f)
eqfocus (I.∨r₂∧l₂ {f = f}) = ∨r₂∧l₂-ri (focus f)
eqfocus (I.∨r₂∨l {f = f} {g}) = ∨r₂∨l-ri (focus f) (focus g)
