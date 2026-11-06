{-# OPTIONS --safe #-}

module Focus.EmbFocus (At : Set) where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
open import SeqCalc.ImplEq At
open import Focus.Tags
open import Focus.FocusedCalc At
open import Focus.Maps At

-- Embedding an admissible left rule agrees with the original rule.
emb∨l : {Γ : Cxt} {A B C : Fma}
  → (f : just A ∣ Γ ⊢ri C) (g : just B ∣ Γ ⊢ri C)
  → emb-ri (∨l-ri f g) ≗ ∨l (emb-ri f) (emb-ri g)
emb∨l (∧r f f₁) (∧r g g₁) = ∧r (emb∨l f g) (emb∨l f₁ g₁) ∙ ∧r∨l
emb∨l (li2ri {C = .(pos (` x , snd₁)) , snd} f) (li2ri {C = ` x , snd₁} f₁) = refl
emb∨l (li2ri {C = .(pos (I , snd₁)) , snd} f) (li2ri {C = I , snd₁} f₁) = refl
emb∨l (li2ri {C = .(pos (C ⊗ C₃ , snd₁)) , snd} f) (li2ri {C = C ⊗ C₃ , snd₁} f₁) = refl
emb∨l (li2ri {C = .(pos (C ∨ C₃ , snd₁)) , snd} f) (li2ri {C = C ∨ C₃ , snd₁} f₁) = refl

emb⊗l : {Γ : Cxt} {A B C : Fma}
  → (f : just A ∣ B ∷ Γ ⊢ri C)
  → emb-ri (⊗l-ri f) ≗ ⊗l (emb-ri f)
emb⊗l (∧r f g) = ∧r (emb⊗l f) (emb⊗l g) ∙ ∧r⊗l
emb⊗l (li2ri f) = refl

emb∧l₁ : {Γ : Cxt} {A B C : Fma}
  → (f : just A ∣ Γ ⊢ri C)
  → emb-ri (∧l₁-ri {B = B} f) ≗ ∧l₁ (emb-ri f)
emb∧l₁ (∧r f g) = ∧r (emb∧l₁ f) (emb∧l₁ g) ∙ ∧r∧l₁
emb∧l₁ (li2ri f) = refl

emb∧l₂ : {Γ : Cxt} {A B C : Fma}
  → (f : just B ∣ Γ ⊢ri C)
  → emb-ri (∧l₂-ri {A = A} f) ≗ ∧l₂ (emb-ri f)
emb∧l₂ (∧r f g) = ∧r (emb∧l₂ f) (emb∧l₂ g) ∙ ∧r∧l₂
emb∧l₂ (li2ri f) = refl

embpass : ∀ {Γ Δ A C} (p : Pick A Γ Δ) (f : just A ∣ Δ ⊢ri C)
  → emb-ri (pass-ri p f) ≗ pass p (emb-ri f)
embpass p (∧r f g) = ∧r (embpass p f) (embpass p g) ∙ ∧rpass p
embpass p (li2ri f) = refl

embIl : {Γ : Cxt} {C : Fma}
  → (f : - ∣ Γ ⊢ri C)
  → emb-ri (Il-ri f) ≗ Il (emb-ri f)
embIl (∧r f g) = ∧r (embIl f) (embIl g) ∙ ∧rIl
embIl (li2ri f) = refl


-- Move a common left rule through the right-invertible tree.
emb-∧r*-pass : ∀ {A Γ Δ} (p : Pick A Γ Δ) (D : Fma)
  (fs : All (λ C → just A ∣ Δ ⊢li C) (toTree D))
  → pass p (emb-ri (∧r*-ri D fs)) ≗ emb-ri (∧r*-ri D (f2li-fs (pass-f-fs p fs)))
emb-∧r*-pass p (` X) (leaf f) = refl
emb-∧r*-pass p I (leaf f) = refl
emb-∧r*-pass p (A ⊗ B) (leaf f) = refl
emb-∧r*-pass p (A ∨ B) (leaf f) = refl
emb-∧r*-pass p (D ∧ E) (node fs gs) =
  (~ ∧rpass p) ∙ ∧r (emb-∧r*-pass p D fs) (emb-∧r*-pass p E gs)

emb-∧r*-∧l₁ : ∀ {A B Γ} (D : Fma) (fs : All (λ C → just A ∣ Γ ⊢li C) (toTree D))
  → ∧l₁ {B = B} (emb-ri (∧r*-ri D fs)) ≗ emb-ri (∧r*-ri D (f2li-fs (∧l₁-f-fs {B = B} fs)))
emb-∧r*-∧l₁ (` X) (leaf (f)) = refl
emb-∧r*-∧l₁ I (leaf (f)) = refl
emb-∧r*-∧l₁ (A ⊗ B) (leaf (f)) = refl
emb-∧r*-∧l₁ (A ∨ B) (leaf (f)) = refl
emb-∧r*-∧l₁ {B = B} (D ∧ E) (node fs gs) = (~ ∧r∧l₁) ∙ ∧r (emb-∧r*-∧l₁ D fs) (emb-∧r*-∧l₁ E gs)

emb-∧r*-∧l₂ : ∀ {A B Γ} (D : Fma) (fs : All (λ C → just B ∣ Γ ⊢li C) (toTree D))
  → ∧l₂ {A = A} (emb-ri (∧r*-ri D fs)) ≗ emb-ri (∧r*-ri D (f2li-fs (∧l₂-f-fs {A = A} fs)))
emb-∧r*-∧l₂ (` X) (leaf (f)) = refl
emb-∧r*-∧l₂ I (leaf (f)) = refl
emb-∧r*-∧l₂ (A ⊗ B) (leaf (f)) = refl
emb-∧r*-∧l₂ (A ∨ B) (leaf (f)) = refl
emb-∧r*-∧l₂ {A = A} (D ∧ E) (node fs gs) = (~ ∧r∧l₂) ∙ ∧r (emb-∧r*-∧l₂ D fs) (emb-∧r*-∧l₂ E gs)

emb-∧r*-Il : ∀ {Γ} (D : Fma) (fs : All (λ C → just I ∣ Γ ⊢li C) (toTree D))
  → Il (emb-ri (∧r*-ri D (Il-inv-fs fs))) ≗ emb-ri (∧r*-ri D fs)
emb-∧r*-Il (` X) (leaf (Il f)) = refl
emb-∧r*-Il I (leaf (Il f)) = refl
emb-∧r*-Il (A ⊗ B) (leaf (Il f)) = refl
emb-∧r*-Il (A ∨ B) (leaf (Il f)) = refl
emb-∧r*-Il (D ∧ E) (node fs gs) = (~ ∧rIl) ∙ ∧r (emb-∧r*-Il D fs) (emb-∧r*-Il E gs)

emb-∧r*-⊗l : ∀ {A B Γ} (D : Fma) (fs : All (λ C → just (A ⊗ B) ∣ Γ ⊢li C) (toTree D))
  → ⊗l (emb-ri (∧r*-ri D (⊗l-inv-fs fs))) ≗ emb-ri (∧r*-ri D fs)
emb-∧r*-⊗l (` X) (leaf (⊗l f)) = refl
emb-∧r*-⊗l I (leaf (⊗l f)) = refl
emb-∧r*-⊗l (A ⊗ B) (leaf (⊗l f)) = refl
emb-∧r*-⊗l (A ∨ B) (leaf (⊗l f)) = refl
emb-∧r*-⊗l (D ∧ E) (node fs gs) = (~ ∧r⊗l) ∙ ∧r (emb-∧r*-⊗l D fs) (emb-∧r*-⊗l E gs)

emb-∧r*-∨l : ∀ {A B Γ} (D : Fma) (fs : All (λ C → just (A ∨ B) ∣ Γ ⊢li C) (toTree D))
  → ∨l (emb-ri (∧r*-ri D (∨l-inv-fs₁ fs))) (emb-ri (∧r*-ri D (∨l-inv-fs₂ fs))) ≗ emb-ri (∧r*-ri D fs)
emb-∧r*-∨l (` X) (leaf (∨l f g)) = refl
emb-∧r*-∨l I (leaf (∨l f g)) = refl
emb-∧r*-∨l (A ⊗ B) (leaf (∨l f g)) = refl
emb-∧r*-∨l (A ∨ B) (leaf (∨l f g)) = refl
emb-∧r*-∨l (D ∧ E) (node fs gs) = (~ ∧r∨l) ∙ ∧r (emb-∧r*-∨l D fs) (emb-∧r*-∨l E gs)

-- Embedding an admissible right introduction recovers the original rule
-- up to ≗. The proof follows the same LView recursion as normalization.
emb⊗r-li : ∀ {S Γ Δ Ξ} (v : LView S Γ) {A B : Fma}
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) (p : Part Γ Δ Ξ) (g : - ∣ Δ ⊢ri B)
  → emb-li (⊗r-li v fs p g) ≗ ⊗r p (emb-ri (∧r*-ri A fs)) (emb-ri g)
emb⊗r-li-irr : ∀ {S} {i : isIrr S} {Γ Δ Ξ} (v : LView S Γ) {A B : Fma}
  (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) (ch : CheckFocus {S , i} fs)
  (p : Part Γ Δ Ξ) (g : - ∣ Δ ⊢ri B)
  → emb-f (⊗r-li-irr v fs ch p g) ≗ ⊗r p (emb-ri (∧r*-ri A fs)) (emb-ri g)

emb⊗r-li atom fs p g = emb⊗r-li-irr atom fs (check-focus fs) p g
emb⊗r-li empty fs p g = emb⊗r-li-irr empty fs (check-focus fs) p g
emb⊗r-li (pass v) fs p g = emb⊗r-li-irr (pass v) fs (check-focus fs) p g
emb⊗r-li (∧l v w) fs p g = emb⊗r-li-irr (∧l v w) fs (check-focus fs) p g
emb⊗r-li (Il v) fs p g =
  Il (emb⊗r-li v (Il-inv-fs fs) p g) ∙ (~ ⊗rIl p) ∙ ⊗r p (emb-∧r*-Il _ fs) refl
emb⊗r-li (⊗l v) fs p g =
  ⊗l (emb⊗r-li v (⊗l-inv-fs fs) (left p) g) ∙ (~ ⊗r⊗l p) ∙ ⊗r p (emb-∧r*-⊗l _ fs) refl
emb⊗r-li (∨l v w) fs p g =
  ∨l (emb⊗r-li v (∨l-inv-fs₁ fs) p g) (emb⊗r-li w (∨l-inv-fs₂ fs) p g) ∙
  (~ ⊗r∨l p) ∙ ⊗r p (emb-∧r*-∨l _ fs) refl

emb⊗r-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl refl)) p g =
  ∧l₁ (emb⊗r-li v gs p g) ∙ (~ ⊗r∧l₁ p) ∙ ⊗r p (emb-∧r*-∧l₁ _ gs) refl
emb⊗r-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl refl)) p g =
  ∧l₂ (emb⊗r-li w gs p g) ∙ (~ ⊗r∧l₂ p) ∙ ⊗r p (emb-∧r*-∧l₂ _ gs) refl
emb⊗r-li-irr (pass v) fs (casepass (allPass q gs refl refl)) p g =
  pass (proj₁ (proj₂ (pull-left p q)))
    (emb⊗r-li (v q) gs (proj₂ (proj₂ (pull-left p q))) g) ∙
  (~ ⊗rpass p q) ∙ ⊗r p (emb-∧r*-pass q _ gs) refl
emb⊗r-li-irr empty fs (casepass (allPass () gs refl refl)) p g
emb⊗r-li-irr atom fs (caseok ok) p g = refl
emb⊗r-li-irr empty fs (caseok ok) p g = refl
emb⊗r-li-irr (pass v) fs (caseok ok) p g = refl
emb⊗r-li-irr (∧l v w) fs (caseok ok) p g = refl

emb⊗r : ∀ {S Γ Δ Ξ A B} (p : Part Γ Δ Ξ)
  (f : S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → emb-ri (⊗r-ri p f g) ≗ ⊗r p (emb-ri f) (emb-ri g)
emb⊗r {S} {Γ} p f g =
  emb⊗r-li (view-ant S Γ) (∧r*-ri-inv f) p g ∙
  ⊗r p (≡to≗ (cong emb-ri (∧r*∧r*-ri-inv f))) refl

emb∨r₁-li : {S : Stp} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A))
  → emb-li (∨r₁-li v {B = B} fs) ≗ ∨r₁ (emb-ri (∧r*-ri A fs))
emb∨r₁-li-irr : {S : Stp} {i : isIrr S} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) (c : CheckFocus {S , i} fs)
  → emb-f (∨r₁-li-irr v {B = B} fs c) ≗ ∨r₁ (emb-ri (∧r*-ri A fs))

emb∨r₁-li atom fs = emb∨r₁-li-irr atom fs (check-focus fs)
emb∨r₁-li empty fs = emb∨r₁-li-irr empty fs (check-focus fs)
emb∨r₁-li (pass v) fs = emb∨r₁-li-irr (pass v) fs (check-focus fs)
emb∨r₁-li (∧l v w) fs = emb∨r₁-li-irr (∧l v w) fs (check-focus fs)
emb∨r₁-li (Il v) fs =
  Il (emb∨r₁-li v (Il-inv-fs fs)) ∙ (~ ∨r₁Il) ∙ ∨r₁ (emb-∧r*-Il _ fs)
emb∨r₁-li (⊗l v) fs =
  ⊗l (emb∨r₁-li v (⊗l-inv-fs fs)) ∙ (~ ∨r₁⊗l) ∙ ∨r₁ (emb-∧r*-⊗l _ fs)
emb∨r₁-li (∨l v w) fs =
  ∨l (emb∨r₁-li v (∨l-inv-fs₁ fs)) (emb∨r₁-li w (∨l-inv-fs₂ fs)) ∙ (~ ∨r₁∨l) ∙ ∨r₁ (emb-∧r*-∨l _ fs)

emb∨r₁-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl refl)) =
  ∧l₁ (emb∨r₁-li v gs) ∙ (~ ∨r₁∧l₁) ∙ ∨r₁ (emb-∧r*-∧l₁ _ gs)
emb∨r₁-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl refl)) =
  ∧l₂ (emb∨r₁-li w gs) ∙ (~ ∨r₁∧l₂) ∙ ∨r₁ (emb-∧r*-∧l₂ _ gs)
emb∨r₁-li-irr (pass v) fs (casepass (allPass q gs refl refl)) =
  pass q (emb∨r₁-li (v q) gs) ∙ (~ ∨r₁pass q) ∙ ∨r₁ (emb-∧r*-pass q _ gs)
emb∨r₁-li-irr empty fs (casepass (allPass () gs refl refl))
emb∨r₁-li-irr atom fs (caseok ok) = refl
emb∨r₁-li-irr empty fs (caseok ok) = refl
emb∨r₁-li-irr (pass v) fs (caseok ok) = refl
emb∨r₁-li-irr (∧l v w) fs (caseok ok) = refl

emb∨r₁ : {S : Stp} {Γ : Cxt} {A B : Fma} (f : S ∣ Γ ⊢ri A)
  → emb-ri (∨r₁-ri {B = B} f) ≗ ∨r₁ (emb-ri f)
emb∨r₁ {S} {Γ} f =
  emb∨r₁-li (view-ant S Γ) (∧r*-ri-inv f)
  ∙ ∨r₁ (≡to≗ (cong emb-ri (∧r*∧r*-ri-inv f)))

emb∨r₂-li : {S : Stp} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree B))
  → emb-li (∨r₂-li v {A = A} fs) ≗ ∨r₂ (emb-ri (∧r*-ri B fs))
emb∨r₂-li-irr : {S : Stp} {i : isIrr S} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree B)) (c : CheckFocus {S , i} fs)
  → emb-f (∨r₂-li-irr v {A = A} fs c) ≗ ∨r₂ (emb-ri (∧r*-ri B fs))

emb∨r₂-li atom fs = emb∨r₂-li-irr atom fs (check-focus fs)
emb∨r₂-li empty fs = emb∨r₂-li-irr empty fs (check-focus fs)
emb∨r₂-li (pass v) fs = emb∨r₂-li-irr (pass v) fs (check-focus fs)
emb∨r₂-li (∧l v w) fs = emb∨r₂-li-irr (∧l v w) fs (check-focus fs)
emb∨r₂-li (Il v) fs =
  Il (emb∨r₂-li v (Il-inv-fs fs)) ∙ (~ ∨r₂Il) ∙ ∨r₂ (emb-∧r*-Il _ fs)
emb∨r₂-li (⊗l v) fs =
  ⊗l (emb∨r₂-li v (⊗l-inv-fs fs)) ∙ (~ ∨r₂⊗l) ∙ ∨r₂ (emb-∧r*-⊗l _ fs)
emb∨r₂-li (∨l v w) fs =
  ∨l (emb∨r₂-li v (∨l-inv-fs₁ fs)) (emb∨r₂-li w (∨l-inv-fs₂ fs)) ∙ (~ ∨r₂∨l) ∙ ∨r₂ (emb-∧r*-∨l _ fs)

emb∨r₂-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl refl)) =
  ∧l₁ (emb∨r₂-li v gs) ∙ (~ ∨r₂∧l₁) ∙ ∨r₂ (emb-∧r*-∧l₁ _ gs)
emb∨r₂-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl refl)) =
  ∧l₂ (emb∨r₂-li w gs) ∙ (~ ∨r₂∧l₂) ∙ ∨r₂ (emb-∧r*-∧l₂ _ gs)
emb∨r₂-li-irr (pass v) fs (casepass (allPass q gs refl refl)) =
  pass q (emb∨r₂-li (v q) gs) ∙ (~ ∨r₂pass q) ∙ ∨r₂ (emb-∧r*-pass q _ gs)
emb∨r₂-li-irr empty fs (casepass (allPass () gs refl refl))
emb∨r₂-li-irr atom fs (caseok ok) = refl
emb∨r₂-li-irr empty fs (caseok ok) = refl
emb∨r₂-li-irr (pass v) fs (caseok ok) = refl
emb∨r₂-li-irr (∧l v w) fs (caseok ok) = refl

emb∨r₂ : {S : Stp} {Γ : Cxt} {A B : Fma} (f : S ∣ Γ ⊢ri B)
  → emb-ri (∨r₂-ri {A = A} f) ≗ ∨r₂ (emb-ri f)
emb∨r₂ {S} {Γ} f =
  emb∨r₂-li (view-ant S Γ) (∧r*-ri-inv f)
  ∙ ∨r₂ (≡to≗ (cong emb-ri (∧r*∧r*-ri-inv f)))

-- Expanded identities are equivalent to the original axiom by η-conversion.
embax : {D : Fma}
  → emb-ri (ax-ri {C = D}) ≗ ax
embax {` x} = refl
embax {I} = ~ axI
embax {D1 ⊗ D2} =
  emb⊗l (⊗r-ri (right done) ax-ri (pass-ri here ax-ri)) ∙
  ⊗l (emb⊗r (right done) ax-ri (pass-ri here ax-ri)) ∙
  ⊗l (⊗r (right done) embax (embpass here ax-ri ∙ pass here embax)) ∙ (~ ax⊗)
embax {D1 ∧ D2} = ∧r (emb∧l₁ ax-ri) (emb∧l₂ ax-ri) ∙ (∧r (∧l₁ (embax {D = D1})) (∧l₂ (embax {D = D2})) ∙ (~ ax∧))
embax {D1 ∨ D2} = emb∨l (∨r₁-ri ax-ri) (∨r₂-ri ax-ri) ∙ (∨l (emb∨r₁ ax-ri) (emb∨r₂ ax-ri) ∙ (∨l (∨r₁ embax) (∨r₂ embax) ∙ (~ ax∨)))

-- Every derivation is equivalent to the embedding of its focused normal form.
-- Apply the rule lemmas above and recurse on the original derivation.
embfocus : {S : Stp} {Γ : Cxt} {C : Fma}
  → (f : S ∣ Γ ⊢ C)
  → emb-ri (focus f) ≗ f
embfocus ax = embax
embfocus (pass p f) = embpass p (focus f) ∙ pass p (embfocus f)
embfocus Ir = refl
embfocus (Il f) = embIl (focus f) ∙ Il (embfocus f)
embfocus (⊗r p f g) = emb⊗r p (focus f) (focus g) ∙ ⊗r p (embfocus f) (embfocus g)
embfocus (⊗l f) = emb⊗l (focus f) ∙ ⊗l (embfocus f)
embfocus (∧r f g) = ∧r (embfocus f) (embfocus g)
embfocus (∧l₁ f) = emb∧l₁ (focus f) ∙ ∧l₁ (embfocus f)
embfocus (∧l₂ f) = emb∧l₂ (focus f) ∙ ∧l₂ (embfocus f)
embfocus (∨r₁ f) = emb∨r₁ (focus f) ∙ ∨r₁ (embfocus f)
embfocus (∨r₂ f) = emb∨r₂ (focus f) ∙ ∨r₂ (embfocus f)
embfocus (∨l f g) = emb∨l (focus f) (focus g) ∙ ∨l (embfocus f) (embfocus g)
