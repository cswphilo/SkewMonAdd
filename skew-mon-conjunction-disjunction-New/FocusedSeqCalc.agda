{-# OPTIONS --safe #-}
module FocusedSeqCalc (At : Set) where
open import Data.List
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Formulae At
open import Tags
open import Data.Unit
open import Data.Empty
open import Utilities

-- The three phases mutually refer to one another.
-- ri introduces right conjunctions; li decomposes the stoup; f chooses a rule.

-- ri = right invertible
data _∣_⊢ri_ : Stp → Cxt → Fma → Set


-- li = left invertible
data _∣_⊢li_ : Stp → Cxt → Pos → Set

-- f = focusing
data _∣_⊢f_ : Irr → Cxt → Pos → Set
-- Compute tags from derivations instead of indexing a separate tagged calculus.
tags-ri : (S : Irr) {Γ : Cxt} {C : Fma} → irr S ∣ Γ ⊢ri C → List Tag
tag-f : {S : Irr} {Γ : Cxt} {C : Pos} → S ∣ Γ ⊢f C → Tag

data _∣_⊢ri_ where
  ∧r : {S : Stp} {Γ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ⊢ri A) (g : S ∣ Γ ⊢ri B)
    ---------------------------------------
    →          S ∣ Γ ⊢ri A ∧ B
  li2ri : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    ------------------------
    →      S ∣ Γ ⊢ri pos C

data _∣_⊢li_ where
  ⊗l : {Γ : Cxt} {A B : Fma} {C : Pos}
       (f : just A ∣ B ∷ Γ ⊢li C) →
    -------------------------------------
          just (A ⊗ B) ∣ Γ ⊢li C
  Il : {Γ : Cxt} {C : Pos}
       (f : - ∣ Γ ⊢li C) →
    -------------------------
            just I ∣ Γ ⊢li C
  ∨l : {Γ : Cxt} {A B : Fma} {C : Pos}
      (f : just A ∣ Γ ⊢li C) (g : just B ∣ Γ ⊢li C) →
      -----------------------------------------
           just (A ∨ B) ∣ Γ ⊢li C
  f2li : {S : Irr} {Γ : Cxt} {C : Pos}
        (f : S ∣ Γ ⊢f C) →
        --------------------------
             irr S ∣ Γ ⊢li C

data _∣_⊢f_ where
  ax : {X : At} →
       (just (` X) , _) ∣ [] ⊢f (` X , _)
  Ir : (- , _) ∣ [] ⊢f (I , _)
  pass : {Γ : Cxt} {A : Fma} {C : Pos}
         (f : just A ∣ Γ ⊢li C) →
         --------------------------------
              (- , _) ∣ A ∷ Γ ⊢f C
  -- A right introduction is allowed only when its left premise has valid tags.
  -- The equality records the context split explicitly.
  ⊗r : {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma} →
         (eq : Γ' ≡ Γ ++ Δ) →
         (f : irr S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B) →
         (ok : isOK (tags-ri S f)) →
         -----------------------------------
              S ∣ Γ' ⊢f (A ⊗ B , _)
  ∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) →
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C
  ∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ⊢li C) →
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C
  -- Both disjunction introductions impose the same validity condition.
  ∨r₁ : {S : Irr} {Γ : Cxt} {A B : Fma} →
        (f : irr S ∣ Γ ⊢ri A) →
        (ok : isOK (tags-ri S f)) →
        -------------------------
             S ∣ Γ ⊢f (A  ∨ B , _)
  ∨r₂ : {S : Irr} {Γ : Cxt} {A B : Fma} →
        (f : irr S ∣ Γ ⊢ri B) →
        (ok : isOK (tags-ri S f)) →
        -------------------------
             S ∣ Γ ⊢f (A  ∨ B , _)


tags-ri S (∧r f g) = tags-ri S f ++ tags-ri S g
tags-ri (just (` X) , _) (li2ri (f2li f)) = [ tag-f f ]
tags-ri (just (A ∧ B) , _) (li2ri (f2li f)) = [ tag-f f ]
tags-ri (- , _) (li2ri (f2li f)) = [ tag-f f ]

tag-f ax = R
tag-f Ir = R
tag-f (pass f) = P
tag-f (⊗r eq f g ok) = R
tag-f (∧l₁ f) = C₁
tag-f (∧l₂ f) = C₂
tag-f (∨r₁ f ok) = R
tag-f (∨r₂ f ok) = R

-- Operations on trees of positive conclusions.
f2li-fs : ∀ {S Γ Φ} → All (λ C → S ∣ Γ ⊢f C) Φ → All (λ C → irr S ∣ Γ ⊢li C) Φ
f2li-fs = mapAll f2li

∧l₁-f-fs : ∀ {A B Γ Φ} → All (λ C → just A ∣ Γ ⊢li C) Φ → All (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C) Φ
∧l₁-f-fs = mapAll ∧l₁

∧l₂-f-fs : ∀ {A B Γ Φ} → All (λ C → just B ∣ Γ ⊢li C) Φ → All (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C) Φ
∧l₂-f-fs = mapAll ∧l₂

pass-f-fs : ∀ {A Γ Φ} → All (λ C → just A ∣ Γ ⊢li C) Φ → All (λ C → (- , _) ∣ A ∷ Γ ⊢f C) Φ
pass-f-fs = mapAll pass

⊗l-inv-fs : ∀ {A B Γ Φ} → All (λ C → just (A ⊗ B) ∣ Γ ⊢li C) Φ → All (λ C → just A ∣ B ∷ Γ ⊢li C) Φ
⊗l-inv-fs {A} {B} = mapAll inv
  where
  inv : ∀ {C} → just (A ⊗ B) ∣ _ ⊢li C → just A ∣ B ∷ _ ⊢li C
  inv (⊗l f) = f

Il-inv-fs : ∀ {Γ Φ} → All (λ C → just I ∣ Γ ⊢li C) Φ → All (λ C → - ∣ Γ ⊢li C) Φ
Il-inv-fs = mapAll inv
  where
  inv : ∀ {C} → just I ∣ _ ⊢li C → - ∣ _ ⊢li C
  inv (Il f) = f

∨l-inv-fs₁ : ∀ {A B Γ Φ} → All (λ C → just (A ∨ B) ∣ Γ ⊢li C) Φ → All (λ C → just A ∣ Γ ⊢li C) Φ
∨l-inv-fs₁ {A} {B} = mapAll inv
  where
  inv : ∀ {C} → just (A ∨ B) ∣ _ ⊢li C → just A ∣ _ ⊢li C
  inv (∨l f g) = f

∨l-inv-fs₂ : ∀ {A B Γ Φ} → All (λ C → just (A ∨ B) ∣ Γ ⊢li C) Φ → All (λ C → just B ∣ Γ ⊢li C) Φ
∨l-inv-fs₂ {A} {B} = mapAll inv
  where
  inv : ∀ {C} → just (A ∨ B) ∣ _ ⊢li C → just B ∣ _ ⊢li C
  inv (∨l f g) = g

-- Collect tags from the positive leaves of a tree of left-phase derivations.
tags-fs : (S : Irr) {Γ : Cxt} {Φ : Tree Pos} → All (λ C → irr S ∣ Γ ⊢li C) Φ → List Tag
tags-fs S (leaf (f2li f)) = [ tag-f f ]
tags-fs S (node fs fs') = tags-fs S fs ++ tags-fs S fs'

nonempty-tags-fs : ∀ {S Γ Φ} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) → tags-fs S fs ≡ [] → ⊥
nonempty-tags-fs (leaf (f2li f)) ()
nonempty-tags-fs (node fs gs) eq = nonempty-tags-fs fs (empty++1 _ eq)

-- Uniform projections and pass produce uniform tag lists; these facts
-- rule out the corresponding CheckFocus cases when isOK holds.
tags-onlyC₁ : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ) → onlyC₁ (tags-fs _ (f2li-fs (∧l₁-f-fs {A = A} {B = B} fs)))
tags-onlyC₁ (leaf f) = tt
tags-onlyC₁ (node fs gs) = onlyC₁++ (tags-fs _ (f2li-fs (∧l₁-f-fs fs))) (tags-onlyC₁ fs) (tags-onlyC₁ gs)

tags-onlyC₂ : ∀ {A B Γ Φ} (fs : All (λ C → just B ∣ Γ ⊢li C) Φ) → onlyC₂ (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} {B = B} fs)))
tags-onlyC₂ (leaf f) = tt
tags-onlyC₂ (node fs gs) = onlyC₂++ (tags-fs _ (f2li-fs (∧l₂-f-fs fs))) (tags-onlyC₂ fs) (tags-onlyC₂ gs)

tags-onlyP : ∀ {A Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ)
  → onlyP (tags-fs _ (f2li-fs (pass-f-fs fs)))
tags-onlyP (leaf f) = tt
tags-onlyP (node fs gs) = onlyP++ (tags-fs _ (f2li-fs (pass-f-fs fs))) (tags-onlyP fs) (tags-onlyP gs)

-- Normal-form side conditions are propositions, so they do not affect
-- equality when the premises of a focused right rule are equal.
∨r₁eq : ∀ {S Γ A B} {f f' : irr S ∣ Γ ⊢ri A} → f ≡ f'
  → {ok : isOK (tags-ri S f)} {ok' : isOK (tags-ri S f')}
  → ∨r₁ {B = B} f ok ≡ ∨r₁ f' ok'
∨r₁eq {S} {f = f} refl = cong (∨r₁ _) (isProp-isOK (tags-ri S f))

∨r₂eq : ∀ {S Γ A B} {f f' : irr S ∣ Γ ⊢ri B} → f ≡ f'
  → {ok : isOK (tags-ri S f)} {ok' : isOK (tags-ri S f')}
  → ∨r₂ {A = A} f ok ≡ ∨r₂ f' ok'
∨r₂eq {S} {f = f} refl = cong (∨r₂ _) (isProp-isOK (tags-ri S f))

⊗req : ∀ {S Γ Δ Γ' A B} {f f' : irr S ∣ Γ ⊢ri A} {g g' : - ∣ Δ ⊢ri B}
  → (eq : Γ' ≡ Γ ++ Δ) → f ≡ f' → g ≡ g'
  → {ok : isOK (tags-ri S f)} {ok' : isOK (tags-ri S f')}
  → ⊗r eq f g ok ≡ ⊗r eq f' g' ok'
⊗req {S} {f = f} eq refl refl = cong (⊗r eq _ _) (isProp-isOK (tags-ri S f))
