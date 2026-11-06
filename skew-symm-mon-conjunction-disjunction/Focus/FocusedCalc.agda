{-# OPTIONS --safe #-}
module Focus.FocusedCalc (At : Set) where
open import Data.List
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Formulae At
open import Focus.Tags
open import Data.Unit using (⊤; tt)
open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.Empty
open import Utilities

-- Skew exchange is implicit in arbitrary pass selections and tensor
-- partitions. There is no exchange rule and no additional phase.
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
  -- Select an occurrence; retain the relative order of all others.
  pass : {Γ Δ : Cxt} {A : Fma} {C : Pos}
    → Pick A Γ Δ → just A ∣ Δ ⊢li C
    → (- , tt) ∣ Γ ⊢f C
  -- Split the conclusion into two order-preserving, possibly interleaved
  -- sublists. Every occurrence is assigned to exactly one premise.
  ⊗r : {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma}
    → (split : Part Γ Δ Γ')
    → (f : irr S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
    → (ok : isOK (tags-ri S f))
    → S ∣ Γ' ⊢f (A ⊗ B , tt)
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
tag-f (pass p f) = P (pick-index p)
tag-f (⊗r eq f g ok) = R
tag-f (∧l₁ f) = C₁
tag-f (∧l₂ f) = C₂
tag-f (∨r₁ f ok) = R
tag-f (∨r₂ f ok) = R

-- Inverses of the left-invertible rules on individual derivations.
⊗l-li-inv : ∀ {A B Γ C} → just (A ⊗ B) ∣ Γ ⊢li C → just A ∣ B ∷ Γ ⊢li C
⊗l-li-inv (⊗l f) = f

Il-li-inv : ∀ {Γ C} → just I ∣ Γ ⊢li C → - ∣ Γ ⊢li C
Il-li-inv (Il f) = f

∨l-li-inv₁ : ∀ {A B Γ C} → just (A ∨ B) ∣ Γ ⊢li C → just A ∣ Γ ⊢li C
∨l-li-inv₁ (∨l f g) = f

∨l-li-inv₂ : ∀ {A B Γ C} → just (A ∨ B) ∣ Γ ⊢li C → just B ∣ Γ ⊢li C
∨l-li-inv₂ (∨l f g) = g

-- Operations on trees of positive conclusions.
f2li-fs : ∀ {S Γ Φ} → All (λ C → S ∣ Γ ⊢f C) Φ → All (λ C → irr S ∣ Γ ⊢li C) Φ
f2li-fs = mapAll f2li

∧l₁-f-fs : ∀ {A B Γ Φ} → All (λ C → just A ∣ Γ ⊢li C) Φ → All (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C) Φ
∧l₁-f-fs = mapAll ∧l₁

∧l₂-f-fs : ∀ {A B Γ Φ} → All (λ C → just B ∣ Γ ⊢li C) Φ → All (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C) Φ
∧l₂-f-fs = mapAll ∧l₂

pass-f-fs : ∀ {A Γ Δ Φ} → Pick A Γ Δ
  → All (λ C → just A ∣ Δ ⊢li C) Φ
  → All (λ C → (- , tt) ∣ Γ ⊢f C) Φ
pass-f-fs p = mapAll (pass p)

⊗l-inv-fs : ∀ {A B Γ Φ} → All (λ C → just (A ⊗ B) ∣ Γ ⊢li C) Φ → All (λ C → just A ∣ B ∷ Γ ⊢li C) Φ
⊗l-inv-fs = mapAll ⊗l-li-inv

Il-inv-fs : ∀ {Γ Φ} → All (λ C → just I ∣ Γ ⊢li C) Φ → All (λ C → - ∣ Γ ⊢li C) Φ
Il-inv-fs = mapAll Il-li-inv

∨l-inv-fs₁ : ∀ {A B Γ Φ} → All (λ C → just (A ∨ B) ∣ Γ ⊢li C) Φ → All (λ C → just A ∣ Γ ⊢li C) Φ
∨l-inv-fs₁ = mapAll ∨l-li-inv₁

∨l-inv-fs₂ : ∀ {A B Γ Φ} → All (λ C → just (A ∨ B) ∣ Γ ⊢li C) Φ → All (λ C → just B ∣ Γ ⊢li C) Φ
∨l-inv-fs₂ = mapAll ∨l-li-inv₂

-- Collect tags from the positive leaves of a tree of left-phase derivations.
tags-fs : (S : Irr) {Γ : Cxt} {Φ : Tree Pos} → All (λ C → irr S ∣ Γ ⊢li C) Φ → List Tag
tags-fs S (leaf (f2li f)) = [ tag-f f ]
tags-fs S (node fs fs') = tags-fs S fs ++ tags-fs S fs'

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
  → (split : Part Γ Δ Γ') → f ≡ f' → g ≡ g'
  → {ok : isOK (tags-ri S f)} {ok' : isOK (tags-ri S f')}
  → ⊗r split f g ok ≡ ⊗r split f' g' ok'
⊗req {S} {f = f} split refl refl = cong (⊗r split _ _) (isProp-isOK (tags-ri S f))

-- Positive succedents have no right-invertible connective at their root.
ri2li : ∀ {S Γ} {C : Pos} → S ∣ Γ ⊢ri pos C → S ∣ Γ ⊢li C
ri2li {C = ` X , _} (li2ri f) = f
ri2li {C = I , _} (li2ri f) = f
ri2li {C = A ⊗ B , _} (li2ri f) = f
ri2li {C = A ∨ B , _} (li2ri f) = f


-- Trees with a common left choice have a uniform list of tags.
tags-onlyC₁ : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ)
  → onlyC₁ (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₁-f-fs fs)))
tags-onlyC₁ (leaf f) = tt
tags-onlyC₁ {B = B} (node fs gs) = onlyC₁++
  (tags-fs _ (f2li-fs (∧l₁-f-fs {B = B} fs))) (tags-onlyC₁ fs) (tags-onlyC₁ gs)

tags-onlyC₂ : ∀ {A B Γ Φ} (fs : All (λ C → just B ∣ Γ ⊢li C) Φ)
  → onlyC₂ (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₂-f-fs fs)))
tags-onlyC₂ (leaf f) = tt
tags-onlyC₂ {A = A} (node fs gs) = onlyC₂++
  (tags-fs _ (f2li-fs (∧l₂-f-fs {A = A} fs))) (tags-onlyC₂ fs) (tags-onlyC₂ gs)

tags-onlyP : ∀ {A Γ Δ Φ} (p : Pick A Γ Δ) (fs : All (λ C → just A ∣ Δ ⊢li C) Φ)
  → onlyP (pick-index p) (tags-fs (- , tt) (f2li-fs (pass-f-fs p fs)))
tags-onlyP p (leaf f) with pick-index p ≟ pick-index p
... | yes _ = tt
... | no neq = ⊥-elim (neq refl)
tags-onlyP p (node fs gs) = onlyP++ (pick-index p)
  (tags-fs _ (f2li-fs (pass-f-fs p fs))) (tags-onlyP p fs) (tags-onlyP p gs)

-- An irreducible stoup has no left-invertible rule at its root.
f2li-inv : ∀ {S Γ C} → irr S ∣ Γ ⊢li C → S ∣ Γ ⊢f C
f2li-inv {just (` X) , _} (f2li f) = f
f2li-inv {just (A ∧ B) , _} (f2li f) = f
f2li-inv { - , _} (f2li f) = f

tag-li : (S : Irr) {Γ : Cxt} {C : Pos} → irr S ∣ Γ ⊢li C → Tag
tag-li S f = tag-f (f2li-inv {S} f)

tags-ri-li : ∀ S {Γ C} (f : irr S ∣ Γ ⊢li C) → tags-ri S (li2ri f) ≡ [ tag-li S f ]
tags-ri-li (just (` X) , _) (f2li f) = refl
tags-ri-li (just (A ∧ B) , _) (f2li f) = refl
tags-ri-li (- , _) (f2li f) = refl

tag-li-f2li : ∀ S {Γ C} (f : S ∣ Γ ⊢f C) → tag-li S (f2li f) ≡ tag-f f
tag-li-f2li (just (` X) , _) f = refl
tag-li-f2li (just (A ∧ B) , _) f = refl
tag-li-f2li (- , _) f = refl
