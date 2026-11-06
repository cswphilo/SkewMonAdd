{-# OPTIONS --safe #-}

module Focus (At : Set) where

open import Data.List
open import Data.Unit
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
open import SeqCalc At
open import FocusedSeqCalc At
open import Tags

-- Rebuild a right-invertible derivation from its positive premises.
∧r*-ri : {S : Stp} {Γ : Cxt} (A : Fma) (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) → S ∣ Γ ⊢ri A
∧r*-ri (A ∧ B) (node fs gs) = ∧r (∧r*-ri A fs) (∧r*-ri B gs)
∧r*-ri (` X) (leaf f) = li2ri f
∧r*-ri I (leaf f) = li2ri f
∧r*-ri (A ⊗ B) (leaf f) = li2ri f
∧r*-ri (A ∨ B) (leaf f) = li2ri f

-- Expose those premises by inverting all right conjunctions.
∧r*-ri-inv : {S : Stp} {Γ : Cxt} {A : Fma} (f : S ∣ Γ ⊢ri A) → All (λ C → S ∣ Γ ⊢li C) (toTree A)
∧r*-ri-inv (∧r f g) = node (∧r*-ri-inv f) (∧r*-ri-inv g)
∧r*-ri-inv (li2ri {C = (` X , _)} f) = leaf f
∧r*-ri-inv (li2ri {C = (I , _)} f) = leaf f
∧r*-ri-inv (li2ri {C = (A ⊗ B , _)} f) = leaf f
∧r*-ri-inv (li2ri {C = (A ∨ B , _)} f) = leaf f

-- Rebuilding the exposed premises recovers the original derivation.
∧r*∧r*-ri-inv : {S : Stp} {Γ : Cxt} {A : Fma} (f : S ∣ Γ ⊢ri A) → ∧r*-ri A (∧r*-ri-inv f) ≡ f
∧r*∧r*-ri-inv (∧r f f') = cong₂ ∧r (∧r*∧r*-ri-inv f) (∧r*∧r*-ri-inv f')
∧r*∧r*-ri-inv (li2ri {C = (` X , _)} f) = refl
∧r*∧r*-ri-inv (li2ri {C = (I , _)} f) = refl
∧r*∧r*-ri-inv (li2ri {C = (A ⊗ B , _)} f) = refl
∧r*∧r*-ri-inv (li2ri {C = (A ∨ B , _)} f) = refl

-- Reconstruction preserves the tags used by the isOK side conditions.
tags-ri∧r*-ri : ∀ {S Γ} A (fs : All (λ C → irr S ∣ Γ ⊢li C) (toTree A))
   → tags-fs S fs ≡ tags-ri S (∧r*-ri A fs)
tags-ri∧r*-ri {just (` X) , _} (` Y) (leaf (f2li f)) = refl
tags-ri∧r*-ri {just (S ∧ T) , _} (` Y) (leaf (f2li f)) = refl
tags-ri∧r*-ri { - , _} (` Y) (leaf (f2li f)) = refl
tags-ri∧r*-ri {just (` X) , _} I (leaf (f2li f)) = refl
tags-ri∧r*-ri {just (S ∧ T) , _} I (leaf (f2li f)) = refl
tags-ri∧r*-ri { - , _} I (leaf (f2li f)) = refl
tags-ri∧r*-ri {just (` X) , _} (A ⊗ B) (leaf (f2li f)) = refl
tags-ri∧r*-ri {just (S ∧ T) , _} (A ⊗ B) (leaf (f2li f)) = refl
tags-ri∧r*-ri { - , _} (A ⊗ B) (leaf (f2li f)) = refl
tags-ri∧r*-ri (A ∧ B) (node fs gs) = cong₂ _++_ (tags-ri∧r*-ri A fs) (tags-ri∧r*-ri B gs)
tags-ri∧r*-ri {just (` X) , _} (A ∨ B) (leaf (f2li f)) = refl
tags-ri∧r*-ri {just (S ∧ T) , _} (A ∨ B) (leaf (f2li f)) = refl
tags-ri∧r*-ri { - , _} (A ∨ B) (leaf (f2li f)) = refl

-- Classify a tree of positive premises with an irreducible stoup.
-- Either every leaf ends in the same projection or pass, or its tags are valid.
-- The records retain the premises and equalities needed to move a shared rule.
record All∧l₁ {S : Irr} {Γ : Cxt} {Φ : Tree Pos} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) : Set where
  constructor all∧l₁
  field
    {A B} : Fma
    gs : All (λ C → just A ∣ Γ ⊢li C) Φ
    eqS : irr S ≡ just (A ∧ B)
    eqf : subst (λ x → All (λ P → x ∣ Γ ⊢li P) Φ) eqS fs ≡ f2li-fs (∧l₁-f-fs {B = B} gs)

record All∧l₂ {S : Irr} {Γ : Cxt} {Φ : Tree Pos} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) : Set where
  constructor all∧l₂
  field
    {A B} : Fma
    gs : All (λ C → just B ∣ Γ ⊢li C) Φ
    eqS : irr S ≡ just (A ∧ B)
    eqf : subst (λ x → All (λ P → x ∣ Γ ⊢li P) Φ) eqS fs ≡ f2li-fs (∧l₂-f-fs {A = A} gs)

record AllPass {S : Irr} {Γ : Cxt} {Φ : Tree Pos} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) : Set where
  constructor allPass
  field
    {A} : Fma
    {Δ} : Cxt
    gs : All (λ C → just A ∣ Δ ⊢li C) Φ
    eqS : irr S ≡ -
    eqΓ : Γ ≡ A ∷ Δ
    eqf : subst₂ (λ S Γ → All (λ C → S ∣ Γ ⊢li C) Φ) eqS eqΓ fs ≡ f2li-fs (pass-f-fs gs)

data CheckFocus {S : Irr} {Γ : Cxt} {Φ : Tree Pos} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) : Set where
  case1 : All∧l₁ {S} fs → CheckFocus fs
  case2 : All∧l₂ {S} fs → CheckFocus fs
  casepass : AllPass {S} fs → CheckFocus fs
  caseok : isOK (tags-fs S fs) → CheckFocus fs

open All∧l₁
open All∧l₂
open AllPass

check-focus : {S : Irr} {Γ : Cxt} {Φ : Tree Pos} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) → CheckFocus {S} fs
check-focus (leaf (f2li ax)) = caseok tt
check-focus (leaf (f2li Ir)) = caseok tt
check-focus (leaf (f2li (pass f))) = casepass (allPass (leaf f) refl refl refl)
check-focus (leaf (f2li (∧l₁ f))) = case1 (all∧l₁ (leaf f) refl refl)
check-focus (leaf (f2li (∧l₂ f))) = case2 (all∧l₂ (leaf f) refl refl)
check-focus (leaf (f2li (∨r₁ f ok))) = caseok tt
check-focus (leaf (f2li (∨r₂ f ok))) = caseok tt
check-focus (leaf (f2li (⊗r eq f g ok))) = caseok tt
check-focus {S} (node fs fs') with check-focus {S} fs | check-focus {S} fs'
... | case1 (all∧l₁ gs refl refl) | case1 (all∧l₁ gs' refl refl) = case1 (all∧l₁ (node gs gs') refl refl)
... | case1 (all∧l₁ gs refl refl) | case2 (all∧l₂ {A}{B} gs' refl refl) =
  caseok (isOKC₁++C₂ (tags-fs _ (f2li-fs (∧l₁-f-fs gs))) (tags-onlyC₁ gs) (tags-onlyC₂ gs')
                     (nonempty-tags-fs {S} (f2li-fs (∧l₁-f-fs gs)))
                     (nonempty-tags-fs {S} (f2li-fs (∧l₂-f-fs gs'))))
... | case2 (all∧l₂ gs refl refl) | case1 (all∧l₁ gs' refl refl) =
  caseok (isOKC₂++C₁ (tags-fs _ (f2li-fs (∧l₂-f-fs gs))) (tags-onlyC₂ gs) (tags-onlyC₁ gs')
                     (nonempty-tags-fs {S} (f2li-fs (∧l₂-f-fs gs)))
                     (nonempty-tags-fs {S} (f2li-fs (∧l₁-f-fs gs'))))
... | case2 (all∧l₂ gs refl refl) | case2 (all∧l₂ gs' refl refl) = case2 (all∧l₂ (node gs gs') refl refl)
... | casepass (allPass gs refl refl refl) | casepass (allPass gs' refl refl refl) = casepass (allPass (node gs gs') refl refl refl)
... | _ | caseok ok = caseok (isOK++2 (tags-fs _ fs) ok)
... | caseok ok | _ = caseok (isOK++1 (tags-fs _ fs) ok)

-- A finite view of all possible left decompositions of an antecedent.
-- Recursion on this view is structural even when pass moves a formula
-- into the stoup, or tensor-left moves one back into the context.
data LView : Stp → Cxt → Set where
  atom : ∀ {X Γ} → LView (just (` X)) Γ
  empty : LView - []
  pass : ∀ {A Γ} → LView (just A) Γ → LView - (A ∷ Γ)
  Il : ∀ {Γ} → LView - Γ → LView (just I) Γ
  ⊗l : ∀ {A B Γ} → LView (just A) (B ∷ Γ) → LView (just (A ⊗ B)) Γ
  ∧l : ∀ {A B Γ} → LView (just A) Γ → LView (just B) Γ → LView (just (A ∧ B)) Γ
  ∨l : ∀ {A B Γ} → LView (just A) Γ → LView (just B) Γ → LView (just (A ∨ B)) Γ

-- Build the view structurally on formulae and contexts.
view-fma : (A : Fma) {Γ : Cxt} → LView - Γ → LView (just A) Γ
view-fma (` X) v = atom
view-fma I v = Il v
view-fma (A ⊗ B) v = ⊗l (view-fma A (pass (view-fma B v)))
view-fma (A ∧ B) v = ∧l (view-fma A v) (view-fma B v)
view-fma (A ∨ B) v = ∨l (view-fma A v) (view-fma B v)

view-cxt : (Γ : Cxt) → LView - Γ
view-cxt [] = empty
view-cxt (A ∷ Γ) = pass (view-fma A (view-cxt Γ))

view-ant : (S : Stp) (Γ : Cxt) → LView S Γ
view-ant (just A) Γ = view-fma A (view-cxt Γ)
view-ant - Γ = view-cxt Γ

-- Admissible right introductions commute past invertible left rules and
-- any shared projection or pass. Otherwise check-focus supplies isOK.
-- Each helper recurses on LView to make termination structural.
∨r₁-li : {S : Stp} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) → S ∣ Γ ⊢li (A ∨ B , _)
∨r₁-li-irr : {S : Stp} {i : isIrr S} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) → CheckFocus {S , i} fs → (S , i) ∣ Γ ⊢f (A ∨ B , _)

∨r₁-li atom fs = f2li (∨r₁-li-irr atom fs (check-focus fs))
∨r₁-li empty fs = f2li (∨r₁-li-irr empty fs (check-focus fs))
∨r₁-li (pass v) fs = f2li (∨r₁-li-irr (pass v) fs (check-focus fs))
∨r₁-li (∧l v w) fs = f2li (∨r₁-li-irr (∧l v w) fs (check-focus fs))
∨r₁-li (Il v) fs = Il (∨r₁-li v (Il-inv-fs fs))
∨r₁-li (⊗l v) fs = ⊗l (∨r₁-li v (⊗l-inv-fs fs))
∨r₁-li (∨l v w) fs = ∨l (∨r₁-li v (∨l-inv-fs₁ fs)) (∨r₁-li w (∨l-inv-fs₂ fs))

∨r₁-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl eqf)) = ∧l₁ (∨r₁-li v gs)
∨r₁-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl eqf)) = ∧l₂ (∨r₁-li w gs)
∨r₁-li-irr (pass v) fs (casepass (allPass gs refl refl eqf)) = pass (∨r₁-li v gs)
∨r₁-li-irr v fs (caseok ok) = ∨r₁ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)

∨r₁-ri : {S : Stp} {Γ : Cxt} {A B : Fma} → S ∣ Γ ⊢ri A → S ∣ Γ ⊢ri A ∨ B
∨r₁-ri {S} {Γ} f = li2ri (∨r₁-li (view-ant S Γ) (∧r*-ri-inv f))

∨r₂-li : {S : Stp} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree B)) → S ∣ Γ ⊢li (A ∨ B , _)
∨r₂-li-irr : {S : Stp} {i : isIrr S} {Γ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree B)) → CheckFocus {S , i} fs → (S , i) ∣ Γ ⊢f (A ∨ B , _)

∨r₂-li atom fs = f2li (∨r₂-li-irr atom fs (check-focus fs))
∨r₂-li empty fs = f2li (∨r₂-li-irr empty fs (check-focus fs))
∨r₂-li (pass v) fs = f2li (∨r₂-li-irr (pass v) fs (check-focus fs))
∨r₂-li (∧l v w) fs = f2li (∨r₂-li-irr (∧l v w) fs (check-focus fs))
∨r₂-li (Il v) fs = Il (∨r₂-li v (Il-inv-fs fs))
∨r₂-li (⊗l v) fs = ⊗l (∨r₂-li v (⊗l-inv-fs fs))
∨r₂-li (∨l v w) fs = ∨l (∨r₂-li v (∨l-inv-fs₁ fs)) (∨r₂-li w (∨l-inv-fs₂ fs))

∨r₂-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl eqf)) = ∧l₁ (∨r₂-li v gs)
∨r₂-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl eqf)) = ∧l₂ (∨r₂-li w gs)
∨r₂-li-irr (pass v) fs (casepass (allPass gs refl refl eqf)) = pass (∨r₂-li v gs)
∨r₂-li-irr v fs (caseok ok) = ∨r₂ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)

∨r₂-ri : {S : Stp} {Γ : Cxt} {A B : Fma} → S ∣ Γ ⊢ri B → S ∣ Γ ⊢ri A ∨ B
∨r₂-ri {S} {Γ} f = li2ri (∨r₂-li (view-ant S Γ) (∧r*-ri-inv f))

⊗r-li : {S : Stp} {Γ Δ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) → (g : - ∣ Δ ⊢ri B) → S ∣ Γ ++ Δ ⊢li (A ⊗ B , _)
⊗r-li-irr : {S : Stp} {i : isIrr S} {Γ Δ : Cxt} (v : LView S Γ) {A B : Fma} (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) → CheckFocus {S , i} fs → (g : - ∣ Δ ⊢ri B) → (S , i) ∣ Γ ++ Δ ⊢f (A ⊗ B , _)

⊗r-li atom fs g = f2li (⊗r-li-irr atom fs (check-focus fs) g)
⊗r-li empty fs g = f2li (⊗r-li-irr empty fs (check-focus fs) g)
⊗r-li (pass v) fs g = f2li (⊗r-li-irr (pass v) fs (check-focus fs) g)
⊗r-li (∧l v w) fs g = f2li (⊗r-li-irr (∧l v w) fs (check-focus fs) g)
⊗r-li (Il v) fs g = Il (⊗r-li v (Il-inv-fs fs) g)
⊗r-li (⊗l v) fs g = ⊗l (⊗r-li v (⊗l-inv-fs fs) g)
⊗r-li (∨l v w) fs g = ∨l (⊗r-li v (∨l-inv-fs₁ fs) g) (⊗r-li w (∨l-inv-fs₂ fs) g)

⊗r-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl eqf)) g = ∧l₁ (⊗r-li v gs g)
⊗r-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl eqf)) g = ∧l₂ (⊗r-li w gs g)
⊗r-li-irr (pass v) fs (casepass (allPass gs refl refl eqf)) g = pass (⊗r-li v gs g)
⊗r-li-irr v fs (caseok ok) g = ⊗r refl (∧r*-ri _ fs) g (subst isOK (tags-ri∧r*-ri _ fs) ok)

⊗r-ri : {S : Stp} {Γ Δ : Cxt} {A B : Fma} → S ∣ Γ ⊢ri A → (g : - ∣ Δ ⊢ri B) → S ∣ Γ ++ Δ ⊢ri A ⊗ B
⊗r-ri {S} {Γ} f g = li2ri (⊗r-li (view-ant S Γ) (∧r*-ri-inv f) g)

-- The remaining sequent-calculus rules are admissible in phase ri.
Il-ri : {Γ : Cxt} {C : Fma}
        (f : - ∣ Γ ⊢ri C) →
    ------------------------
        just I ∣ Γ ⊢ri C
Il-ri (∧r f f₁) = ∧r (Il-ri f) (Il-ri f₁)
Il-ri (li2ri f) = li2ri (Il f)

⊗l-ri : {Γ : Cxt} {A B C : Fma}
        (f : just A ∣ B ∷ Γ ⊢ri C) →
      --------------------------------
           just (A ⊗ B) ∣ Γ ⊢ri C
⊗l-ri (∧r f f₁) = ∧r (⊗l-ri f) (⊗l-ri f₁)
⊗l-ri (li2ri f) = li2ri (⊗l f)

∨l-ri : {Γ : Cxt} {A B C : Fma}
        (f : just A ∣ Γ ⊢ri C) (g : just B ∣ Γ ⊢ri C) →
        --------------------------------------------
                just (A ∨ B) ∣ Γ ⊢ri C
∨l-ri (∧r f f₁) (∧r g g₁) = ∧r (∨l-ri f g) (∨l-ri f₁ g₁)
∨l-ri (li2ri {C = .(pos (` x , snd₁)) , snd} f) (li2ri {C = ` x , snd₁} g) = li2ri (∨l f g)
∨l-ri (li2ri {C = .(pos (I , snd₁)) , snd} f) (li2ri {C = I , snd₁} g) = li2ri (∨l f g)
∨l-ri (li2ri {C = .(pos (A ⊗ B , snd₁)) , snd} f) (li2ri {C = A ⊗ B , snd₁} g) = li2ri (∨l f g)
∨l-ri (li2ri {C = .(pos (A ∨ B , snd₁)) , snd} f) (li2ri {C = A ∨ B , snd₁} g) = li2ri (∨l f g)

pass-ri : {Γ : Cxt} {A C : Fma}
          (f : just A ∣ Γ ⊢ri C) →
     --------------------------------
              - ∣ A ∷ Γ ⊢ri C
pass-ri (∧r f f₁) = ∧r (pass-ri f) (pass-ri f₁)
pass-ri (li2ri f) = li2ri (f2li (pass f))

∧l₁-ri : {Γ : Cxt} {A B C : Fma}
         (f : just A ∣ Γ ⊢ri C) →
              just (A ∧ B) ∣ Γ ⊢ri C
∧l₁-ri (∧r f f₁) = ∧r (∧l₁-ri f) (∧l₁-ri f₁)
∧l₁-ri (li2ri f) = li2ri (f2li (∧l₁ f))

∧l₂-ri : {Γ : Cxt} {A B C : Fma}
         (f : just B ∣ Γ ⊢ri C) →
              just (A ∧ B) ∣ Γ ⊢ri C
∧l₂-ri (∧r f f₁) = ∧r (∧l₂-ri f) (∧l₂-ri f₁)
∧l₂-ri (li2ri f) = li2ri (f2li (∧l₂ f))

Ir-ri : - ∣ [] ⊢ri I
Ir-ri = li2ri (f2li Ir)

-- Expand identity recursively, using the η-conversions for compound formulae.
ax-ri : {C : Fma} → just C ∣ [] ⊢ri C
ax-ri {C = ` x} = li2ri (f2li ax)
ax-ri {C = I} = li2ri (Il (f2li Ir))
ax-ri {C = C ⊗ C'} = ⊗l-ri (⊗r-ri ax-ri (pass-ri ax-ri))
ax-ri {C = C ∧ C'} = ∧r (∧l₁-ri ax-ri) (∧l₂-ri ax-ri)
ax-ri {C ∨ C'} = ∨l-ri (∨r₁-ri ax-ri) (∨r₂-ri ax-ri)

-- Normalize by replacing each sequent-calculus rule with its admissible
-- counterpart in phase ri.
focus : {S : Stp} {Γ : Cxt} {C : Fma}
  → (f : S ∣ Γ ⊢ C)
  → S ∣ Γ ⊢ri C
focus ax = ax-ri
focus (pass f) = pass-ri (focus f)
focus Ir = Ir-ri
focus (Il f) = Il-ri (focus f)
focus (⊗r f f₁) = ⊗r-ri (focus f) (focus f₁)
focus (⊗l f) = ⊗l-ri (focus f)
focus (∧r f f₁) = ∧r (focus f) (focus f₁)
focus (∧l₁ f) = ∧l₁-ri (focus f)
focus (∧l₂ f) = ∧l₂-ri (focus f)
focus (∨r₁ f) = ∨r₁-ri (focus f)
focus (∨r₂ f) = ∨r₂-ri (focus f)
focus (∨l f g) = ∨l-ri (focus f) (focus g)

