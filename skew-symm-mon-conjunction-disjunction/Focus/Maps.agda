{-# OPTIONS --safe #-}

module Focus.Maps (At : Set) where

open import Data.List
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Data.Unit using (tt)
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
import SeqCalc.Impl At as I
open I using (_∣_⊢_)
open import Focus.FocusedCalc At
open import Focus.Tags

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
    pick : Pick A Γ Δ
    gs : All (λ C → just A ∣ Δ ⊢li C) Φ
    eqS : irr S ≡ -
    eqf : subst (λ S → All (λ C → S ∣ Γ ⊢li C) Φ) eqS fs ≡ f2li-fs (pass-f-fs pick gs)

data CheckFocus {S : Irr} {Γ : Cxt} {Φ : Tree Pos} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) : Set where
  case1 : All∧l₁ {S} fs → CheckFocus fs
  case2 : All∧l₂ {S} fs → CheckFocus fs
  casepass : AllPass {S} fs → CheckFocus fs
  caseok : isOK (tags-fs S fs) → CheckFocus fs

open All∧l₁
open All∧l₂
open AllPass

-- Uniform trees provide the witnesses needed for conflicting choices.
tags-C₁ : ∀ {A B Γ Φ} (fs : All (λ C → just A ∣ Γ ⊢li C) Φ)
  → hasC₁ (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₁-f-fs fs)))
tags-C₁ (leaf f) = tt
tags-C₁ {A} {B} (node fs gs) = hasC₁-++1
  (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₁-f-fs fs)))
  (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₁-f-fs gs))) (tags-C₁ {B = B} fs)

tags-C₂ : ∀ {A B Γ Φ} (fs : All (λ C → just B ∣ Γ ⊢li C) Φ)
  → hasC₂ (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₂-f-fs fs)))
tags-C₂ (leaf f) = tt
tags-C₂ {A} {B} (node fs gs) = hasC₂-++1
  (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₂-f-fs fs)))
  (tags-fs (just (A ∧ B) , tt) (f2li-fs (∧l₂-f-fs gs))) (tags-C₂ {A = A} fs)

tags-pass-differ : ∀ n {A Γ Δ Φ} (p : Pick A Γ Δ)
  (fs : All (λ C → just A ∣ Δ ⊢li C) Φ)
  → (n ≡ pick-index p → ⊥)
  → differsFromP n (tags-fs (- , tt) (f2li-fs (pass-f-fs p fs)))
tags-pass-differ n p (leaf f) neq with n ≟ pick-index p
... | yes eq = ⊥-elim (neq eq)
... | no _ = tt
tags-pass-differ n p (node fs gs) neq = differsFromP-++1 n
  (tags-fs (- , tt) (f2li-fs (pass-f-fs p fs)))
  (tags-fs (- , tt) (f2li-fs (pass-f-fs p gs))) (tags-pass-differ n p fs neq)

tags-pass-conflict : ∀ {A Γ Δ Φ} (p : Pick A Γ Δ)
  (fs : All (λ C → just A ∣ Δ ⊢li C) Φ) (ts : List Tag)
  → differsFromP (pick-index p) ts
  → differentP (tags-fs (- , tt) (f2li-fs (pass-f-fs p fs)) ++ ts)
tags-pass-conflict p (leaf f) ts ok = ok
tags-pass-conflict p (node fs gs) ts ok =
  subst differentP (sym (++-assoc
    (tags-fs (- , tt) (f2li-fs (pass-f-fs p fs)))
    (tags-fs (- , tt) (f2li-fs (pass-f-fs p gs))) ts))
    (tags-pass-conflict p fs (tags-fs (- , tt) (f2li-fs (pass-f-fs p gs)) ++ ts)
      (differsFromP-++2 (pick-index p)
        (tags-fs (- , tt) (f2li-fs (pass-f-fs p gs))) ts ok))

-- Classify the two branches separately and combine their results.
check-focus-node : ∀ {S Γ Φ Ψ}
  (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ)
  (hs : All (λ C → irr S ∣ Γ ⊢li C) Ψ)
  → CheckFocus {S} fs → CheckFocus {S} hs → CheckFocus {S} (node fs hs)
check-focus-node {S} fs hs (case1 (all∧l₁ gs refl refl)) (case1 (all∧l₁ ks refl refl)) = case1 (all∧l₁ (node gs ks) refl refl)
check-focus-node {S} fs hs (case2 (all∧l₂ gs refl refl)) (case2 (all∧l₂ ks refl refl)) = case2 (all∧l₂ (node gs ks) refl refl)
check-focus-node {S} fs hs (case1 (all∧l₁ {A} {B} gs refl refl)) (case2 (all∧l₂ ks refl refl)) =
  caseok (valid-Cs (tags-fs S fs ++ tags-fs S hs)
    (hasC₁-++1 (tags-fs S fs) (tags-fs S hs) (tags-C₁ {B = B} gs))
    (hasC₂-++2 (tags-fs S fs) (tags-fs S hs) (tags-C₂ {A = A} ks)))
check-focus-node {S} fs hs (case2 (all∧l₂ {A} {B} gs refl refl)) (case1 (all∧l₁ ks refl refl)) =
  caseok (valid-Cs (tags-fs S fs ++ tags-fs S hs)
    (hasC₁-++2 (tags-fs S fs) (tags-fs S hs) (tags-C₁ {B = B} ks))
    (hasC₂-++1 (tags-fs S fs) (tags-fs S hs) (tags-C₂ {A = A} gs)))
check-focus-node {S} fs hs (casepass (allPass p gs refl eqf)) (case1 (all∧l₁ ks () eqg))
check-focus-node {S} fs hs (casepass (allPass p gs refl eqf)) (case2 (all∧l₂ ks () eqg))
check-focus-node {S} fs hs _ (caseok ok) = caseok (isOK++2 (tags-fs _ fs) ok)
check-focus-node {S} fs hs (caseok ok) _ = caseok (isOK++1 (tags-fs _ fs) ok)
check-focus-node {S} fs hs (casepass (allPass p gs refl refl)) (casepass (allPass q ks refl refl)) with pick-index p ≟ pick-index q
... | no neq = caseok (valid-Ps (tags-fs S fs ++ tags-fs S hs)
  (tags-pass-conflict p gs (tags-fs S hs) (tags-pass-differ (pick-index p) q ks neq)))
... | yes eq with same-pick p q eq
... | refl = casepass (allPass p (node gs ks) refl refl)

check-focus : {S : Irr} {Γ : Cxt} {Φ : Tree Pos} (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ) → CheckFocus {S} fs
check-focus (leaf (f2li ax)) = caseok tt
check-focus (leaf (f2li Ir)) = caseok tt
check-focus (leaf (f2li (pass p f))) = casepass (allPass p (leaf f) refl refl)
check-focus (leaf (f2li (∧l₁ f))) = case1 (all∧l₁ (leaf f) refl refl)
check-focus (leaf (f2li (∧l₂ f))) = case2 (all∧l₂ (leaf f) refl refl)
check-focus (leaf (f2li (∨r₁ f ok))) = caseok tt
check-focus (leaf (f2li (∨r₂ f ok))) = caseok tt
check-focus (leaf (f2li (⊗r p f g ok))) = caseok tt
check-focus {S} (node fs hs) = check-focus-node {S} fs hs (check-focus {S} fs) (check-focus {S} hs)

-- A view contains every possible left decomposition. At an empty stoup,
-- pass may select any occurrence, so its child is indexed by a Pick witness.
data LView : Stp → Cxt → Set where
  atom : ∀ {X Γ} → LView (just (` X)) Γ
  empty : LView - []
  pass : ∀ {Γ} → (∀ {A Δ} → Pick A Γ Δ → LView (just A) Δ) → LView - Γ
  Il : ∀ {Γ} → LView - Γ → LView (just I) Γ
  ⊗l : ∀ {A B Γ} → LView (just A) (B ∷ Γ) → LView (just (A ⊗ B)) Γ
  ∧l : ∀ {A B Γ} → LView (just A) Γ → LView (just B) Γ → LView (just (A ∧ B)) Γ
  ∨l : ∀ {A B Γ} → LView (just A) Γ → LView (just B) Γ → LView (just (A ∨ B)) Γ

-- Formula decomposition and insertion are mutually structural. Formula
-- decomposition calls insertion on a subformula; insertion descends through
-- the original view. Pick records the occurrence being inserted.
view-fma : (A : Fma) {Γ : Cxt} → LView - Γ → LView (just A) Γ

insert-view-pick : (A : Fma) {S : Stp} {Γ Γ' : Cxt}
  → Pick A Γ' Γ → LView S Γ → LView S Γ'

-- Selecting the inserted occurrence decomposes A against the original
-- context. Every other choice inserts A into a child of the original view.
insert-pass : (A : Fma) {Γ Γ' : Cxt} → Pick A Γ' Γ
  → (∀ {B Δ} → Pick B Γ Δ → LView (just B) Δ)
  → ∀ {B Δ'} → Pick B Γ' Δ' → LView (just B) Δ'

view-fma (` X) v = atom
view-fma I v = Il v
view-fma (A ⊗ B) v = ⊗l (view-fma A (insert-view-pick B here v))
view-fma (A ∧ B) v = ∧l (view-fma A v) (view-fma B v)
view-fma (A ∨ B) v = ∨l (view-fma A v) (view-fma B v)

insert-view-pick A p atom = atom
insert-view-pick A here empty = pass λ { here → view-fma A empty ; (there ()) }
insert-view-pick A p (pass vs) = pass (insert-pass A p vs)
insert-view-pick A p (Il v) = Il (insert-view-pick A p v)
insert-view-pick A p (⊗l v) = ⊗l (insert-view-pick A (there p) v)
insert-view-pick A p (∧l v w) = ∧l (insert-view-pick A p v) (insert-view-pick A p w)
insert-view-pick A p (∨l v w) = ∨l (insert-view-pick A p v) (insert-view-pick A p w)

insert-pass A p vs q with ex-pickR p q
... | inj₁ (refl , refl) = view-fma A (pass vs)
... | inj₂ (Δ , q' , p') = insert-view-pick A p' (vs q')


-- Insert at a specified context position, preserving the existing order.
insert-view : (A : Fma) (Γ : Cxt) {S : Stp} {Δ : Cxt}
  → LView S (Γ ++ Δ) → LView S (Γ ++ A ∷ Δ)
insert-view A Γ = insert-view-pick A (pick-prefix Γ)

view-cxt : (Γ : Cxt) → LView - Γ
view-cxt [] = empty
view-cxt (A ∷ Γ) = insert-view A [] (view-cxt Γ)

view-ant : (S : Stp) (Γ : Cxt) → LView S Γ
view-ant - Γ = view-cxt Γ
view-ant (just A) Γ = view-fma A (view-cxt Γ)

-- Admissible right introductions use the same tree and LView structure as
-- the calculus without exchange. A shared pass is commuted out using its
-- selected occurrence; for tensor, pull-left locates it in the conclusion.
∨r₁-li : {S : Stp} {Γ : Cxt} (v : LView S Γ) {A B : Fma}
  → All (λ C → S ∣ Γ ⊢li C) (toTree A) → S ∣ Γ ⊢li (A ∨ B , tt)
∨r₁-li-irr : {S : Stp} {i : isIrr S} {Γ : Cxt} (v : LView S Γ) {A B : Fma}
  → (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A))
  → CheckFocus {S , i} fs → (S , i) ∣ Γ ⊢f (A ∨ B , tt)

∨r₁-li atom fs = f2li (∨r₁-li-irr atom fs (check-focus fs))
∨r₁-li empty fs = f2li (∨r₁-li-irr empty fs (check-focus fs))
∨r₁-li (pass v) fs = f2li (∨r₁-li-irr (pass v) fs (check-focus fs))
∨r₁-li (∧l v w) fs = f2li (∨r₁-li-irr (∧l v w) fs (check-focus fs))
∨r₁-li (Il v) fs = Il (∨r₁-li v (Il-inv-fs fs))
∨r₁-li (⊗l v) fs = ⊗l (∨r₁-li v (⊗l-inv-fs fs))
∨r₁-li (∨l v w) fs = ∨l (∨r₁-li v (∨l-inv-fs₁ fs)) (∨r₁-li w (∨l-inv-fs₂ fs))

∨r₁-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl eqf)) = ∧l₁ (∨r₁-li v gs)
∨r₁-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl eqf)) = ∧l₂ (∨r₁-li w gs)
∨r₁-li-irr (pass v) fs (casepass (allPass p gs refl eqf)) =
  pass p (∨r₁-li (v p) gs)
∨r₁-li-irr empty fs (casepass (allPass () gs refl eqf))
∨r₁-li-irr v fs (caseok ok) = ∨r₁ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)

∨r₁-ri : ∀ {S Γ A B} → S ∣ Γ ⊢ri A → S ∣ Γ ⊢ri A ∨ B
∨r₁-ri {S} {Γ} f = li2ri (∨r₁-li (view-ant S Γ) (∧r*-ri-inv f))

∨r₂-li : {S : Stp} {Γ : Cxt} (v : LView S Γ) {A B : Fma}
  → All (λ C → S ∣ Γ ⊢li C) (toTree B) → S ∣ Γ ⊢li (A ∨ B , tt)
∨r₂-li-irr : {S : Stp} {i : isIrr S} {Γ : Cxt} (v : LView S Γ) {A B : Fma}
  → (fs : All (λ C → S ∣ Γ ⊢li C) (toTree B))
  → CheckFocus {S , i} fs → (S , i) ∣ Γ ⊢f (A ∨ B , tt)

∨r₂-li atom fs = f2li (∨r₂-li-irr atom fs (check-focus fs))
∨r₂-li empty fs = f2li (∨r₂-li-irr empty fs (check-focus fs))
∨r₂-li (pass v) fs = f2li (∨r₂-li-irr (pass v) fs (check-focus fs))
∨r₂-li (∧l v w) fs = f2li (∨r₂-li-irr (∧l v w) fs (check-focus fs))
∨r₂-li (Il v) fs = Il (∨r₂-li v (Il-inv-fs fs))
∨r₂-li (⊗l v) fs = ⊗l (∨r₂-li v (⊗l-inv-fs fs))
∨r₂-li (∨l v w) fs = ∨l (∨r₂-li v (∨l-inv-fs₁ fs)) (∨r₂-li w (∨l-inv-fs₂ fs))

∨r₂-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl eqf)) = ∧l₁ (∨r₂-li v gs)
∨r₂-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl eqf)) = ∧l₂ (∨r₂-li w gs)
∨r₂-li-irr (pass v) fs (casepass (allPass p gs refl eqf)) =
  pass p (∨r₂-li (v p) gs)
∨r₂-li-irr empty fs (casepass (allPass () gs refl eqf))
∨r₂-li-irr v fs (caseok ok) = ∨r₂ (∧r*-ri _ fs) (subst isOK (tags-ri∧r*-ri _ fs) ok)

∨r₂-ri : ∀ {S Γ A B} → S ∣ Γ ⊢ri B → S ∣ Γ ⊢ri A ∨ B
∨r₂-ri {S} {Γ} f = li2ri (∨r₂-li (view-ant S Γ) (∧r*-ri-inv f))

⊗r-li : {S : Stp} {Γ Δ Ξ : Cxt} (v : LView S Γ) {A B : Fma}
  → All (λ C → S ∣ Γ ⊢li C) (toTree A)
  → Part Γ Δ Ξ → - ∣ Δ ⊢ri B → S ∣ Ξ ⊢li (A ⊗ B , tt)
⊗r-li-irr : {S : Stp} {i : isIrr S} {Γ Δ Ξ : Cxt} (v : LView S Γ) {A B : Fma}
  → (fs : All (λ C → S ∣ Γ ⊢li C) (toTree A)) → CheckFocus {S , i} fs
  → Part Γ Δ Ξ → - ∣ Δ ⊢ri B → (S , i) ∣ Ξ ⊢f (A ⊗ B , tt)

⊗r-li atom fs p g = f2li (⊗r-li-irr atom fs (check-focus fs) p g)
⊗r-li empty fs p g = f2li (⊗r-li-irr empty fs (check-focus fs) p g)
⊗r-li (pass v) fs p g = f2li (⊗r-li-irr (pass v) fs (check-focus fs) p g)
⊗r-li (∧l v w) fs p g = f2li (⊗r-li-irr (∧l v w) fs (check-focus fs) p g)
⊗r-li (Il v) fs p g = Il (⊗r-li v (Il-inv-fs fs) p g)
⊗r-li (⊗l v) fs p g = ⊗l (⊗r-li v (⊗l-inv-fs fs) (left p) g)
⊗r-li (∨l v w) fs p g = ∨l (⊗r-li v (∨l-inv-fs₁ fs) p g) (⊗r-li w (∨l-inv-fs₂ fs) p g)

⊗r-li-irr (∧l v w) fs (case1 (all∧l₁ gs refl eqf)) p g = ∧l₁ (⊗r-li v gs p g)
⊗r-li-irr (∧l v w) fs (case2 (all∧l₂ gs refl eqf)) p g = ∧l₂ (⊗r-li w gs p g)
⊗r-li-irr (pass v) fs (casepass (allPass q gs refl eqf)) p g =
  pass (proj₁ (proj₂ (pull-left p q)))
    (⊗r-li (v q) gs (proj₂ (proj₂ (pull-left p q))) g)
⊗r-li-irr empty fs (casepass (allPass () gs refl eqf)) p g
⊗r-li-irr v fs (caseok ok) p g = ⊗r p (∧r*-ri _ fs) g (subst isOK (tags-ri∧r*-ri _ fs) ok)

⊗r-ri : ∀ {S Γ Δ Ξ} → Part Γ Δ Ξ → {A B : Fma}
  → S ∣ Γ ⊢ri A → - ∣ Δ ⊢ri B → S ∣ Ξ ⊢ri A ⊗ B
⊗r-ri {S} {Γ} p f g = li2ri (⊗r-li (view-ant S Γ) (∧r*-ri-inv f) p g)

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

pass-ri : ∀ {Γ Δ A C} → Pick A Γ Δ
  → just A ∣ Δ ⊢ri C → - ∣ Γ ⊢ri C
pass-ri p (∧r f g) = ∧r (pass-ri p f) (pass-ri p g)
pass-ri p (li2ri f) = li2ri (f2li (pass p f))

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
ax-ri {C = C ⊗ C'} = ⊗l-ri (⊗r-ri (right done) ax-ri (pass-ri here ax-ri))
ax-ri {C = C ∧ C'} = ∧r (∧l₁-ri ax-ri) (∧l₂-ri ax-ri)
ax-ri {C ∨ C'} = ∨l-ri (∨r₁-ri ax-ri) (∨r₂-ri ax-ri)

-- Normalize an implicit derivation by replacing each rule with its
-- admissible focused form. Pass selections and tensor partitions are
-- supplied directly; no exchange admissibility proof is needed.
focus : {S : Stp} {Γ : Cxt} {C : Fma}
  → S ∣ Γ ⊢ C → S ∣ Γ ⊢ri C
focus I.ax = ax-ri
focus (I.pass p f) = pass-ri p (focus f)
focus I.Ir = Ir-ri
focus (I.Il f) = Il-ri (focus f)
focus (I.⊗r p f g) = ⊗r-ri p (focus f) (focus g)
focus (I.⊗l f) = ⊗l-ri (focus f)
focus (I.∧r f g) = ∧r (focus f) (focus g)
focus (I.∧l₁ f) = ∧l₁-ri (focus f)
focus (I.∧l₂ f) = ∧l₂-ri (focus f)
focus (I.∨r₁ f) = ∨r₁-ri (focus f)
focus (I.∨r₂ f) = ∨r₂-ri (focus f)
focus (I.∨l f g) = ∨l-ri (focus f) (focus g)

-- Forget focusing phases and normal-form side conditions, retaining
-- the pass selections and tensor partitions of the implicit calculus.
emb-ri : ∀ {S Γ C} → S ∣ Γ ⊢ri C → S ∣ Γ ⊢ C
emb-li : ∀ {S Γ C} → S ∣ Γ ⊢li C → S ∣ Γ ⊢ pos C
emb-f : ∀ {S Γ C} → S ∣ Γ ⊢f C → irr S ∣ Γ ⊢ pos C

emb-ri (∧r f g) = I.∧r (emb-ri f) (emb-ri g)
emb-ri (li2ri f) = emb-li f

emb-li (⊗l f) = I.⊗l (emb-li f)
emb-li (Il f) = I.Il (emb-li f)
emb-li (∨l f g) = I.∨l (emb-li f) (emb-li g)
emb-li (f2li f) = emb-f f

emb-f ax = I.ax
emb-f Ir = I.Ir
emb-f (pass p f) = I.pass p (emb-li f)
emb-f (⊗r p f g ok) = I.⊗r p (emb-ri f) (emb-ri g)
emb-f (∧l₁ f) = I.∧l₁ (emb-li f)
emb-f (∧l₂ f) = I.∧l₂ (emb-li f)
emb-f (∨r₁ f ok) = I.∨r₁ (emb-ri f)
emb-f (∨r₂ f ok) = I.∨r₂ (emb-ri f)
