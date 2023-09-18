{-# OPTIONS --rewriting #-}

module Focusing where

open import Data.List renaming (map to mapList)
open import Data.List.Relation.Unary.All
open import Data.List.Properties
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open import Data.Bool hiding (_∧_; _∨_)

open import Utilities
open import Formulae
open import SeqCalc

mapList++ : {A B : Set} {f : A → B} (xs ys : List A)
  → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
mapList++ [] ys = refl
mapList++ {f = f} (x ∷ xs) ys = cong (f x ∷_) (mapList++ xs ys)
{-# REWRITE mapList++ #-}

All++ : {A : Set} {xs ys : List A} {P : A → Set} → All P xs → All P ys → All P (xs ++ ys)
All++ [] ys = ys
All++ (px ∷ xs) ys = px ∷ (All++ xs ys)

{-
We define a data type of tags which 
monitors proof search process 
in the focused calculus.
-}
data Tag : Set where
  R : Tag -- the tag for non-left non-invertible rules
  C₁ : Tag -- for ∧l₁T
  C₂ : Tag -- for ∧l₁T
  P : Tag  -- for passT

{-
The predicates below show that 
what is a valid list of tags.
In particular, a list of tags
is valid if
i) there is at least one tag R, or
ii) both C₁ and C₂ are in the list.
-}

isOKC₁ : List Tag → Set
isOKC₁ (C₂ ∷ l) = ⊤
isOKC₁ (R ∷ l) = ⊤
isOKC₁ (C₁ ∷ l) = isOKC₁ l
isOKC₁ _ = ⊥

isOKC₂ : List Tag → Set
isOKC₂ (C₁ ∷ l) = ⊤
isOKC₂ (R ∷ l) = ⊤
isOKC₂ (C₂ ∷ l) = isOKC₂ l
isOKC₂ _ = ⊥

isOK : List Tag → Set
isOK [] = ⊥
isOK (R ∷ l) = ⊤
isOK (C₁ ∷ l) = isOKC₁ l
isOK (C₂ ∷ l) = isOKC₂ l
isOK (P ∷ l) = isOK l


{-
Definition of the focused calculus
-}
-- ri = right invertible
data _∣_⊢ri_ : Stp → Cxt → Fma → Set

data _∣_∣_⊢riT_ : (l : List Tag) → Irr → Cxt → Fma → Set

-- l = left phase
data _∣_⊢li_ : Stp → Cxt → Pos → Set

-- f = focusing
data _∣_⊢f_ : Irr → Cxt → Pos → Set
data _∣_∣_⊢fT_ : (t : Tag) → Irr → Cxt → Pos → Set

data _∣_⊢ri_ where
  ∧r : {S : Stp} {Γ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ⊢ri A) (g : S ∣ Γ ⊢ri B)
    ---------------------------------------
    →          S ∣ Γ ⊢ri A ∧ B
  li2ri : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    ------------------------
    →      S ∣ Γ ⊢ri pos C

data _∣_∣_⊢riT_ where
  ∧rT : {l l' : List Tag} {S : Irr} {Γ : Cxt} {A B : Fma}
    → (f : l ∣ S ∣ Γ ⊢riT A) (g : l' ∣ S ∣ Γ ⊢riT B)
    ---------------------------------------------------------
    →             (l ++ l') ∣ S ∣ Γ ⊢riT A ∧ B
  f2riT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : t ∣ S ∣ Γ ⊢fT C)
    ------------------------
    →    [ t ] ∣ S ∣ Γ ⊢riT pos C

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
  ⊗r : (l : List Tag) {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma} →
         (ok : isOK l) (eq : Γ' ≡ Γ ++ Δ) →
         (f : l ∣ S ∣ Γ ⊢riT A) (g : - ∣ Δ  ⊢ri B) →
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
  ∨r₁ : (l : List Tag) {S : Irr} {Γ : Cxt} {A B : Fma} →
        (ok : isOK l) →
        (f : l ∣ S ∣ Γ ⊢riT A) →
        -------------------------
             S ∣ Γ ⊢f (A  ∨ B , _)
  ∨r₂ : (l : List Tag) {S : Irr} {Γ : Cxt} {A B : Fma} →
        (ok : isOK l) →
        (f : l ∣ S ∣ Γ ⊢riT B) →
        -------------------------
             S ∣ Γ ⊢f (A  ∨ B , _)

data _∣_∣_⊢fT_ where
  ax : {X : At} →
       R ∣ (just (` X) , _) ∣ [] ⊢fT (` X , _)
  Ir : R ∣ (- , _) ∣ [] ⊢fT (I , _)
  passT : {Ω : Cxt} {A : Fma} {C : Pos}
           (f : just A ∣ Ω ⊢li C) →
           -------------------------------
               P ∣ (- , _) ∣ A ∷ Ω ⊢fT C
  ⊗rT : (l : List Tag) {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma} →
         (ok : isOK l) (eq : Γ' ≡ Γ ++ Δ) →
         (f : l ∣ S ∣ Γ ⊢riT A) (g : - ∣ Δ ⊢ri B) →
         -----------------------------------
              R ∣ S ∣ Γ' ⊢fT (A ⊗ B , _)
  ∧l₁T : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) →
        --------------------------------
              C₁ ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C
  ∧l₂T : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ⊢li C) →
        --------------------------------
             C₂ ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C
  ∨r₁T : (l : List Tag) {S : Irr} {Γ : Cxt} {A B : Fma} →
        (ok : isOK l) →
        (f : l ∣ S ∣ Γ ⊢riT A) →
        -------------------------
             R ∣ S ∣ Γ ⊢fT (A  ∨ B , _)
  ∨r₂T : (l : List Tag) {S : Irr} {Γ : Cxt} {A B : Fma} →
        (ok : isOK l) →
        (f : l ∣ S ∣ Γ ⊢riT B) →
        -------------------------
             R ∣ S ∣ Γ ⊢fT (A  ∨ B , _)

{-
The data type SubFmas records how a formula 
is construct by a list of positive formulas.
-}

data SubFmas : List Pos → Fma → Set where
  conj : {Φ Ψ : List Pos} {A B : Fma} →
      SubFmas Φ A → SubFmas Ψ B →
      SubFmas (Φ ++ Ψ) (A ∧ B)
  stop : {A : Pos} →
       SubFmas [ A ]  (pos A)

SubFmas[]-⊥ : {A : Fma} {Φ : List Pos}
  → SubFmas Φ A
  → (eq : Φ ≡ [])
  → ⊥
SubFmas[]-⊥ (conj {[]} SF SF₁) eq = SubFmas[]-⊥ SF refl

match-fT : (S : Irr) (Γ : Cxt) (Φ : Tag × Pos) → Set
match-fT S Γ (t , p) = t ∣ S ∣ Γ ⊢fT p

-- To distribute a list of Tags and Positive formulas
fsDist : {S : Irr} {Γ : Cxt} {Θ : List (Tag × Pos)}
  → (Φ Ψ : List Pos) (fs : All (match-fT S Γ) Θ) (eq : Φ ++ Ψ ≡ mapList (λ x → proj₂ x) Θ)
  → Σ (List (Tag × Pos)) λ Θ₁ → Σ (List (Tag × Pos)) λ Θ₂ 
    → Σ (All (match-fT S Γ) Θ₁) λ fs1 → Σ (All (match-fT S Γ) Θ₂) λ fs2 →  Σ (Θ₁ ++ Θ₂ ≡ Θ) λ eq1 → Φ ≡ mapList (λ x → proj₂ x) Θ₁ × Ψ ≡ mapList (λ x → proj₂ x) Θ₂
      × fs ≡ subst (λ x → All (match-fT S Γ) x) eq1 (All++ fs1 fs2)
fsDist [] [] [] refl = [] , [] , [] , [] , refl , refl , refl , refl
fsDist [] (A ∷ Ψ) (f ∷ fs) refl = [] , _ ∷ _ , [] , f ∷ fs , refl , refl , refl , refl
fsDist (x ∷ Φ) Ψ (f ∷ fs) eq with fsDist Φ Ψ fs (proj₂ (inj∷ eq))
fsDist (._ ∷ .(mapList (λ x → proj₂ x) Θ₁)) .(mapList (λ x → proj₂ x) Θ₂) (f ∷ fs) refl | Θ₁ , Θ₂ , fs1 , fs2 , refl , refl , refl , refl = 
  _ ∷ Θ₁ , Θ₂ , f ∷ fs1 , fs2 , refl , refl , refl , refl

fsDist-refl : {S : Irr} {Γ : Cxt}
  → {Φ Ψ : List (Tag × Pos)}
  → (fs : All (match-fT S Γ) Φ)
  → (gs : All (match-fT S Γ) Ψ)
  → fsDist (mapList (λ r → proj₂ r) Φ) (mapList (λ r → proj₂ r) Ψ) (All++ fs gs) refl ≡ (Φ , Ψ , fs , gs , refl , refl , refl , refl)
fsDist-refl [] [] = refl
fsDist-refl [] (g ∷ gs) = refl
fsDist-refl (f ∷ fs) gs rewrite fsDist-refl fs gs = refl
{-# REWRITE fsDist-refl #-}

∧rT* : {S : Irr} {Γ : Cxt} {A : Fma}
  → {Θ : List (Tag × Pos)} {Φ : List Pos}
  → (fs : All (match-fT S Γ) Θ)
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → proj₂ x) Θ)
  → (mapList (λ x → proj₁ x) Θ) ∣ S ∣ Γ ⊢riT A
∧rT* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist Φ Ψ fs eq
∧rT* fs (conj {.(mapList (λ x → proj₂ x) Θ₁)} {.(mapList (λ x → proj₂ x) Θ₂)} SF1 SF2) refl | Θ₁ , Θ₂ , fs1 , fs2 , refl , refl , refl , refl = 
  ∧rT (∧rT* fs1 SF1 refl) (∧rT* fs2 SF2 refl)
∧rT* (f ∷ []) stop refl = f2riT f

{-
We can generalize operations to lists of sequents.
-}

f2li-fs : {S : Irr} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → S ∣ Γ ⊢f P) Φ
  → All (λ P → irr S ∣ Γ ⊢li P) Φ
f2li-fs [] = []
f2li-fs (f ∷ fs) = f2li f ∷ (f2li-fs fs)

li2f-fs : {S : Irr} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → irr S ∣ Γ ⊢li P) Φ
  → All (λ P → S ∣ Γ ⊢f P) Φ
li2f-fs [] = []
li2f-fs {S , p} (f2li {.(irr (S , p)) , q} f ∷ fs) rewrite irr-eq S q | isIrr-unique S q p = f ∷ li2f-fs fs 

∧l₁-fs : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just A ∣ Γ ⊢li P) Φ
  → All (λ P → (just (A ∧ B) , _) ∣ Γ ⊢f P) Φ
∧l₁-fs [] = []
∧l₁-fs (f ∷ fs) = ∧l₁ f ∷ (∧l₁-fs fs)

∧l₂-fs : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just B ∣ Γ ⊢li P) Φ
  → All (λ P → (just (A ∧ B) , _) ∣ Γ ⊢f P) Φ
∧l₂-fs [] = []
∧l₂-fs (f ∷ fs) = ∧l₂ f ∷ (∧l₂-fs fs)

pass-fs : {A : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just A ∣ Γ ⊢li P) Φ
  → All (λ P → (- , _) ∣ A ∷ Γ ⊢f P) Φ
pass-fs [] = []
pass-fs (f ∷ fs) = pass f ∷ (pass-fs fs)

⊗l-inv-fs : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just (A ⊗ B) ∣ Γ ⊢li P) Φ
  → All (λ P → just A ∣ B ∷ Γ ⊢li P) Φ
⊗l-inv-fs [] = []
⊗l-inv-fs (⊗l f ∷ fs) = f ∷ (⊗l-inv-fs fs)

Il-inv-fs : {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just I ∣ Γ ⊢li P) Φ
  → All (λ P → - ∣ Γ ⊢li P) Φ
Il-inv-fs [] = []
Il-inv-fs (Il f ∷ fs) = f ∷ (Il-inv-fs fs)

∨l-inv-fs₁ : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just (A ∨ B) ∣ Γ ⊢li P) Φ
  → All (λ P → just A ∣ Γ ⊢li P) Φ
∨l-inv-fs₁ [] = []
∨l-inv-fs₁ (∨l f g ∷ fs) = f ∷ (∨l-inv-fs₁ fs)

∨l-inv-fs₂ : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just (A ∨ B) ∣ Γ ⊢li P) Φ
  → All (λ P → just B ∣ Γ ⊢li P) Φ
∨l-inv-fs₂ [] = []
∨l-inv-fs₂ (∨l f g ∷ fs) = g ∷ (∨l-inv-fs₂ fs)

