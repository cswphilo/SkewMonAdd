{-# OPTIONS --rewriting #-}

module FocusingRE where

open import Data.List renaming (map to mapList; zip to zipList)
open import Data.List.Relation.Unary.All renaming (map to mapAll)
open import Data.List.Properties
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open import Data.Bool hiding (_∧_; _∨_)
open import Relation.Nullary.Decidable.Core

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

data Tag : Set where
  R : Tag
  C₁ : Tag
  C₂ : Tag
  P : Tag

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

allC₁ : List Pos → List (Tag × Pos)
allC₁ [] = []
allC₁ (A ∷ Φ) = (C₁ , A) ∷ allC₁ Φ

allC₁-refl : (Φ : List Pos) → mapList (λ r → proj₂ r) (allC₁ Φ) ≡ Φ 
allC₁-refl [] = refl
allC₁-refl (A ∷ Φ) = cong (A ∷_) (allC₁-refl Φ)
{-# REWRITE allC₁-refl #-}

allC₂ : List Pos → List (Tag × Pos)
allC₂ [] = []
allC₂ (A ∷ Φ) = (C₂ , A) ∷ allC₂ Φ

allC₂-refl : (Φ : List Pos) → mapList (λ r → proj₂ r) (allC₂ Φ) ≡ Φ 
allC₂-refl [] = refl
allC₂-refl (A ∷ Φ) = cong (A ∷_) (allC₂-refl Φ)
{-# REWRITE allC₂-refl #-}

allP : List Pos → List (Tag × Pos)
allP [] = []
allP (A ∷ Φ) = (P , A) ∷ allP Φ

allP-refl : (Φ : List Pos) → mapList (λ r → proj₂ r) (allP Φ) ≡ Φ 
allP-refl [] = refl
allP-refl (A ∷ Φ) = cong (A ∷_) (allP-refl Φ)
{-# REWRITE allP-refl #-}

projCompose : (Ψ : List (Tag × Pos)) → mapList pos (mapList (λ r → proj₂ r) Ψ) ≡ mapList (λ x → pos (proj₂ x)) Ψ
projCompose [] = refl
projCompose (tp ∷ Ψ) = cong (pos (proj₂ tp) ∷_) (projCompose Ψ)

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

data SubFmas : List Fma → Fma → Set where
  conj : {Φ Ψ : List Fma} {A A' B B' : Fma} →
      SubFmas (A' ∷ Φ) A → SubFmas (B' ∷ Ψ) B →
      SubFmas (A' ∷ Φ ++ B' ∷ Ψ) (A ∧ B)
  stop : {A : Fma} →
       SubFmas [ A ]  A

-- SubFmas∧ : {Φ Ψ : List Fma} {Γ : List Fma} {A' B' A : Fma}
--     → SubFmas Γ A → (eq : Γ ≡ (Φ ++ A' ∧ B' ∷ Ψ))
--     → SubFmas (Φ ++ A' ∷ B' ∷ Ψ) A
-- SubFmas∧ {Φ'} {Ψ'} (conj {Φ} {Ψ} {A' = A'} {B' = B'} SF SF₁) eq with cases++ Φ' (A' ∷ Φ) Ψ' (B' ∷ Ψ) eq
-- SubFmas∧ {[]} {.(Δ ++ B' ∷ Ψ)} (conj {Δ} {Ψ} {A' = A'} {B' = B'} SF SF₁) refl | inj₁ (Δ , refl , refl) = conj {Φ = _ ∷ Δ} (SubFmas∧ {Φ = []} SF refl) SF₁
-- SubFmas∧ {x ∷ Φ'} {.(Δ ++ B' ∷ Ψ)} {A' = A'} (conj {.(Φ' ++ A' ∧ _ ∷ Δ)} {Ψ} {A' = _} {B' = B'} SF SF₁) refl | inj₁ (Δ , refl , refl) = conj {Φ = Φ' ++ A' ∷ _ ∷ Δ} (SubFmas∧ {Φ = x ∷ Φ'} SF refl) SF₁
-- SubFmas∧ {.(_ ∷ Φ ++ [])} {Ψ'} (conj {Φ} {.Ψ'} {A' = _} {B' = .(_ ∧ _)} SF SF₁) refl | inj₂ ([] , refl , refl) = conj SF (SubFmas∧ {Φ = []} SF₁ refl)
-- SubFmas∧ {.(_ ∷ Φ ++ x ∷ Δ)} {Ψ'} (conj {Φ} {.(Δ ++ _ ∧ _ ∷ Ψ')} {A' = _} {B' = .x} SF SF₁) refl | inj₂ (x ∷ Δ , refl , refl) = conj SF (SubFmas∧ {Φ = x ∷ Δ} SF₁ refl)
-- SubFmas∧ {[]} {[]} stop refl = conj stop stop
-- SubFmas∧ {x ∷ Φ} {[]} stop eq = ⊥-elim ([]disj∷ Φ (proj₂ (inj∷ eq)))
-- SubFmas∧ {x ∷ Φ} {x₁ ∷ Ψ} stop eq = ⊥-elim ([]disj∷ Φ (proj₂ (inj∷ eq)))

match-fT : (S : Irr) (Γ : Cxt) (Φ : Tag × Pos) → Set
match-fT S Γ (t , p) = t ∣ S ∣ Γ ⊢fT p

-- To distribute a list of Tags and Positive formulas
fsDist : {S : Irr} {Γ : Cxt} {Θ : List (Tag × Pos)}
  → (Φ Ψ : List Fma) (fs : All (match-fT S Γ) Θ) (eq : Φ ++ Ψ ≡ mapList (λ x → proj₁ (proj₂ x)) Θ)
  → Σ (List (Tag × Pos)) λ Θ₁ → Σ (List (Tag × Pos)) λ Θ₂ 
    → All (match-fT S Γ) Θ₁ × All (match-fT S Γ) Θ₂ × Θ ≡ Θ₁ ++ Θ₂ × Φ ≡ mapList (λ x → pos (proj₂ x)) Θ₁ × Ψ ≡ mapList (λ x → pos (proj₂ x)) Θ₂
fsDist [] [] [] refl = [] , [] , [] , [] , refl , refl , refl 
fsDist [] (A ∷ Ψ) (f ∷ fs) refl = [] , _ ∷ _ , [] , f ∷ fs , refl , refl , refl
fsDist (x ∷ Φ) Ψ (f ∷ fs) eq with fsDist Φ Ψ fs (proj₂ (inj∷ eq))
fsDist (._ ∷ .(mapList (λ x → proj₁ (proj₂ x)) Θ₁)) .(mapList (λ x → proj₁ (proj₂ x)) Θ₂) (f ∷ fs) refl | Θ₁ , Θ₂ , fs1 , fs2 , refl , refl , refl = 
  _ ∷ Θ₁ , Θ₂ , f ∷ fs1 , fs2 , refl , refl , refl

∧rT* : {S : Irr} {Γ : Cxt} {A : Fma}
  → {Θ : List (Tag × Pos)} {Φ : List Fma}
  → (fs : All (match-fT S Γ) Θ)
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₂ x)) Θ)
  → (mapList (λ x → proj₁ x) Θ) ∣ S ∣ Γ ⊢riT A
∧rT* fs (conj {Φ} {Ψ} {A' = A} {B' = B} SF1 SF2) eq with fsDist (A ∷ Φ) (B ∷ Ψ) fs eq
∧rT* fs (conj {.(mapList (λ x → proj₁ (proj₂ x)) Θ₁)} {.(mapList (λ x → proj₁ (proj₂ x)) Θ₂)} {A' = _} {B' = .(proj₁ (proj₂ tp2))} SF1 SF2) refl | tp1 ∷ Θ₁ , tp2 ∷ Θ₂ , f1 ∷ fs1 , f2 ∷ fs2 , refl , refl , refl = 
  ∧rT (∧rT* (f1 ∷ fs1) SF1 refl) (∧rT* (f2 ∷ fs2) SF2 refl)
∧rT* (f ∷ []) stop refl = f2riT f

f2li-fs : {S : Irr} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → S ∣ Γ ⊢f P) Φ
  → All (λ P → irr S ∣ Γ ⊢li P) Φ
f2li-fs [] = []
f2li-fs (f ∷ fs) = f2li f ∷ (f2li-fs fs)

∧l₁-fs : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just A ∣ Γ ⊢li P) Φ
  → All (λ P → (just (A ∧ B) , _) ∣ Γ ⊢f P) Φ
∧l₁-fs [] = []
∧l₁-fs (f ∷ fs) = ∧l₁ f ∷ (∧l₁-fs fs)

∧l₁T-fs : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just A ∣ Γ ⊢li P) Φ
  → All (match-fT (just (A ∧ B) , _) Γ) (allC₁ Φ)
∧l₁T-fs [] = []
∧l₁T-fs (f ∷ fs) = ∧l₁T f ∷ ∧l₁T-fs fs

∧l₂-fs : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just B ∣ Γ ⊢li P) Φ
  → All (λ P → (just (A ∧ B) , _) ∣ Γ ⊢f P) Φ
∧l₂-fs [] = []
∧l₂-fs (f ∷ fs) = ∧l₂ f ∷ (∧l₂-fs fs)

∧l₂T-fs : {A B : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just B ∣ Γ ⊢li P) Φ
  → All (match-fT (just (A ∧ B) , _) Γ) (allC₂ Φ)
∧l₂T-fs [] = []
∧l₂T-fs (f ∷ fs) = ∧l₂T f ∷ ∧l₂T-fs fs

pass-fs : {A : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just A ∣ Γ ⊢li P) Φ
  → All (λ P → (- , _) ∣ A ∷ Γ ⊢f P) Φ
pass-fs [] = []
pass-fs (f ∷ fs) = pass f ∷ (pass-fs fs)

passT-fs : {A : Fma} {Γ : Cxt} {Φ : List Pos}
  → All (λ P → just A ∣ Γ ⊢li P) Φ
  → All (match-fT (- , _) (A ∷ Γ)) (allP Φ)
passT-fs [] = []
passT-fs (f ∷ fs) = passT f ∷ passT-fs fs

untagF : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → t ∣ S ∣ Γ ⊢fT C
  → S ∣ Γ ⊢f C
untagF ax = ax
untagF Ir = Ir
untagF (passT f) = pass f
untagF (⊗rT l ok eq f g) = ⊗r l ok eq f g
untagF (∧l₁T f) = ∧l₁ f
untagF (∧l₂T f) = ∧l₂ f
untagF (∨r₁T l ok f) = ∨r₁ l ok f
untagF (∨r₂T l ok f) = ∨r₂ l ok f

untagF-fs : {S : Irr} {Γ : Cxt} {Ψ : List (Tag × Pos)} {Φ : List Pos}
  → All (match-fT S Γ) Ψ 
  → (eq : Φ ≡ mapList proj₂ Ψ)
  → All (λ C → S ∣ Γ ⊢f C) Φ
untagF-fs [] refl = []
untagF-fs {Φ = ._ ∷ .(mapList (λ r → proj₂ r) _)} (f ∷ fs) refl = untagF f ∷ untagF-fs fs refl

untagF-∧l₁-fs-refl : {A B : Fma} {Γ : Cxt}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just A) Γ) Φ )
  → ∧l₁-fs fs ≡ untagF-fs (∧l₁T-fs {B = B} fs) refl
untagF-∧l₁-fs-refl [] = refl
untagF-∧l₁-fs-refl (f ∷ fs) = cong (∧l₁ f ∷_) (untagF-∧l₁-fs-refl fs)

untagF-∧l₂-fs-refl : {A B : Fma} {Γ : Cxt}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just B) Γ) Φ )
  → ∧l₂-fs fs ≡ untagF-fs (∧l₂T-fs {A = A} fs) refl
untagF-∧l₂-fs-refl [] = refl
untagF-∧l₂-fs-refl (f ∷ fs) = cong (∧l₂ f ∷_) (untagF-∧l₂-fs-refl fs)

untagF-pass-fs-refl : {A : Fma} {Γ : Cxt}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just A) Γ) Φ )
  → pass-fs fs ≡ untagF-fs (passT-fs fs) refl
untagF-pass-fs-refl [] = refl
untagF-pass-fs-refl (f ∷ fs) = cong (pass f ∷_) (untagF-pass-fs-refl fs)

irr-eq : (S : Stp) (p : isIrr S) → irr (S , p) ≡ S
irr-eq (just (` x)) tt = refl
irr-eq (just (x ∧ x₁)) tt = refl
irr-eq - tt = refl

isIrr-unique : (S : Stp) (p q : isIrr S) → p ≡ q
isIrr-unique (just (` x)) p q = refl
isIrr-unique (just (x ∧ x₁)) p q = refl
isIrr-unique - p q = refl

isOK2isOKC₁ : (t : Tag) {l : List Tag} {Γ : Cxt} {A B : Fma} {C : Pos}
  → (f : t ∣ just (A ∧ B) , _ ∣ Γ ⊢fT C)
  → (ok : isOK (t ∷ l))
  → isOKC₁ (t ∷ l)
isOK2isOKC₁ .R (⊗rT l₁ ok₁ eq f g) ok = tt
isOK2isOKC₁ .C₁ (∧l₁T f) ok = ok
isOK2isOKC₁ .C₂ (∧l₂T f) ok = tt
isOK2isOKC₁ .R (∨r₁T l₁ ok₁ f) ok = tt
isOK2isOKC₁ .R (∨r₂T l₁ ok₁ f) ok = tt

isOK2isOKC₂ : (t : Tag) {l : List Tag} {Γ : Cxt} {A B : Fma} {C : Pos}
  → (f : t ∣ just (A ∧ B) , _ ∣ Γ ⊢fT C)
  → (ok : isOK (t ∷ l))
  → isOKC₂ (t ∷ l)
isOK2isOKC₂ .R (⊗rT l₁ ok₁ eq f g) ok = tt
isOK2isOKC₂ .C₁ (∧l₁T f) ok = tt
isOK2isOKC₂ .C₂ (∧l₂T f) ok = ok
isOK2isOKC₂ .R (∨r₁T l₁ ok₁ f) ok = tt
isOK2isOKC₂ .R (∨r₂T l₁ ok₁ f) ok = tt

check-focus : {S : Irr} {Γ : Cxt} {C : Pos} {Φ : List Pos}
  → (f : irr S ∣ Γ ⊢li C)
  → (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ)
  → ((Σ Fma λ A → Σ Fma λ B → Σ (All (λ C → just A ∣ Γ ⊢li C) (C ∷ Φ)) λ fs' 
    → Σ (irr S ≡  just (A ∧ B)) λ eq → subst (λ x → All (λ P → x ∣ Γ ⊢li P) (C ∷ Φ)) eq (f ∷ fs) ≡ f2li-fs (∧l₁-fs {B = B} fs'))
    ⊎
    (Σ Fma λ A → Σ Fma λ B → Σ (All (λ C → just B ∣ Γ ⊢li C) (C ∷ Φ)) λ fs' 
      → Σ (irr S ≡  just (A ∧ B)) λ eq → subst (λ x → All (λ P → x ∣ Γ ⊢li P) (C ∷ Φ)) eq (f ∷ fs) ≡ f2li-fs (∧l₂-fs {A} fs'))
    ⊎
    (Σ Fma λ A → Σ Cxt λ Γ' → Σ (All (λ C → just A ∣ Γ' ⊢li C) (C ∷ Φ)) λ fs' 
      → Σ (irr S ≡ -) λ eq1 → Σ (Γ ≡ A ∷ Γ') λ eq2 → subst₂ (λ x → λ y → All (λ P → x ∣ y ⊢li P) (C ∷ Φ)) eq1 eq2 (f ∷ fs) ≡ f2li-fs (pass-fs fs')))
    ⊎
    (Σ (List (Tag × Pos)) λ Ψ → Σ (All (match-fT S Γ) Ψ) λ fs' → Σ (C ∷ Φ ≡ mapList proj₂ Ψ) λ eq → f ∷ fs ≡ f2li-fs (untagF-fs fs' eq) × isOK (mapList proj₁ Ψ))
check-focus (f2li (ax {X})) [] = inj₂ ((R , (` X , _)) ∷ [] , ax ∷ [] , refl , refl , _)
check-focus (f2li Ir) [] = inj₂ ((R , (I , _)) ∷ [] , Ir ∷ [] , refl , refl , _)
check-focus (f2li (pass {Γ = Γ} {A} f)) [] = inj₁ (inj₂ (inj₂ (A , Γ , f ∷ [] , refl , refl , refl)))
check-focus {S = .(irr (S , q)) , p} (f2li {S , q} (⊗r l {S = .(S , q)} ok eq f g)) [] 
  rewrite irr-eq S p | isIrr-unique S p q =  inj₂ ((R , (_ ⊗ _ , _)) ∷ [] , ⊗rT l ok eq f g ∷ [] , refl , refl , _)
check-focus (f2li (∧l₁ {A = A} {B} f)) [] = inj₁ (inj₁ (A , B , f ∷ [] , refl , refl))
check-focus (f2li (∧l₂ {A = A} {B} f)) [] = inj₁ (inj₂ (inj₁ (A , B , f ∷ [] , refl , refl)))
check-focus {S , q} (f2li {.(irr (S , q)) , p} (∨r₁ l {S = .(irr (S , q) , p)} ok f)) [] 
  rewrite irr-eq S p | isIrr-unique S p q = inj₂ ((R , (_ ∨ _ , _)) ∷ [] , ∨r₁T l ok f ∷ [] , refl , refl , _)
check-focus {S , q} (f2li {.(irr (S , q)) , p} (∨r₂ l {S = .(irr (S , q) , p)} ok f)) [] 
  rewrite irr-eq S p | isIrr-unique S p q = inj₂ ((R , (_ ∨ _ , _)) ∷ [] , ∨r₂T l ok f ∷ [] , refl , refl , _)
check-focus {S} (f2li f) (f1 ∷ fs) with check-focus {S} f1 fs
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (⊗r l ok eq f g)) (.(f2li (∧l₁ f1')) ∷ .(f2li-fs (∧l₁-fs fs'))) | inj₁ (inj₁ (A , B , f1' ∷ fs' , refl , refl)) = 
    inj₂ ((R , (_ ⊗ _ , _)) ∷ allC₁ (C ∷ Φ) , ⊗rT l ok eq f g ∷ ∧l₁T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (⊗r l ok eq f g) ∷ f2li (∧l₁ f1') ∷ f2li-fs x) (untagF-∧l₁-fs-refl fs') , _)
check-focus {.(just (A ∧ B)) , snd} (f2li (∧l₁ f)) (.(f2li (∧l₁ f1')) ∷ .(f2li-fs (∧l₁-fs fs'))) | inj₁ (inj₁ (A , B , f1' ∷ fs' , refl , refl)) = inj₁ (inj₁ (A , B , f ∷ f1' ∷ fs' , refl , refl))
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (∧l₂ f)) (.(f2li (∧l₁ f1')) ∷ .(f2li-fs (∧l₁-fs fs'))) | inj₁ (inj₁ (A , B , f1' ∷ fs' , refl , refl)) = 
  inj₂ ((C₂ , (_ , _)) ∷ allC₁ (C ∷ Φ) , ∧l₂T f ∷ ∧l₁T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∧l₂ f) ∷ f2li (∧l₁ f1') ∷ f2li-fs x) (untagF-∧l₁-fs-refl fs') , _)
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (∨r₁ l ok f)) (.(f2li (∧l₁ f1')) ∷ .(f2li-fs (∧l₁-fs fs'))) | inj₁ (inj₁ (A , B , f1' ∷ fs' , refl , refl)) = 
  inj₂ ((R , (_ ∨ _ , _)) ∷ allC₁ (C ∷ Φ) , ∨r₁T l ok f ∷ ∧l₁T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∨r₁ l ok f) ∷ f2li (∧l₁ f1') ∷ f2li-fs x) (untagF-∧l₁-fs-refl fs') , _)
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (∨r₂ l ok f)) (.(f2li (∧l₁ f1')) ∷ .(f2li-fs (∧l₁-fs fs'))) | inj₁ (inj₁ (A , B , f1' ∷ fs' , refl , refl)) = 
  inj₂ ((R , (_ ∨ _ , _)) ∷ allC₁ (C ∷ Φ) , ∨r₂T l ok f ∷ ∧l₁T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∨r₂ l ok f) ∷ f2li (∧l₁ f1') ∷ f2li-fs x) (untagF-∧l₁-fs-refl fs') , _)
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (⊗r l ok eq f g)) (.(f2li (∧l₂ f1')) ∷ .(f2li-fs (∧l₂-fs fs'))) | inj₁ (inj₂ (inj₁ (A , B , f1' ∷ fs' , refl , refl))) = 
  inj₂ ((R , (_ ⊗ _ , _)) ∷ allC₂ (C ∷ Φ) , ⊗rT l ok eq f g ∷ ∧l₂T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (⊗r l ok eq f g) ∷ f2li (∧l₂ f1') ∷ f2li-fs x) (untagF-∧l₂-fs-refl fs') , _)
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (∧l₁ f)) (.(f2li (∧l₂ f1')) ∷ .(f2li-fs (∧l₂-fs fs'))) | inj₁ (inj₂ (inj₁ (A , B , f1' ∷ fs' , refl , refl))) = 
  inj₂ ((C₁ , (_ , _)) ∷ allC₂ (C ∷ Φ) , ∧l₁T f ∷ ∧l₂T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∧l₁ f) ∷ f2li (∧l₂ f1') ∷ f2li-fs x) (untagF-∧l₂-fs-refl fs') , _)
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (∧l₂ f)) (.(f2li (∧l₂ f1')) ∷ .(f2li-fs (∧l₂-fs fs'))) | inj₁ (inj₂ (inj₁ (A , B , f1' ∷ fs' , refl , refl))) = 
  inj₁ (inj₂ (inj₁ (A , B , f ∷ f1' ∷ fs' , refl , refl)))
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (∨r₁ l ok f)) (.(f2li (∧l₂ f1')) ∷ .(f2li-fs (∧l₂-fs fs'))) | inj₁ (inj₂ (inj₁ (A , B , f1' ∷ fs' , refl , refl))) = 
  inj₂ ((R , (_ ∨ _ , _)) ∷ allC₂ (C ∷ Φ) , ∨r₁T l ok f ∷ ∧l₂T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∨r₁ l ok f) ∷ f2li (∧l₂ f1') ∷ f2li-fs x) (untagF-∧l₂-fs-refl fs') , _)
check-focus {.(just (A ∧ B)) , snd} {Φ = C ∷ Φ} (f2li (∨r₂ l ok f)) (.(f2li (∧l₂ f1')) ∷ .(f2li-fs (∧l₂-fs fs'))) | inj₁ (inj₂ (inj₁ (A , B , f1' ∷ fs' , refl , refl))) = 
  inj₂ ((R , (_ ∨ _ , _)) ∷ allC₂ (C ∷ Φ) , ∨r₂T l ok f ∷ ∧l₂T-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∨r₂ l ok f) ∷ f2li (∧l₂ f1') ∷ f2li-fs x) (untagF-∧l₂-fs-refl fs') , _)
check-focus {.- , snd} (f2li (pass f)) (.(f2li (pass f1')) ∷ .(f2li-fs (pass-fs fs'))) | inj₁ (inj₂ (inj₂ (A , Γ , f1' ∷ fs' , refl , refl , refl))) = 
  inj₁ (inj₂ (inj₂ (A , Γ , f ∷ f1' ∷ fs' , refl , refl , refl)))
check-focus {.- , snd} {Φ = C ∷ Φ} (f2li (⊗r l ok eq f g)) (.(f2li (pass f1')) ∷ .(f2li-fs (pass-fs fs'))) | inj₁ (inj₂ (inj₂ (A , Γ , f1' ∷ fs' , refl , refl , refl))) = 
  inj₂ ((R , (_ ⊗ _ , _)) ∷ allP (C ∷ Φ) , ⊗rT l ok eq f g ∷ passT-fs (f1' ∷ fs') , refl , cong (λ x → f2li (⊗r l ok eq f g) ∷ f2li (pass f1') ∷ f2li-fs x) (untagF-pass-fs-refl fs') , _)
check-focus {.- , snd} {Φ = C ∷ Φ} (f2li (∨r₁ l ok f)) (.(f2li (pass f1')) ∷ .(f2li-fs (pass-fs fs'))) | inj₁ (inj₂ (inj₂ (A , Γ , f1' ∷ fs' , refl , refl , refl))) = 
  inj₂ ((R , (_ ∨ _ , _)) ∷ allP (C ∷ Φ) , ∨r₁T l ok f ∷ passT-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∨r₁ l ok f) ∷ f2li (pass f1') ∷ f2li-fs x) (untagF-pass-fs-refl fs') , _)
check-focus {.- , snd} {Φ = C ∷ Φ} (f2li (∨r₂ l ok f)) (.(f2li (pass f1')) ∷ .(f2li-fs (pass-fs fs'))) | inj₁ (inj₂ (inj₂ (A , Γ , f1' ∷ fs' , refl , refl , refl))) = 
  inj₂ ((R , (_ ∨ _ , _)) ∷ allP (C ∷ Φ) , ∨r₂T l ok f ∷ passT-fs (f1' ∷ fs') , refl , cong (λ x → f2li (∨r₂ l ok f) ∷ f2li (pass f1') ∷ f2li-fs x) (untagF-pass-fs-refl fs') , _)
check-focus {.(just (` _)) , snd} (f2li ax) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) = 
  inj₂ ((R , (` _  , _)) ∷ _ ∷ _ , ax ∷ f1' ∷ fs' , refl , refl , _)
check-focus {.- , snd} (f2li Ir) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) = 
  inj₂ ((R , (I , _)) ∷ _ ∷ _ , Ir ∷ f1' ∷ fs' , refl , refl , _)
check-focus {.- , snd} (f2li (pass f)) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) = 
  inj₂ ((P , (_ , _)) ∷ _ ∷ _ , passT f ∷ f1' ∷ fs' , refl , refl , ok)
check-focus {S , p} (f2li (⊗r l {S = (S , q)} ok₁ eq f g)) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) 
  rewrite isIrr-unique S q p = 
     inj₂ ((R , (_ ⊗ _ , _)) ∷ _ ∷ _ , ⊗rT l ok₁ eq f g ∷ f1' ∷ fs' , refl , refl , _)
check-focus {.(just (_ ∧ _)) , snd} (f2li (∧l₁ f)) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) = 
  inj₂ ((C₁ , (_ , _)) ∷ _ ∷ _ , ∧l₁T f ∷ f1' ∷ fs' , refl , refl , isOK2isOKC₁ _ f1' ok)
check-focus {.(just (_ ∧ _)) , snd} (f2li (∧l₂ f)) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) =
  inj₂ ((C₂ , (_ , _)) ∷ _ ∷ _ , ∧l₂T f ∷ f1' ∷ fs' , refl , refl , isOK2isOKC₂ _ f1' ok)
check-focus {S , p} (f2li (∨r₁ l {S = (S , q)} ok₁ f)) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) 
  rewrite isIrr-unique S q p = 
    inj₂ ((R , (_ ∨ _ , _)) ∷ _ ∷ _ , ∨r₁T l ok₁ f ∷ f1' ∷ fs' , refl , refl , _)
check-focus {S , p} (f2li (∨r₂ l {S = (S , q)} ok₁ f)) (.(f2li (untagF f1')) ∷ .(f2li-fs (untagF-fs fs' refl))) | inj₂ (.(_ ∷ _) , f1' ∷ fs' , refl , refl , ok) 
  rewrite isIrr-unique S q p = 
    inj₂ ((R , (_ ∨ _ , _)) ∷ _ ∷ _ , ∨r₂T l ok₁ f ∷ f1' ∷ fs' , refl , refl , _)

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

gen⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos} {Ψ : List Fma}
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (eq : Ψ ≡ pos C ∷ mapList (λ x → pos x) Φ)
  → (SF : SubFmas Ψ A)
  → - ∣ Δ ⊢ri B
  → S ∣ Γ ++ Δ ⊢li (A ⊗ B , _)
gen⊗r-li (⊗l f) fs eq SF g = ⊗l (gen⊗r-li f (⊗l-inv-fs fs) eq SF g)
gen⊗r-li (Il f) fs eq SF g = Il (gen⊗r-li f (Il-inv-fs fs) eq SF g)
gen⊗r-li (∨l f f') fs eq SF g = ∨l (gen⊗r-li f (∨l-inv-fs₁ fs) eq SF g) (gen⊗r-li f' (∨l-inv-fs₂ fs) eq SF g)
gen⊗r-li (f2li {S = S} f) fs eq SF g with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = f2li (∧l₁ (gen⊗r-li f' fs' eq SF g))
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = f2li (∧l₂ (gen⊗r-li f' fs' eq SF g))
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = f2li (pass (gen⊗r-li f' fs' eq SF g))
... | inj₂ (tp ∷ Ψ , f ∷ fs' , refl , refl , ok) = 
  f2li (⊗r (mapList proj₁ (tp ∷ Ψ)) ok refl (∧rT* (f ∷ fs') SF (trans eq (projCompose (tp ∷ Ψ)))) g)

gen∨r₁-li : {S : Stp} {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos} {Ψ : List Fma}
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (eq : Ψ ≡ pos C ∷ mapList (λ x → pos x) Φ)
  → (SF : SubFmas Ψ A)
  → S ∣ Γ ⊢li (A ∨ B , _)
gen∨r₁-li (⊗l f) fs eq SF = ⊗l (gen∨r₁-li f (⊗l-inv-fs fs) eq SF)
gen∨r₁-li (Il f) fs eq SF = Il (gen∨r₁-li f (Il-inv-fs fs) eq SF)
gen∨r₁-li (∨l f f') fs eq SF = ∨l (gen∨r₁-li f (∨l-inv-fs₁ fs) eq SF) (gen∨r₁-li f' (∨l-inv-fs₂ fs) eq SF)
gen∨r₁-li (f2li {S = S} f) fs eq SF with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = f2li (∧l₁ (gen∨r₁-li f' fs' eq SF))
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = f2li (∧l₂ (gen∨r₁-li f' fs' eq SF))
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = f2li (pass (gen∨r₁-li f' fs' eq SF))
... | inj₂ (tp ∷ Ψ , f ∷ fs' , refl , refl , ok) = 
  f2li (∨r₁ (mapList proj₁ (tp ∷ Ψ)) ok (∧rT* (f ∷ fs') SF (trans eq (projCompose (tp ∷ Ψ)))))

gen∨r₂-li : {S : Stp} {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos} {Ψ : List Fma}
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (eq : Ψ ≡ pos C ∷ mapList (λ x → pos x) Φ)
  → (SF : SubFmas Ψ B)
  → S ∣ Γ ⊢li (A ∨ B , _)
gen∨r₂-li (⊗l f) fs eq SF = ⊗l (gen∨r₂-li f (⊗l-inv-fs fs) eq SF)
gen∨r₂-li (Il f) fs eq SF = Il (gen∨r₂-li f (Il-inv-fs fs) eq SF)
gen∨r₂-li (∨l f f') fs eq SF = ∨l (gen∨r₂-li f (∨l-inv-fs₁ fs) eq SF) (gen∨r₂-li f' (∨l-inv-fs₂ fs) eq SF)
gen∨r₂-li (f2li {S = S} f) fs eq SF with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = f2li (∧l₁ (gen∨r₂-li f' fs' eq SF))
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = f2li (∧l₂ (gen∨r₂-li f' fs' eq SF))
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = f2li (pass (gen∨r₂-li f' fs' eq SF))
... | inj₂ (tp ∷ Ψ , f ∷ fs' , refl , refl , ok) = 
  f2li (∨r₂ (mapList proj₁ (tp ∷ Ψ)) ok (∧rT* (f ∷ fs') SF (trans eq (projCompose (tp ∷ Ψ)))))

fsDist-white : {S : Stp} {Γ : Cxt} {Θ : List Pos}
  → (Φ Ψ : List Fma) (fs : All (λ C → S ∣ Γ ⊢li C) Θ) (eq : Φ ++ Ψ ≡ mapList (λ x → proj₁ x) Θ)
  → Σ (List Pos) λ Θ₁ → Σ (List Pos) λ Θ₂
    → All (λ C → S ∣ Γ ⊢li C) Θ₁ × All (λ C → S ∣ Γ ⊢li C) Θ₂ × Θ ≡ Θ₁ ++ Θ₂ × Φ ≡ mapList (λ x → proj₁ x) Θ₁ × Ψ ≡ mapList (λ x → proj₁ x) Θ₂
fsDist-white [] [] [] refl = [] , [] , [] , [] , refl , refl , refl
fsDist-white [] (A ∷ Ψ) (f ∷ fs) refl = [] , _ ∷ _ , [] , f ∷ fs , refl , refl , refl
fsDist-white (A ∷ Φ) Ψ (f ∷ fs) eq with fsDist-white Φ Ψ fs (proj₂ (inj∷ eq))
fsDist-white (._ ∷ .(mapList (λ x → proj₁ x) Θ₁)) .(mapList (λ x → proj₁ x) Θ₂) (f ∷ fs) refl | Θ₁ , Θ₂ , fs1 , fs2 , refl , refl , refl = 
  _ ∷ Θ₁ , Θ₂ , f ∷ fs1 , fs2 , refl , refl , refl

∧r* : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Pos} {Ψ : List Fma}
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas Ψ A)
  → (eq : Ψ ≡ mapList (λ x → proj₁ x) Φ)
  → S ∣ Γ ⊢ri A
∧r* fs (conj {Φ} {Ψ} {A' = A} {B' = B} SF1 SF2) eq with fsDist-white (A ∷ Φ) (B ∷ Ψ) fs eq
... | P1 ∷ Θ1 , P2 ∷ Θ2 , fs1 , fs2 , refl , refl , refl = ∧r (∧r* fs1 SF1 refl) (∧r* fs2 SF2 refl) -- ∧r (∧r* fs1 SF1 eq2) (∧r* fs2 SF2 eq3)
∧r* (f ∷ []) stop refl = li2ri f

fsDist-white-refl : {S : Stp} {Γ : Cxt} {P1 P2 : Pos}
  → {Φ Ψ : List Pos}
  → (fs : All (λ C → S ∣ Γ ⊢li C) (P1 ∷ Φ))
  → (gs : All (λ C → S ∣ Γ ⊢li C) (P2 ∷ Ψ))
  → fsDist-white (mapList (λ z → proj₁ z) (P1 ∷ Φ)) (mapList (λ z → proj₁ z) (P2 ∷ Ψ)) (All++ fs gs) refl ≡ (P1 ∷ Φ , P2 ∷ Ψ , fs , gs , refl , refl , refl)
fsDist-white-refl (f ∷ []) (g ∷ []) = refl
fsDist-white-refl (f ∷ []) (g1 ∷ g2 ∷ gs) = refl
fsDist-white-refl (f1 ∷ f2 ∷ fs) gs rewrite fsDist-white-refl (f2 ∷ fs) gs = refl
{-# REWRITE fsDist-white-refl #-}

f2fs : {S : Stp} {Γ : Cxt} {A : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → Σ (List Pos) λ Φ → Σ (All (λ C → S ∣ Γ ⊢li C) Φ) λ fs → Σ (List Fma) λ Ψ → Σ (SubFmas Ψ A) λ SF → Σ (Ψ ≡ mapList (λ x → proj₁ x) Φ) λ eq → f ≡ ∧r* fs SF eq
f2fs (∧r f g) with f2fs f | f2fs g
... | P1 ∷ Φ1 , fs , .(proj₁ P1) ∷ .(mapList (λ x → proj₁ x) Φ1) , SF1 , refl , refl | P2 ∷ Φ2 , gs , .(proj₁ P2) ∷ .(mapList (λ x → proj₁ x) Φ2) , SF2 , refl , refl = 
    (P1 ∷ Φ1) ++ (P2 ∷ Φ2) , All++ fs gs , (proj₁ P1) ∷ (mapList (λ x → proj₁ x) Φ1) ++ (proj₁ P2) ∷ (mapList (λ x → proj₁ x) Φ2) , conj SF1 SF2 , refl , refl
f2fs (li2ri {C = C} f) = C ∷ [] , f ∷ [] , proj₁ C ∷ [] , stop , refl , refl

-- f2fs-refl : {S : Stp} {Γ : Cxt} {A : Fma}
--   → {Φ : List Fma}
--   → (fs : List (Σ Pos (_∣_⊢li_ S Γ)))
--   → (SF : SubFmas Φ A)
--   → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
--   → f2fs (∧r* fs SF eq) ≡ (fs , Φ , eq , SF , refl)
-- f2fs-refl {S} {Γ} fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
-- f2fs-refl {S} {Γ} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl
--   rewrite f2fs-refl ((C , f) ∷ fs') SF1 refl | f2fs-refl ((C' , f') ∷ fs'') SF2 refl = refl
-- f2fs-refl (x ∷ []) stop refl = refl

⊗r-ri : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → (g : - ∣ Δ ⊢ri B)
  → S ∣ Γ ++ Δ ⊢ri A ⊗ B
⊗r-ri {A = A} f g with f2fs f
... | .[] , [] , .[] , () , refl , eq2
... | .(_ ∷ _) , f ∷ fs , Ψ , SF , eq1 , refl = li2ri (gen⊗r-li f fs eq1 SF g)

∨r₁-ri : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → S ∣ Γ ⊢ri A ∨ B
∨r₁-ri f with f2fs f
... | .[] , [] , .[] , () , refl , eq2
... | .(_ ∷ _) , f ∷ fs , Ψ , SF , eq1 , refl = li2ri (gen∨r₁-li f fs eq1 SF)

∨r₂-ri : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri B)
  → S ∣ Γ ⊢ri A ∨ B
∨r₂-ri f with f2fs f
... | .[] , [] , .[] , () , refl , eq2
... | .(_ ∷ _) , f ∷ fs , Ψ , SF , eq1 , refl = li2ri (gen∨r₂-li f fs eq1 SF)

-- admissible rules, except ⊗r-ri, ∨r₁-ri, and ∨r₂-ri
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

ax-ri : {C : Fma} → just C ∣ [] ⊢ri C
ax-ri {C = ` x} = li2ri (f2li ax)
ax-ri {C = I} = li2ri (Il (f2li Ir))
ax-ri {C = C ⊗ C'} = ⊗l-ri (⊗r-ri ax-ri (pass-ri ax-ri))
ax-ri {C = C ∧ C'} = ∧r (∧l₁-ri ax-ri) (∧l₂-ri ax-ri)
ax-ri {C ∨ C'} = ∨l-ri (∨r₁-ri ax-ri) (∨r₂-ri ax-ri)

-- focus function maps each derivation in SeqCalc to a focused derivation.
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

-- each emb function maps derivations in a certain phase to a non-focused derivation
mutual
  emb-ri : {S : Stp} {Γ : Cxt} {C : Fma}
    → (f : S ∣ Γ ⊢ri C)
    → S ∣ Γ ⊢ C
  emb-ri (∧r f f₁) = ∧r (emb-ri f) (emb-ri f₁)
  emb-ri (li2ri f) = emb-li f

  emb-riT : {l : List Tag} {S : Irr} {Γ : Cxt} {C : Fma}
    → (f : l ∣ S ∣ Γ ⊢riT C)
    → irr S ∣ Γ ⊢ C
  emb-riT (∧rT f f₁) = ∧r (emb-riT f) (emb-riT f₁)
  emb-riT (f2riT f) = emb-fT f

  emb-li : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    → S ∣ Γ ⊢ pos C
  emb-li (⊗l f) = ⊗l (emb-li f)
  emb-li (Il f) = Il (emb-li f)
  emb-li (∨l f g) = ∨l (emb-li f) (emb-li g)
  emb-li (f2li f) = emb-f f

  emb-f : {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢f C)
    → irr S ∣ Γ ⊢ pos C
  emb-f ax = ax
  emb-f Ir = Ir
  emb-f (pass f) = pass (emb-li f)
  emb-f (⊗r l ok refl f g) = ⊗r (emb-riT f) (emb-ri g)
  emb-f (∧l₁ f) = ∧l₁ (emb-li f)
  emb-f (∧l₂ f) = ∧l₂ (emb-li f)
  emb-f (∨r₁ l ok f) = ∨r₁ (emb-riT f)
  emb-f (∨r₂ l ok f) = ∨r₂ (emb-riT f)

  emb-fT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : t ∣ S ∣ Γ ⊢fT C)
    → irr S ∣ Γ ⊢ pos C
  emb-fT ax = ax
  emb-fT Ir = Ir
  emb-fT (passT f) = pass (emb-li f)
  emb-fT (⊗rT l ok refl f g) = ⊗r (emb-riT f) (emb-ri g)
  emb-fT (∧l₁T f) = ∧l₁ (emb-li f)
  emb-fT (∧l₂T f) = ∧l₂ (emb-li f)
  emb-fT (∨r₁T l ok f) = ∨r₁ (emb-riT f)
  emb-fT (∨r₂T l ok f) = ∨r₂ (emb-riT f)
        