{-# OPTIONS --rewriting #-}

module Embfocus where

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

open import Utilities
open import Formulae
open import SeqCalc
open import Focusing
open import CheckFocus
open import TagUntag
open import FocusingProperties


{-
We show that every derivation in SeqCalc is ≗-to the its normal form, 
i.e. emb-ri (focus f) ≗ f
-}

fsDist-seq : {S : Stp} {Γ : Cxt} {Θ : List Pos}
  → (Θ₁ Θ₂ : List Pos) (fs : All (λ C → S ∣ Γ ⊢ pos C) Θ) (eq : Θ₁ ++ Θ₂ ≡ Θ)
  → Σ (All (λ C → S ∣ Γ ⊢ pos C) Θ₁) λ fs1 → Σ (All (λ C → S ∣ Γ ⊢ pos C) Θ₂) λ fs2 → fs ≡ subst (λ x → All (λ C → S ∣ Γ ⊢ pos C) x) eq (All++ fs1 fs2)
fsDist-seq [] [] [] refl = [] , [] , refl
fsDist-seq [] .(_ ∷ _) (f ∷ fs) refl = [] , _ ∷ _ , refl
fsDist-seq (x ∷ Θ₁) Θ₂ (f ∷ fs) eq with fsDist-seq Θ₁ Θ₂ fs (proj₂ (inj∷ eq))
fsDist-seq (x ∷ Θ₁) Θ₂ (f ∷ .(subst (All (λ C → _ ∣ _ ⊢ proj₁ C)) _ (All++ fs1 fs2))) refl | fs1 , fs2 , refl = f ∷ fs1 , fs2 , refl

fsDist-seq-refl : {S : Stp} {Γ : Cxt}
  → {Φ Ψ : List Pos}
  → (fs : All (λ C → S ∣ Γ ⊢ pos C) Φ)
  → (gs : All (λ C → S ∣ Γ ⊢ pos C) Ψ)
  → fsDist-seq Φ Ψ (All++ fs gs) refl ≡ (fs , gs , refl)
fsDist-seq-refl [] [] = refl
fsDist-seq-refl [] (g ∷ gs) = refl
fsDist-seq-refl (f ∷ fs) gs rewrite fsDist-seq-refl fs gs = refl

-- several ∧r in one step in SeqCalc
∧r*-seq : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Pos}
  → (fs : All (λ C → S ∣ Γ ⊢ pos C) Φ)
  → (SF : SubFmas Φ A)
  → S ∣ Γ ⊢ A
∧r*-seq fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-seq Φ Ψ fs refl
... | fs1 , fs2 , refl = ∧r (∧r*-seq fs1 SF1) (∧r*-seq fs2 SF2)
∧r*-seq (f ∷ []) stop = f

emb-li-fs : {S : Stp} {Γ : Cxt}
  → {Φ : List Pos}
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → All (λ C → S ∣ Γ ⊢ pos C) Φ
emb-li-fs [] = []
emb-li-fs (f ∷ fs) = emb-li f ∷ emb-li-fs fs

emb-li-fs-All++ : {S : Stp} {Γ : Cxt} {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ S Γ) Φ)
  → (fs2 : All (_∣_⊢li_ S Γ) Ψ)
  → emb-li-fs (All++ fs1 fs2) ≡ All++ (emb-li-fs fs1) (emb-li-fs fs2)
emb-li-fs-All++ [] fs2 = refl
emb-li-fs-All++ (f1 ∷ fs1) fs2 = cong (emb-li f1 ∷_) (emb-li-fs-All++ fs1 fs2)

emb-fT-fs : {S : Irr} {Γ : Cxt}
  → {Φ : List (Tag × Pos)}
  → (fs : All (match-fT S Γ) Φ)
  → All (λ C → irr S ∣ Γ ⊢ pos C) (mapList proj₂ Φ)
emb-fT-fs [] = []
emb-fT-fs (f ∷ fs) = emb-fT f ∷ emb-fT-fs fs

⊗l-inv-fs-All++ : {Γ : Cxt} {A B : Fma}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just (A ⊗ B)) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just (A ⊗ B)) Γ) Ψ)
  → ⊗l-inv-fs (All++ fs1 fs2) ≡ All++ (⊗l-inv-fs fs1) (⊗l-inv-fs fs2)
⊗l-inv-fs-All++ [] fs2 = refl
⊗l-inv-fs-All++ (⊗l f1 ∷ fs1) fs2 = cong (f1 ∷_) (⊗l-inv-fs-All++ fs1 fs2)

Il-inv-fs-All++ : {Γ : Cxt}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just I) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just I) Γ) Ψ)
  → Il-inv-fs (All++ fs1 fs2) ≡ All++ (Il-inv-fs fs1) (Il-inv-fs fs2)
Il-inv-fs-All++ [] fs2 = refl
Il-inv-fs-All++ (Il f1 ∷ fs1) fs2 = cong (f1 ∷_) (Il-inv-fs-All++ fs1 fs2)

∨l-inv-fs₁-All++ : {Γ : Cxt} {A B : Fma}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just (A ∨ B)) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just (A ∨ B)) Γ) Ψ)
  → ∨l-inv-fs₁ (All++ fs1 fs2) ≡ All++ (∨l-inv-fs₁ fs1) (∨l-inv-fs₁ fs2)
∨l-inv-fs₁-All++ [] fs2 = refl
∨l-inv-fs₁-All++ (∨l f1 f2 ∷ fs1) fs2 = cong (f1 ∷_) (∨l-inv-fs₁-All++ fs1 fs2)

∨l-inv-fs₂-All++ : {Γ : Cxt} {A B : Fma}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just (A ∨ B)) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just (A ∨ B)) Γ) Ψ)
  → ∨l-inv-fs₂ (All++ fs1 fs2) ≡ All++ (∨l-inv-fs₂ fs1) (∨l-inv-fs₂ fs2)
∨l-inv-fs₂-All++ [] fs2 = refl
∨l-inv-fs₂-All++ (∨l f1 f2 ∷ fs1) fs2 = cong (f2 ∷_) (∨l-inv-fs₂-All++ fs1 fs2)

f2li-fs-All++ : {S : Irr} {Γ : Cxt}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢f_ S Γ) Φ)
  → (fs2 : All (_∣_⊢f_ S Γ) Ψ)
  → f2li-fs (All++ fs1 fs2) ≡ All++ (f2li-fs fs1) (f2li-fs fs2)
f2li-fs-All++ [] fs2 = refl
f2li-fs-All++ (f1 ∷ fs1) fs2 = cong (f2li f1 ∷_) (f2li-fs-All++ fs1 fs2)

∧l₁-fs-All++ : {Γ : Cxt} {A B : Fma}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just A) Γ) Ψ)
  → ∧l₁-fs {B = B} (All++ fs1 fs2) ≡ All++ (∧l₁-fs fs1) (∧l₁-fs fs2)
∧l₁-fs-All++ [] fs2 = refl
∧l₁-fs-All++ (f1 ∷ fs1) fs2 = cong (∧l₁ f1 ∷_) (∧l₁-fs-All++ fs1 fs2)

∧l₂-fs-All++ : {Γ : Cxt} {A B : Fma}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just B) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just B) Γ) Ψ)
  → ∧l₂-fs {A = A} (All++ fs1 fs2) ≡ All++ (∧l₂-fs fs1) (∧l₂-fs fs2)
∧l₂-fs-All++ [] fs2 = refl
∧l₂-fs-All++ (f1 ∷ fs1) fs2 = cong (∧l₂ f1 ∷_) (∧l₂-fs-All++ fs1 fs2)

pass-fs-All++ : {Γ : Cxt} {A : Fma}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just A) Γ) Ψ)
  → pass-fs (All++ fs1 fs2) ≡ All++ (pass-fs fs1) (pass-fs fs2)
pass-fs-All++ [] fs2 = refl
pass-fs-All++ (f1 ∷ fs1) fs2 = cong (pass f1 ∷_) (pass-fs-All++ fs1 fs2)

emb∧r*-seq : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ S Γ) Φ) 
  → (SF : SubFmas Φ A)
  → ∧r*-seq (emb-li-fs fs) SF ≗ emb-ri (∧r* fs SF)
emb∧r*-seq fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite emb-li-fs-All++ fs1 fs2 | fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) = 
    ∧r (emb∧r*-seq fs1 SF1) (emb∧r*-seq fs2 SF2)
emb∧r*-seq (f ∷ []) stop = refl

∧r*-seq-⊗l : {Γ : Cxt} {A B C : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just (A ⊗ B)) Γ) Φ)
  → (SF : SubFmas Φ C)
  → ⊗l (∧r*-seq (emb-li-fs (⊗l-inv-fs fs)) SF) ≗ ∧r*-seq (emb-li-fs fs) SF
∧r*-seq-⊗l fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite emb-li-fs-All++ fs1 fs2 | 
          fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) | 
          ⊗l-inv-fs-All++ fs1 fs2 | 
          emb-li-fs-All++ (⊗l-inv-fs fs1) (⊗l-inv-fs fs2) |
          fsDist-seq-refl (emb-li-fs (⊗l-inv-fs fs1)) (emb-li-fs (⊗l-inv-fs fs2)) = 
            ~ ∧r⊗l ∙ ∧r (∧r*-seq-⊗l fs1 SF1) (∧r*-seq-⊗l fs2 SF2)
∧r*-seq-⊗l (⊗l f ∷ []) stop = refl

∧r*-seq-Il : {Γ : Cxt} {A : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just I) Γ) Φ)
  → (SF : SubFmas Φ A)
  → Il (∧r*-seq (emb-li-fs (Il-inv-fs fs)) SF) ≗ ∧r*-seq (emb-li-fs fs) SF
∧r*-seq-Il fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite emb-li-fs-All++ fs1 fs2 | 
          fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) | 
          Il-inv-fs-All++ fs1 fs2 | 
          emb-li-fs-All++ (Il-inv-fs fs1) (Il-inv-fs fs2) |
          fsDist-seq-refl (emb-li-fs (Il-inv-fs fs1)) (emb-li-fs (Il-inv-fs fs2)) = 
            ~ ∧rIl ∙ ∧r (∧r*-seq-Il fs1 SF1) (∧r*-seq-Il fs2 SF2)
∧r*-seq-Il (Il f ∷ []) stop = refl

∧r*-seq-∨l : {Γ : Cxt} {A B C : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just (A ∨ B)) Γ) Φ)
  → (SF : SubFmas Φ C)
  → ∨l (∧r*-seq (emb-li-fs (∨l-inv-fs₁ fs)) SF) (∧r*-seq (emb-li-fs (∨l-inv-fs₂ fs)) SF) 
    ≗ ∧r*-seq (emb-li-fs fs) SF
∧r*-seq-∨l fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl
  rewrite emb-li-fs-All++ fs1 fs2 | 
          fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) | 
          ∨l-inv-fs₁-All++ fs1 fs2 |
          emb-li-fs-All++ (∨l-inv-fs₁ fs1) (∨l-inv-fs₁ fs2) |
          fsDist-seq-refl (emb-li-fs (∨l-inv-fs₁ fs1)) (emb-li-fs (∨l-inv-fs₁ fs2)) |
          ∨l-inv-fs₂-All++ fs1 fs2 |
          emb-li-fs-All++ (∨l-inv-fs₂ fs1) (∨l-inv-fs₂ fs2) |
          fsDist-seq-refl (emb-li-fs (∨l-inv-fs₂ fs1)) (emb-li-fs (∨l-inv-fs₂ fs2)) = 
            ~ ∧r∨l ∙ ∧r (∧r*-seq-∨l fs1 SF1) (∧r*-seq-∨l fs2 SF2)
∧r*-seq-∨l (∨l f g ∷ []) stop = refl

∧r*-seq-∧l₁ : {Γ : Cxt} {A B C : Fma} 
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just A) Γ) Φ)
  → (SF : SubFmas Φ C)
  → ∧l₁ {B = B} (∧r*-seq (emb-li-fs fs) SF) ≗
      ∧r*-seq (emb-li-fs (f2li-fs (∧l₁-fs fs))) SF
∧r*-seq-∧l₁ {B = B} fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite emb-li-fs-All++ fs1 fs2 | 
          fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) | 
          ∧l₁-fs-All++ {B = B} fs1 fs2 | 
          f2li-fs-All++ (∧l₁-fs {B = B} fs1) (∧l₁-fs fs2) |
          emb-li-fs-All++ (f2li-fs (∧l₁-fs {B = B} fs1)) (f2li-fs (∧l₁-fs fs2)) |
          fsDist-seq-refl (emb-li-fs (f2li-fs (∧l₁-fs {B = B} fs1))) (emb-li-fs (f2li-fs (∧l₁-fs fs2))) = 
            ~ ∧r∧l₁ ∙ ∧r (∧r*-seq-∧l₁ fs1 SF1) (∧r*-seq-∧l₁ fs2 SF2)
∧r*-seq-∧l₁ (f  ∷ []) stop = refl

∧r*-seq-∧l₂ : {Γ : Cxt} {A B C : Fma} 
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just B) Γ) Φ)
  → (SF : SubFmas Φ C)
  → ∧l₂ {A = A} (∧r*-seq (emb-li-fs fs) SF) ≗
      ∧r*-seq (emb-li-fs (f2li-fs (∧l₂-fs fs))) SF
∧r*-seq-∧l₂ {A = A} fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite emb-li-fs-All++ fs1 fs2 | 
          fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) | 
          ∧l₂-fs-All++ {A = A} fs1 fs2 | 
          f2li-fs-All++ (∧l₂-fs {A = A} fs1) (∧l₂-fs fs2) |
          emb-li-fs-All++ (f2li-fs (∧l₂-fs {A = A} fs1)) (f2li-fs (∧l₂-fs fs2)) |
          fsDist-seq-refl (emb-li-fs (f2li-fs (∧l₂-fs {A = A} fs1))) (emb-li-fs (f2li-fs (∧l₂-fs fs2))) = 
            ~ ∧r∧l₂ ∙ ∧r (∧r*-seq-∧l₂ fs1 SF1) (∧r*-seq-∧l₂ fs2 SF2)
∧r*-seq-∧l₂ (f  ∷ []) stop = refl

∧r*-seq-pass : {Γ : Cxt} {A C : Fma} 
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just A) Γ) Φ)
  → (SF : SubFmas Φ C)
  → pass (∧r*-seq (emb-li-fs fs) SF) ≗
      ∧r*-seq (emb-li-fs (f2li-fs (pass-fs fs))) SF
∧r*-seq-pass fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite emb-li-fs-All++ fs1 fs2 | 
          fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) | 
          pass-fs-All++ fs1 fs2 | 
          f2li-fs-All++ (pass-fs fs1) (pass-fs fs2) |
          emb-li-fs-All++ (f2li-fs (pass-fs fs1)) (f2li-fs (pass-fs fs2)) |
          fsDist-seq-refl (emb-li-fs (f2li-fs (pass-fs fs1))) (emb-li-fs (f2li-fs (pass-fs fs2))) = 
            ~ ∧rpass ∙ ∧r (∧r*-seq-pass fs1 SF1) (∧r*-seq-pass fs2 SF2)
∧r*-seq-pass (f  ∷ []) stop = refl

∧r*-seq-emb-riT : {S : Irr} {Γ : Cxt} {A : Fma} 
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (irr S) Γ) Φ)
  → (SF : SubFmas Φ A)
  -- → (eq : Ψ ≡ mapList proj₂ Φ)
  → emb-riT (∧rT* (proj₂ (tagF-fs {S} fs)) SF refl) ≗
      ∧r*-seq (emb-li-fs fs) SF
∧r*-seq-emb-riT {S} fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl
  rewrite emb-li-fs-All++ fs1 fs2 | 
          fsDist-seq-refl (emb-li-fs fs1) (emb-li-fs fs2) |
          tagF-fs-All++ {S} fs1 fs2 |
           fsDist-refl (proj₂ (tagF-fs {S} fs1))  (proj₂ (tagF-fs {S} fs2)) = 
             ∧r (∧r*-seq-emb-riT fs1 SF1) (∧r*-seq-emb-riT fs2 SF2)
∧r*-seq-emb-riT (f2li ax ∷ []) stop = refl
∧r*-seq-emb-riT (f2li Ir ∷ []) stop = refl
∧r*-seq-emb-riT (f2li (pass f) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (just (` x) , q)) , p} (f2li {just (` x) , q} (⊗r l ok refl f g) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (just (x ∧ x₁) , q)) , p} (f2li {just (x ∧ x₁) , q} (⊗r l ok refl f g) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (- , q)) , p} (f2li { - , q} (⊗r l ok refl f g) ∷ []) stop = refl
∧r*-seq-emb-riT (f2li (∧l₁ f) ∷ []) stop = refl
∧r*-seq-emb-riT (f2li (∧l₂ f) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (just (` x) , q)) , p} (f2li {just (` x) , q} (∨r₁ l ok f) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (just (x ∧ x₁) , q)) , p} (f2li {just (x ∧ x₁) , q} (∨r₁ l ok f) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (- , q)) , p} (f2li { - , q} (∨r₁ l ok f) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (just (` x) , q)) , p} (f2li {just (` x) , q} (∨r₂ l ok f) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (just (x ∧ x₁) , q)) , p} (f2li {just (x ∧ x₁) , q} (∨r₂ l ok f) ∷ []) stop = refl
∧r*-seq-emb-riT {.(irr (- , q)) , p} (f2li { - , q} (∨r₂ l ok f) ∷ []) stop = refl

embgen⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma} {C : Pos}
  → {Φ Ψ : List Pos}
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas Ψ A)
  → (eq : Ψ ≡ C ∷ Φ)
  → (g : - ∣ Δ ⊢ri B)
  → emb-li (gen⊗r-li f fs (subst (λ x → SubFmas x A) eq SF) g) ≗ ⊗r (∧r*-seq (emb-li-fs (f ∷ fs)) ((subst (λ x → SubFmas x A) eq SF))) (emb-ri g)
embgen⊗r-li (⊗l f) fs SF refl g = 
  ⊗l (embgen⊗r-li f (⊗l-inv-fs fs) SF refl g) ∙ (~ ⊗r⊗l ∙ ⊗r (∧r*-seq-⊗l  (⊗l f ∷ fs) SF) refl)
embgen⊗r-li (Il f) fs SF refl g = 
  Il (embgen⊗r-li f (Il-inv-fs fs) SF refl g) ∙ (~ ⊗rIl ∙ ⊗r (∧r*-seq-Il  (Il f ∷ fs) SF) refl)
embgen⊗r-li (∨l f1 f2) fs SF refl g = 
  ∨l (embgen⊗r-li f1 (∨l-inv-fs₁ fs) SF refl g) (embgen⊗r-li f2 (∨l-inv-fs₂ fs) SF refl g) 
    ∙ (~ ⊗r∨l ∙ ⊗r (∧r*-seq-∨l  (∨l f1 f2 ∷ fs) SF) refl)
embgen⊗r-li (f2li {S = S} f) fs SF refl g with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = ∧l₁ (embgen⊗r-li f' fs' SF refl g) 
  ∙ (~ ⊗r∧l₁ ∙ ⊗r (∧r*-seq-∧l₁ (f' ∷ fs') SF) refl) 
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = ∧l₂ (embgen⊗r-li f' fs' SF refl g) 
  ∙ (~ ⊗r∧l₂ ∙ ⊗r (∧r*-seq-∧l₂ (f' ∷ fs') SF) refl) 
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = pass (embgen⊗r-li f' fs' SF refl g) 
  ∙ (~ ⊗rpass ∙ ⊗r (∧r*-seq-pass (f' ∷ fs') SF) refl) 
embgen⊗r-li {.(irr (just (` _) , tt))} (f2li {S = .(just (` _)) , .tt} ax) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ⊗r (∧r*-seq-emb-riT ((f2li ax) ∷ fs) SF) refl 
embgen⊗r-li {.(irr (- , tt))} (f2li {S = .- , .tt} Ir) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ⊗r (∧r*-seq-emb-riT ((f2li Ir) ∷ fs) SF) refl 
embgen⊗r-li {.(irr (- , tt))} (f2li {S = .- , .tt} (pass f)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ⊗r (∧r*-seq-emb-riT ((f2li (pass f)) ∷ fs) SF) refl 
embgen⊗r-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (⊗r l ok₁ eq f g)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ⊗r (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (⊗r l ok₁ eq f g)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ⊗r (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (- , snd))} (f2li {S = - , snd} (⊗r l ok₁ eq f g)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ⊗r (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (just (_ ∧ _) , tt))} (f2li {S = .(just (_ ∧ _)) , .tt} (∧l₁ f)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = ⊗r (∧r*-seq-emb-riT ((f2li (∧l₁ f)) ∷ fs) SF) refl 
embgen⊗r-li {.(irr (just (_ ∧ _) , tt))} (f2li {S = .(just (_ ∧ _)) , .tt} (∧l₂ f)) fs SF refl g' | inj₂ (.((C₂ , _) ∷ proj₁ (tagF-fs fs)) , .(∧l₂T f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ⊗r (∧r*-seq-emb-riT ((f2li (∧l₂ f)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (∨r₁ l ok₁ f)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ⊗r (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (∨r₁ l ok₁ f)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ⊗r (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (- , snd))} (f2li {S = - , snd} (∨r₁ l ok₁ f)) fs SF refl g' | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ⊗r (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (∨r₂ l ok₁ f)) fs SF refl g' | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ⊗r (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (∨r₂ l ok₁ f)) fs SF refl g' | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ⊗r (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF) refl
embgen⊗r-li {.(irr (- , snd))} (f2li {S = - , snd} (∨r₂ l ok₁ f)) fs SF refl g' | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ⊗r (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF) refl

embgen∨r₁-li : {S : Stp} {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ Ψ : List Pos}
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas Ψ A)
  → (eq : Ψ ≡ C ∷ Φ)
  → emb-li (gen∨r₁-li {B = B} f fs (subst (λ x → SubFmas x A) eq SF)) ≗ ∨r₁ (∧r*-seq (emb-li-fs (f ∷ fs)) ((subst (λ x → SubFmas x A) eq SF))) 
embgen∨r₁-li (⊗l f) fs SF refl = 
  ⊗l (embgen∨r₁-li f (⊗l-inv-fs fs) SF refl) ∙ (~ ∨r₁⊗l ∙ ∨r₁ (∧r*-seq-⊗l  (⊗l f ∷ fs) SF))
embgen∨r₁-li (Il f) fs SF refl = 
  Il (embgen∨r₁-li f (Il-inv-fs fs) SF refl) ∙ (~ ∨r₁Il ∙ ∨r₁ (∧r*-seq-Il  (Il f ∷ fs) SF))
embgen∨r₁-li (∨l f1 f2) fs SF refl = 
  ∨l (embgen∨r₁-li f1 (∨l-inv-fs₁ fs) SF refl) (embgen∨r₁-li f2 (∨l-inv-fs₂ fs) SF refl) 
    ∙ (~ ∨r₁∨l ∙ ∨r₁ (∧r*-seq-∨l  (∨l f1 f2 ∷ fs) SF))
embgen∨r₁-li (f2li {S = S} f) fs SF refl with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = ∧l₁ (embgen∨r₁-li f' fs' SF refl) 
  ∙ (~ ∨r₁∧l₁ ∙ ∨r₁ (∧r*-seq-∧l₁ (f' ∷ fs') SF)) 
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = ∧l₂ (embgen∨r₁-li f' fs' SF refl) 
  ∙ (~ ∨r₁∧l₂ ∙ ∨r₁ (∧r*-seq-∧l₂ (f' ∷ fs') SF)) 
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = pass (embgen∨r₁-li f' fs' SF refl) 
  ∙ (~ ∨r₁pass ∙ ∨r₁ (∧r*-seq-pass (f' ∷ fs') SF)) 
embgen∨r₁-li {.(irr (just (` _) , tt))} (f2li {S = .(just (` _)) , .tt} ax) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₁ (∧r*-seq-emb-riT ((f2li ax) ∷ fs) SF) 
embgen∨r₁-li {.(irr (- , tt))} (f2li {S = .- , .tt} Ir) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₁ (∧r*-seq-emb-riT ((f2li Ir) ∷ fs) SF) 
embgen∨r₁-li {.(irr (- , tt))} (f2li {S = .- , .tt} (pass f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₁ (∧r*-seq-emb-riT ((f2li (pass f)) ∷ fs) SF) 
embgen∨r₁-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (⊗r l ok₁ eq f g)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₁ (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF)
embgen∨r₁-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (⊗r l ok₁ eq f g)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₁ (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF)
embgen∨r₁-li {.(irr (- , snd))} (f2li {S = - , snd} (⊗r l ok₁ eq f g)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₁ (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF)
embgen∨r₁-li {.(irr (just (_ ∧ _) , tt))} (f2li {S = .(just (_ ∧ _)) , .tt} (∧l₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = ∨r₁ (∧r*-seq-emb-riT ((f2li (∧l₁ f)) ∷ fs) SF) 
embgen∨r₁-li {.(irr (just (_ ∧ _) , tt))} (f2li {S = .(just (_ ∧ _)) , .tt} (∧l₂ f)) fs SF refl | inj₂ (.((C₂ , _) ∷ proj₁ (tagF-fs fs)) , .(∧l₂T f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₁ (∧r*-seq-emb-riT ((f2li (∧l₂ f)) ∷ fs) SF)
embgen∨r₁-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (∨r₁ l ok₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₁ (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF)
embgen∨r₁-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (∨r₁ l ok₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₁ (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF)
embgen∨r₁-li {.(irr (- , snd))} (f2li {S = - , snd} (∨r₁ l ok₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₁ (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF)
embgen∨r₁-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (∨r₂ l ok₁ f)) fs SF refl | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₁ (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF)
embgen∨r₁-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (∨r₂ l ok₁ f)) fs SF refl | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₁ (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF)
embgen∨r₁-li {.(irr (- , snd))} (f2li {S = - , snd} (∨r₂ l ok₁ f)) fs SF refl | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₁ (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF)

embgen∨r₂-li : {S : Stp} {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ Ψ : List Pos}
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas Ψ B)
  → (eq : Ψ ≡ C ∷ Φ)
  → emb-li (gen∨r₂-li {A = A} f fs (subst (λ x → SubFmas x B) eq SF)) ≗ ∨r₂ (∧r*-seq (emb-li-fs (f ∷ fs)) ((subst (λ x → SubFmas x B) eq SF))) 
embgen∨r₂-li (⊗l f) fs SF refl = 
  ⊗l (embgen∨r₂-li f (⊗l-inv-fs fs) SF refl) ∙ (~ ∨r₂⊗l ∙ ∨r₂ (∧r*-seq-⊗l  (⊗l f ∷ fs) SF))
embgen∨r₂-li (Il f) fs SF refl = 
  Il (embgen∨r₂-li f (Il-inv-fs fs) SF refl) ∙ (~ ∨r₂Il ∙ ∨r₂ (∧r*-seq-Il  (Il f ∷ fs) SF))
embgen∨r₂-li (∨l f1 f2) fs SF refl = 
  ∨l (embgen∨r₂-li f1 (∨l-inv-fs₁ fs) SF refl) (embgen∨r₂-li f2 (∨l-inv-fs₂ fs) SF refl) 
    ∙ (~ ∨r₂∨l ∙ ∨r₂ (∧r*-seq-∨l  (∨l f1 f2 ∷ fs) SF))
embgen∨r₂-li {S1} (f2li {S = S} f) fs SF refl with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = ∧l₁ (embgen∨r₂-li f' fs' SF refl) 
  ∙ (~ ∨r₂∧l₁ ∙ ∨r₂ (∧r*-seq-∧l₁ (f' ∷ fs') SF)) 
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = ∧l₂ (embgen∨r₂-li f' fs' SF refl) 
  ∙ (~ ∨r₂∧l₂ ∙ ∨r₂ (∧r*-seq-∧l₂ (f' ∷ fs') SF)) 
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = pass (embgen∨r₂-li f' fs' SF refl) 
  ∙ (~ ∨r₂pass ∙ ∨r₂ (∧r*-seq-pass (f' ∷ fs') SF)) 
embgen∨r₂-li {.(irr (just (` _) , tt))} (f2li {S = .(just (` _)) , .tt} ax) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₂ (∧r*-seq-emb-riT ((f2li ax) ∷ fs) SF) 
embgen∨r₂-li {.(irr (- , tt))} (f2li {S = .- , .tt} Ir) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₂ (∧r*-seq-emb-riT ((f2li Ir) ∷ fs) SF) 
embgen∨r₂-li {.(irr (- , tt))} (f2li {S = .- , .tt} (pass f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₂ (∧r*-seq-emb-riT ((f2li (pass f)) ∷ fs) SF) 
embgen∨r₂-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (⊗r l ok₁ eq f g)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₂ (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF)
embgen∨r₂-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (⊗r l ok₁ eq f g)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₂ (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF)
embgen∨r₂-li {.(irr (- , snd))} (f2li {S = - , snd} (⊗r l ok₁ eq f g)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₂ (∧r*-seq-emb-riT ((f2li (⊗r l ok₁ eq f g)) ∷ fs) SF)
embgen∨r₂-li {.(irr (just (_ ∧ _) , tt))} (f2li {S = .(just (_ ∧ _)) , .tt} (∧l₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = ∨r₂ (∧r*-seq-emb-riT ((f2li (∧l₁ f)) ∷ fs) SF) 
embgen∨r₂-li {.(irr (just (_ ∧ _) , tt))} (f2li {S = .(just (_ ∧ _)) , .tt} (∧l₂ f)) fs SF refl | inj₂ (.((C₂ , _) ∷ proj₁ (tagF-fs fs)) , .(∧l₂T f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₂ (∧r*-seq-emb-riT ((f2li (∧l₂ f)) ∷ fs) SF)
embgen∨r₂-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (∨r₁ l ok₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₂ (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF)
embgen∨r₂-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (∨r₁ l ok₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) = 
  ∨r₂ (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF)
embgen∨r₂-li {.(irr (- , snd))} (f2li {S = - , snd} (∨r₁ l ok₁ f)) fs SF refl | inj₂ (.(_ ∷ _) , f'' ∷ fs' , refl , refl , ok) =
  ∨r₂ (∧r*-seq-emb-riT ((f2li (∨r₁ l ok₁ f)) ∷ fs) SF)
embgen∨r₂-li {.(irr (just (` x) , snd))} (f2li {S = just (` x) , snd} (∨r₂ l ok₁ f)) fs SF refl | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₂ (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF)
embgen∨r₂-li {.(irr (just (x ∧ x₁) , snd))} (f2li {S = just (x ∧ x₁) , snd} (∨r₂ l ok₁ f)) fs SF refl | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₂ (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF)
embgen∨r₂-li {.(irr (- , snd))} (f2li {S = - , snd} (∨r₂ l ok₁ f)) fs SF refl | inj₂ (.((R , _ ∨ _ , tt) ∷ proj₁ (tagF-fs fs)) , .(∨r₂T l ok₁ f) ∷ .(proj₂ (tagF-fs fs)) , refl , refl , ok) = ∨r₂ (∧r*-seq-emb-riT ((f2li (∨r₂ l ok₁ f)) ∷ fs) SF)


emb⊗r : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → emb-ri (⊗r-ri f g) ≗ ⊗r (emb-ri f) (emb-ri g)
emb⊗r f g with f2fs f
... | .[] , [] , SF , refl = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl =  embgen⊗r-li f fs SF refl g ∙ ⊗r (emb∧r*-seq (f ∷ fs) SF) refl

emb∨r₁ : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → emb-ri (∨r₁-ri {B = B} f) ≗ ∨r₁ (emb-ri f)
emb∨r₁ {B = B} f with f2fs f
... | .[] , [] , SF , refl = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl =  embgen∨r₁-li f fs SF refl ∙ ∨r₁ (emb∧r*-seq (f ∷ fs) SF)

emb∨r₂ : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri B)
  → emb-ri (∨r₂-ri {A = A} f) ≗ ∨r₂ (emb-ri f)
emb∨r₂ {A = A} f with f2fs f
... | .[] , [] , SF , refl = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl = embgen∨r₂-li f fs SF refl ∙ ∨r₂ (emb∧r*-seq (f ∷ fs) SF)

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
emb⊗l (∧r f g) = ∧r (emb⊗l f) (emb⊗l g) ∙ (∧r⊗l ∙ ⊗l refl)
emb⊗l (li2ri f) = refl

emb∧l₁ : {Γ : Cxt} {A B C : Fma}
  → (f : just A ∣ Γ ⊢ri C)
  → emb-ri (∧l₁-ri {B = B} f) ≗ ∧l₁ (emb-ri f)
emb∧l₁ (∧r f g) = ∧r (emb∧l₁ f) (emb∧l₁ g) ∙ (∧r∧l₁ ∙ ∧l₁ refl)
emb∧l₁ (li2ri f) = refl

emb∧l₂ : {Γ : Cxt} {A B C : Fma}
  → (f : just B ∣ Γ ⊢ri C)
  → emb-ri (∧l₂-ri {A = A} f) ≗ ∧l₂ (emb-ri f)
emb∧l₂ (∧r f g) = ∧r (emb∧l₂ f) (emb∧l₂ g) ∙ (∧r∧l₂ ∙ ∧l₂ refl)
emb∧l₂ (li2ri f) = refl

embpass : {Γ : Cxt} {A C : Fma}
  → (f : just A ∣ Γ ⊢ri C)
  → emb-ri (pass-ri f) ≗ pass (emb-ri f)
embpass (∧r f g) = ∧r (embpass f) (embpass g) ∙ ∧rpass
embpass (li2ri f) = refl

embax : {D : Fma}
  → emb-ri (ax-ri {C = D}) ≗ ax
embax {` x} = refl
embax {I} = ~ axI
embax {D1 ⊗ D2} = 
  emb⊗l (⊗r-ri ax-ri (pass-ri ax-ri)) 
  ∙ (⊗l (emb⊗r ax-ri (pass-ri ax-ri)) ∙ (⊗l (⊗r embax (embpass ax-ri ∙ pass embax)) ∙ (~ ax⊗)))
embax {D1 ∧ D2} = ∧r (emb∧l₁ ax-ri) (emb∧l₂ ax-ri) ∙ (∧r (∧l₁ (embax {D = D1})) (∧l₂ (embax {D = D2})) ∙ (~ ax∧))
embax {D1 ∨ D2} = emb∨l (∨r₁-ri ax-ri) (∨r₂-ri ax-ri) ∙ (∨l (emb∨r₁ ax-ri) (emb∨r₂ ax-ri) ∙ (∨l (∨r₁ embax) (∨r₂ embax) ∙ (~ ax∨)))

embIl : {Γ : Cxt} {C : Fma}
  → (f : - ∣ Γ ⊢ri C)
  → emb-ri (Il-ri f) ≗ Il (emb-ri f)
embIl (∧r f g) = ∧r (embIl f) (embIl g) ∙ ∧rIl
embIl (li2ri f) = refl

-- embfocus, every derivation in SeqCalc is ≗-to the its normal form,
-- i.e. emb-ri (focus f) ≗ f
embfocus : {S : Stp} {Γ : Cxt} {C : Fma}
  → (f : S ∣ Γ ⊢ C)
  → emb-ri (focus f) ≗ f
embfocus ax = embax
embfocus (pass f) = embpass (focus f) ∙ pass (embfocus f)
embfocus Ir = refl
embfocus (Il f) = embIl (focus f) ∙ Il (embfocus f)
embfocus (⊗r f g) = emb⊗r (focus f) (focus g) ∙ ⊗r (embfocus f) (embfocus g)
embfocus (⊗l f) = emb⊗l (focus f) ∙ ⊗l (embfocus f)
embfocus (∧r f g) = ∧r (embfocus f) (embfocus g)
embfocus (∧l₁ f) = emb∧l₁ (focus f) ∙ ∧l₁ (embfocus f)
embfocus (∧l₂ f) = emb∧l₂ (focus f) ∙ ∧l₂ (embfocus f)
embfocus (∨r₁ f) = emb∨r₁ (focus f) ∙ ∨r₁ (embfocus f)
embfocus (∨r₂ f) = emb∨r₂ (focus f) ∙ ∨r₂ (embfocus f)
embfocus (∨l f g) = emb∨l (focus f) (focus g) ∙ ∨l (embfocus f) (embfocus g)        