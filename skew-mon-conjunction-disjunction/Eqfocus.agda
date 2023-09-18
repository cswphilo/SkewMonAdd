{-# OPTIONS --rewriting #-}

module Eqfocus where

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


f2li-fs-All++ : {Γ : Cxt} {S : Irr} {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢f_ S Γ) Φ)
  → (fs2 : All (_∣_⊢f_ S Γ) Ψ)
  → f2li-fs (All++ fs1 fs2) ≡ All++ (f2li-fs fs1) (f2li-fs fs2)
f2li-fs-All++ [] fs2 = refl
f2li-fs-All++ (f1 ∷ fs1) fs2 = cong (f2li f1 ∷_) (f2li-fs-All++ fs1 fs2)

pass-fs-All++ : {Γ : Cxt} {A : Fma} {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just A) Γ) Ψ)
  → pass-fs (All++ fs1 fs2) ≡ All++ (pass-fs fs1) (pass-fs fs2)
pass-fs-All++ [] fs2 = refl
pass-fs-All++ (f1 ∷ fs1) fs2 = cong (pass f1 ∷_) (pass-fs-All++ fs1 fs2)

pass-ri∧r* : {Γ : Cxt} {A A' : Fma}
  → {Φ : List Pos} 
  → (fs : All (_∣_⊢li_ (just A') Γ) Φ)
  → (SF : SubFmas Φ A)
  → pass-ri (∧r* fs SF) ≡ ∧r* (f2li-fs (pass-fs fs)) SF
pass-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite pass-fs-All++ fs1 fs2 | 
          f2li-fs-All++ (pass-fs fs1) (pass-fs fs2) | 
          fsDist-white-refl (f2li-fs (pass-fs fs1)) (f2li-fs (pass-fs fs2)) = cong₂ ∧r (pass-ri∧r* fs1 SF1) (pass-ri∧r* fs2 SF2)
pass-ri∧r* (f ∷ []) stop = refl

check-focus-all-pass : {Γ : Cxt} {A' : Fma} {C : Pos} {Φ : List Pos}
  → (f : just A' ∣ Γ ⊢li C)
  → (fs : All (_∣_⊢li_ (just A') Γ) Φ)
  → check-focus (f2li (pass f)) (f2li-fs (pass-fs fs)) ≡ inj₁ (inj₂ (inj₂ (A' , Γ , (f ∷ fs) , refl , refl , refl))) 
check-focus-all-pass f [] = refl
check-focus-all-pass f (f' ∷ fs) rewrite check-focus-all-pass f' fs = refl

⊗rpass-ri : {Γ Δ : Cxt} {A' A B : Fma}
  → (f : just A' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (pass-ri f) g ≡ pass-ri (⊗r-ri f g)
⊗rpass-ri f g with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  pass-ri∧r* (f ∷ fs) SF |
           f2fs-refl (f2li (pass f) ∷ f2li-fs (pass-fs fs)) SF refl |
           check-focus-all-pass f fs = refl


∨r₁pass-ri : {Γ : Cxt} {A A' B : Fma}
  → (f : just A' ∣ Γ ⊢ri A)
  → ∨r₁-ri {B = B} (pass-ri f) ≡ pass-ri (∨r₁-ri f)
∨r₁pass-ri f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  pass-ri∧r* (f ∷ fs) SF |
           f2fs-refl (f2li (pass f) ∷ f2li-fs (pass-fs fs)) SF refl |
           check-focus-all-pass f fs = refl

∨r₂pass-ri : {Γ : Cxt} {A A' B : Fma}
  → (f : just A' ∣ Γ ⊢ri B)
  → ∨r₂-ri {A = A} (pass-ri f) ≡ pass-ri (∨r₂-ri f)
∨r₂pass-ri f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  pass-ri∧r* (f ∷ fs) SF |
           f2fs-refl (f2li (pass f) ∷ f2li-fs (pass-fs fs)) SF refl |
           check-focus-all-pass f fs = refl

Il-fs : {Γ : Cxt}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ - Γ) Φ)
  → All (_∣_⊢li_ (just I) Γ) Φ
Il-fs [] = []
Il-fs (f ∷ fs) = Il f ∷ Il-fs fs

Il-fs-All++ : {Γ : Cxt} {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ - Γ) Φ)
  → (fs2 : All (_∣_⊢li_ - Γ) Ψ)
  → Il-fs (All++ fs1 fs2) ≡ All++ (Il-fs fs1) (Il-fs fs2)
Il-fs-All++ [] fs2 = refl
Il-fs-All++ (f1 ∷ fs1) fs2 = cong (Il f1 ∷_) (Il-fs-All++ fs1 fs2)

Il-ri∧r* : {Γ : Cxt} {A : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ - Γ) Φ)
  → (SF : SubFmas Φ A)
  → Il-ri (∧r* fs SF) ≡ ∧r* (Il-fs fs) SF
Il-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl  
      rewrite Il-fs-All++ fs1 fs2 | 
      fsDist-white-refl (Il-fs fs1) (Il-fs fs2) = cong₂ ∧r (Il-ri∧r* fs1 SF1) (Il-ri∧r* fs2 SF2)
Il-ri∧r* (f ∷ []) stop = refl

Il-inv-fs-eq : {Γ : Cxt}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ - Γ) Φ)
  → Il-inv-fs (Il-fs fs) ≡ fs
Il-inv-fs-eq [] = refl
Il-inv-fs-eq (f1 ∷ fs) = cong (f1 ∷_) (Il-inv-fs-eq fs)


⊗rIl-ri : {Γ Δ : Cxt} {A B : Fma}
  → (f : - ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (Il-ri f) g ≡ Il-ri (⊗r-ri f g)
⊗rIl-ri f g with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  Il-ri∧r* (f ∷ fs) SF |
           f2fs-refl (Il f ∷ (Il-fs fs)) SF refl |
           Il-inv-fs-eq fs = refl

∨r₁Il-ri : {Γ : Cxt} {A B : Fma}
  → (f : - ∣ Γ ⊢ri A)
  → ∨r₁-ri {B = B} (Il-ri f) ≡ Il-ri (∨r₁-ri f)
∨r₁Il-ri f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  Il-ri∧r* (f ∷ fs) SF |
           f2fs-refl (Il f ∷ (Il-fs fs)) SF refl |
           Il-inv-fs-eq fs = refl

∨r₂Il-ri : {Γ : Cxt} {A B : Fma}
  → (f : - ∣ Γ ⊢ri B)
  → ∨r₂-ri {A = A} (Il-ri f) ≡ Il-ri (∨r₂-ri f)
∨r₂Il-ri f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  Il-ri∧r* (f ∷ fs) SF |
           f2fs-refl (Il f ∷ (Il-fs fs)) SF refl |
           Il-inv-fs-eq fs = refl

⊗l-fs : {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just A) (B ∷ Γ)) Φ)
  → All (_∣_⊢li_ (just (A ⊗ B)) Γ) Φ
⊗l-fs [] = []
⊗l-fs (f ∷ fs) = ⊗l f ∷ ⊗l-fs fs

⊗l-fs-All++ : {Γ : Cxt} {Φ Ψ : List Pos} {A B : Fma}
  → (fs1 : All (_∣_⊢li_ (just A) (B ∷ Γ)) Φ)
  → (fs2 : All (_∣_⊢li_ (just A) (B ∷ Γ)) Ψ)
  → ⊗l-fs (All++ fs1 fs2) ≡ All++ (⊗l-fs fs1) (⊗l-fs fs2)
⊗l-fs-All++ [] fs2 = refl
⊗l-fs-All++ (f1 ∷ fs1) fs2 = cong (⊗l f1 ∷_) (⊗l-fs-All++ fs1 fs2)

⊗l-ri∧r* : {Γ : Cxt} {A A' B' : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just A') (B' ∷ Γ)) Φ)
  → (SF : SubFmas Φ A)
  → ⊗l-ri (∧r* fs SF) ≡ ∧r* (⊗l-fs fs) SF
⊗l-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl  
      rewrite ⊗l-fs-All++ fs1 fs2 | 
      fsDist-white-refl (⊗l-fs fs1) (⊗l-fs fs2) = cong₂ ∧r (⊗l-ri∧r* fs1 SF1) (⊗l-ri∧r* fs2 SF2)
⊗l-ri∧r* (f ∷ []) stop = refl

⊗l-inv-fs-eq : {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just A) (B ∷ Γ)) Φ)
  → ⊗l-inv-fs (⊗l-fs fs) ≡ fs
⊗l-inv-fs-eq [] = refl
⊗l-inv-fs-eq (f1 ∷ fs) = cong (f1 ∷_) (⊗l-inv-fs-eq fs)


⊗r⊗l-ri : {Γ Δ : Cxt} {A A' B B' : Fma}
  → (f : just A' ∣ B' ∷ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (⊗l-ri f) g ≡ ⊗l-ri (⊗r-ri f g)
⊗r⊗l-ri f g with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ⊗l-ri∧r* (f ∷ fs) SF |
           f2fs-refl (⊗l f ∷ (⊗l-fs fs)) SF refl |
           ⊗l-inv-fs-eq fs = refl

∨r₁⊗l-ri : {Γ : Cxt} {A A' B B' : Fma}
  → (f : just A' ∣ B' ∷ Γ ⊢ri A)
  → ∨r₁-ri {B = B} (⊗l-ri f) ≡ ⊗l-ri (∨r₁-ri f)
∨r₁⊗l-ri f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ⊗l-ri∧r* (f ∷ fs) SF |
           f2fs-refl (⊗l f ∷ (⊗l-fs fs)) SF refl |
           ⊗l-inv-fs-eq fs = refl

∨r₂⊗l-ri : {Γ : Cxt} {A A' B B' : Fma}
  → (f : just A' ∣ B' ∷ Γ ⊢ri B)
  → ∨r₂-ri {A = A} (⊗l-ri f) ≡ ⊗l-ri (∨r₂-ri f)
∨r₂⊗l-ri f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ⊗l-ri∧r* (f ∷ fs) SF |
           f2fs-refl (⊗l f ∷ (⊗l-fs fs)) SF refl |
           ⊗l-inv-fs-eq fs = refl

∧l₁-fs-All++ : {Γ : Cxt} {A B : Fma} {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just A) Γ) Ψ)
  → ∧l₁-fs {B = B} (All++ fs1 fs2) ≡ All++ (∧l₁-fs fs1) (∧l₁-fs fs2)
∧l₁-fs-All++ [] fs2 = refl
∧l₁-fs-All++ (f1 ∷ fs1) fs2 = cong (∧l₁ f1 ∷_) (∧l₁-fs-All++ fs1 fs2)

∧l₁-ri∧r* : {Γ : Cxt} {A B D : Fma}
  → {Φ : List Pos} 
  → (fs : All (_∣_⊢li_ (just A) Γ) Φ)
  → (SF : SubFmas Φ D)
  → ∧l₁-ri {B = B} (∧r* fs SF) ≡ ∧r* (f2li-fs (∧l₁-fs fs)) SF
∧l₁-ri∧r* {B = B} fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite ∧l₁-fs-All++ {B = B} fs1 fs2 | 
          f2li-fs-All++ (∧l₁-fs {B = B} fs1) (∧l₁-fs fs2) | 
          fsDist-white-refl (f2li-fs (∧l₁-fs {B = B} fs1)) (f2li-fs (∧l₁-fs fs2)) = cong₂ ∧r (∧l₁-ri∧r* {B = B} fs1 SF1) (∧l₁-ri∧r* {B = B} fs2 SF2)
∧l₁-ri∧r* (f ∷ []) stop = refl

check-focus-all-∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos} {Φ : List Pos}
  → (f : just A ∣ Γ ⊢li C)
  → (fs : All (_∣_⊢li_ (just A) Γ) Φ)
  → check-focus (f2li (∧l₁ {B = B} f)) (f2li-fs (∧l₁-fs fs)) ≡ inj₁ (inj₁ (A , B , f ∷ fs , refl , refl))
check-focus-all-∧l₁ f [] = refl
check-focus-all-∧l₁ {B = B} f (f' ∷ fs) rewrite check-focus-all-∧l₁ {B = B} f' fs = refl

⊗r∧l₁-ri : {Γ Δ : Cxt} {A B D E : Fma}
  → (f : just A ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (∧l₁-ri {B = B} f) g ≡ ∧l₁-ri (⊗r-ri f g)
⊗r∧l₁-ri {B = B} f g with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ∧l₁-ri∧r* {B = B} (f ∷ fs) SF  |
           f2fs-refl (f2li (∧l₁ {B = B} f) ∷ f2li-fs (∧l₁-fs fs)) SF refl |
           check-focus-all-∧l₁ {B = B} f fs = refl

∨r₁∧l₁-ri : {Γ : Cxt} {A B D E : Fma}
  → (f : just A ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₁-ri f)
∨r₁∧l₁-ri {B = B} f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ∧l₁-ri∧r* {B = B} (f ∷ fs) SF  |
           f2fs-refl (f2li (∧l₁ {B = B} f) ∷ f2li-fs (∧l₁-fs fs)) SF refl |
           check-focus-all-∧l₁ {B = B} f fs = refl

∨r₂∧l₁-ri : {Γ : Cxt} {A B D E : Fma}
  → (f : just A ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₁-ri {B = B} f) ≡ ∧l₁-ri (∨r₂-ri f)
∨r₂∧l₁-ri {B = B} f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ∧l₁-ri∧r* {B = B} (f ∷ fs) SF  |
           f2fs-refl (f2li (∧l₁ {B = B} f) ∷ f2li-fs (∧l₁-fs fs)) SF refl |
           check-focus-all-∧l₁ {B = B} f fs = refl 


∧l₂-fs-All++ : {Γ : Cxt} {A B : Fma} {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just B) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just B) Γ) Ψ)
  → ∧l₂-fs {A = A} (All++ fs1 fs2) ≡ All++ (∧l₂-fs fs1) (∧l₂-fs fs2)
∧l₂-fs-All++ [] fs2 = refl
∧l₂-fs-All++ (f1 ∷ fs1) fs2 = cong (∧l₂ f1 ∷_) (∧l₂-fs-All++ fs1 fs2)

∧l₂-ri∧r* : {Γ : Cxt} {A B D : Fma}
  → {Φ : List Pos} 
  → (fs : All (_∣_⊢li_ (just B) Γ) Φ)
  → (SF : SubFmas Φ D)
  → ∧l₂-ri {A = A} (∧r* fs SF) ≡ ∧r* (f2li-fs (∧l₂-fs fs)) SF
∧l₂-ri∧r* {A = A} fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl 
  rewrite ∧l₂-fs-All++ {A = A} fs1 fs2 | 
          f2li-fs-All++ (∧l₂-fs {A = A} fs1) (∧l₂-fs fs2) | 
          fsDist-white-refl (f2li-fs (∧l₂-fs {A = A} fs1)) (f2li-fs (∧l₂-fs fs2)) = cong₂ ∧r (∧l₂-ri∧r* {A = A} fs1 SF1) (∧l₂-ri∧r* {A = A} fs2 SF2)
∧l₂-ri∧r* (f ∷ []) stop = refl

check-focus-all-∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos} {Φ : List Pos}
  → (f : just B ∣ Γ ⊢li C)
  → (fs : All (_∣_⊢li_ (just B) Γ) Φ)
  → check-focus (f2li (∧l₂ {A = A} f)) (f2li-fs (∧l₂-fs fs)) ≡ inj₁ (inj₂ (inj₁ (A , B , f ∷ fs , refl , refl)))
check-focus-all-∧l₂ f [] = refl
check-focus-all-∧l₂ {A = A} f (f' ∷ fs) rewrite check-focus-all-∧l₂ {A = A} f' fs = refl

⊗r∧l₂-ri : {Γ Δ : Cxt} {A B D E : Fma}
  → (f : just B ∣ Γ ⊢ri D) (g : - ∣ Δ ⊢ri E)
  → ⊗r-ri (∧l₂-ri {A = A} f) g ≡ ∧l₂-ri (⊗r-ri f g)
⊗r∧l₂-ri {A = A} f g with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ∧l₂-ri∧r* {A = A} (f ∷ fs) SF  |
           f2fs-refl (f2li (∧l₂ {A = A} f) ∷ f2li-fs (∧l₂-fs fs)) SF refl |
           check-focus-all-∧l₂ {A = A} f fs = refl

∨r₁∧l₂-ri : {Γ : Cxt} {A B D E : Fma}
  → (f : just B ∣ Γ ⊢ri D)
  → ∨r₁-ri {B = E} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₁-ri f)
∨r₁∧l₂-ri {A = A} f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ∧l₂-ri∧r* {A = A} (f ∷ fs) SF  |
           f2fs-refl (f2li (∧l₂ {A = A} f) ∷ f2li-fs (∧l₂-fs fs)) SF refl |
           check-focus-all-∧l₂ {A = A} f fs = refl

∨r₂∧l₂-ri : {Γ : Cxt} {A B D E : Fma}
  → (f : just B ∣ Γ ⊢ri E)
  → ∨r₂-ri {A = D} (∧l₂-ri {A = A} f) ≡ ∧l₂-ri (∨r₂-ri f)
∨r₂∧l₂-ri {A = A} f with f2fs f
... | .[] , [] , SF , eq = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl 
  rewrite  ∧l₂-ri∧r* {A = A} (f ∷ fs) SF  |
           f2fs-refl (f2li (∧l₂ {A = A} f) ∷ f2li-fs (∧l₂-fs fs)) SF refl |
           check-focus-all-∧l₂ {A = A} f fs = refl

fs-succ-eq : {Γ : Cxt} {A A' B' : Fma}
  → {Φ1 Φ2 : List Pos}
  → {f1 : just A' ∣ Γ ⊢ri A} {f2 : just B' ∣ Γ ⊢ri A}
  → (fs1 : All (_∣_⊢li_ (just A') Γ) Φ1)
  → (fs2 : All (_∣_⊢li_ (just B') Γ) Φ2)
  → (SF1 : SubFmas Φ1 A)
  → (SF2 : SubFmas Φ2 A)
  → (eq3 : f1 ≡ ∧r* fs1 SF1) (eq4 : f2 ≡ ∧r* fs2 SF2)
  → Φ1 ≡ Φ2
fs-succ-eq fs1 fs2 (conj {Φ1} {Ψ1} SF1 SF1') (conj {Φ2} {Ψ2} SF2 SF2') refl refl with fsDist-white Φ1 Ψ1 fs1 refl | fsDist-white Φ2 Ψ2 fs2 refl
... | fs1' , fs1'' , refl | fs2' , fs2'' , refl = 
  cong₂ _++_ (fs-succ-eq fs1' fs2' SF1 SF2 refl refl) (fs-succ-eq fs1'' fs2'' SF1' SF2' refl refl)
--   rewrite fs-succ-eq fs1' fs2' SF1 SF2 refl refl | fs-succ-eq fs1'' fs2'' SF1' SF2' refl refl = {! refl  !}
fs-succ-eq fs1 fs2 (stop {A , q}) (stop {.(pos (A , q)) , p}) refl refl
  rewrite pos-eq A p | isPos-unique A p q = refl

SF-eq : {Γ : Cxt} {A A' B' : Fma}
  → {Φ1 Φ2 : List Pos}
  → {f1 : just A' ∣ Γ ⊢ri A} {f2 : just B' ∣ Γ ⊢ri A}
  → (fs1 : All (_∣_⊢li_ (just A') Γ) Φ1)
  → (fs2 : All (_∣_⊢li_ (just B') Γ) Φ2)
  → (SF1 : SubFmas Φ1 A)
  → (SF2 : SubFmas Φ2 A)
  → (eq3 : f1 ≡ ∧r* fs1 SF1) (eq4 : f2 ≡ ∧r* fs2 SF2)
  → (eq : Φ1 ≡ Φ2)
  → SF2 ≡ subst (λ x → SubFmas x A) eq SF1
SF-eq fs1 fs2 (conj {Φ1} {Ψ1} SF1 SF1') (conj {Φ2} {Ψ2} SF2 SF2') eq1 eq2 eq3 with fsDist-white Φ1 Ψ1 fs1 refl | fsDist-white Φ2 Ψ2 fs2 refl
SF-eq .(All++ fs1' fs1'') .(All++ fs2' fs2'') (conj {Φ1} {Ψ1} SF1 SF1') (conj {Φ2} {Ψ2} SF2 SF2') refl refl eq3 | fs1' , fs1'' , refl | fs2' , fs2'' , refl with fs-succ-eq fs1' fs2' SF1 SF2 refl refl | fs-succ-eq fs1'' fs2'' SF1' SF2' refl refl
SF-eq .(All++ fs1' fs1'') .(All++ fs2' fs2'') (conj {Φ1} {Ψ1} SF1 SF1') (conj {.Φ1} {.Ψ1} SF2 SF2') refl refl refl | fs1' , fs1'' , refl | fs2' , fs2'' , refl | refl | refl 
  rewrite SF-eq fs1' fs2' SF1 SF2 refl refl refl | SF-eq fs1'' fs2'' SF1' SF2' refl refl refl = refl
SF-eq fs1 fs2 stop stop refl refl refl = refl

∨l-fs : {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just B) Γ) Φ)
  → All (_∣_⊢li_ (just (A ∨ B)) Γ) Φ
∨l-fs [] [] = []
∨l-fs (f1 ∷ fs1) (f2 ∷ fs2) = ∨l f1 f2 ∷ ∨l-fs fs1 fs2

∨l-fs-inv-eq₁ : {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just B) Γ) Φ)
  → ∨l-inv-fs₁ (∨l-fs fs1 fs2) ≡ fs1
∨l-fs-inv-eq₁ [] [] = refl
∨l-fs-inv-eq₁ (f1 ∷ fs1) (f2 ∷ fs2) = cong (f1 ∷_) (∨l-fs-inv-eq₁ fs1 fs2)

∨l-fs-inv-eq₂ : {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just B) Γ) Φ)
  → ∨l-inv-fs₂ (∨l-fs fs1 fs2) ≡ fs2
∨l-fs-inv-eq₂ [] [] = refl
∨l-fs-inv-eq₂ (f1 ∷ fs1) (f2 ∷ fs2) = cong (f2 ∷_) (∨l-fs-inv-eq₂ fs1 fs2)

∨l-fs-All++ : {Γ : Cxt} {A B  : Fma}
  → {Φ Ψ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A) Γ) Φ)
  → (fs1' : All (_∣_⊢li_ (just A) Γ) Ψ)
  → (fs2 : All (_∣_⊢li_ (just B) Γ) Φ)
  → (fs2' : All (_∣_⊢li_ (just B) Γ) Ψ)
  → ∨l-fs (All++ fs1 fs1') (All++ fs2 fs2') ≡ All++ (∨l-fs fs1 fs2) (∨l-fs fs1' fs2')
∨l-fs-All++ [] fs1' [] fs2' = refl
∨l-fs-All++ (f1 ∷ fs1) fs1' (f2 ∷ fs2) fs2' = cong (∨l f1 f2 ∷_) (∨l-fs-All++ fs1 fs1' fs2 fs2')

∨l-ri-∧r* : {Γ : Cxt} {A' B' A : Fma}
  → {Φ : List Pos}
  → (fs1 : All (_∣_⊢li_ (just A') Γ) Φ)
  → (fs2 : All (_∣_⊢li_ (just B') Γ) Φ)
  → (SF : SubFmas Φ A)
  → ∨l-ri (∧r* fs1 SF) (∧r* fs2 SF) ≡ ∧r* (∨l-fs fs1 fs2) SF
∨l-ri-∧r* fs1 fs2 (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs1 refl | fsDist-white Φ Ψ fs2 refl
... | fs1' , fs1'' , refl | fs2' , fs2'' , refl 
  rewrite ∨l-fs-All++ fs1' fs1'' fs2' fs2'' | 
          fsDist-white-refl (∨l-fs fs1' fs2') (∨l-fs fs1'' fs2'') |
          ∨l-ri-∧r* fs1' fs2' SF1 | ∨l-ri-∧r* fs1'' fs2'' SF2 = refl
∨l-ri-∧r* (_∷_ {` x , _} f1 []) (f2 ∷ []) stop = refl
∨l-ri-∧r* (_∷_ {I , _} f1 []) (f2 ∷ []) stop = refl
∨l-ri-∧r* (_∷_ {A ⊗ A₁ , _} f1 []) (f2 ∷ []) stop = refl
∨l-ri-∧r* (_∷_ {A ∨ A₁ , _} f1 []) (f2 ∷ []) stop = refl

⊗r∨l-ri : {Γ Δ : Cxt} {A A' B B' : Fma}
  → (f : just A' ∣ Γ ⊢ri A) (f' : just B' ∣ Γ ⊢ri A)
  → (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (∨l-ri f f') g ≡ ∨l-ri (⊗r-ri f g) (⊗r-ri f' g)
⊗r∨l-ri f f' g with f2fs f | f2fs f' 
... | Φ1 , [] , SF1 , refl | Φ2 , [] , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF1 refl)
... | Φ1 , [] , SF1 , refl | Φ2 , f2 ∷ fs2 , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF1 refl)
... | Φ1 , f1 ∷ fs1 , SF1 , refl | Φ2 , [] , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF2 refl)
... | Φ1 , f1 ∷ fs1 , SF1 , refl | Φ2 , f2 ∷ fs2 , SF2 , refl with fs-succ-eq (f1 ∷ fs1) (f2 ∷ fs2) SF1 SF2 refl refl
... | refl with SF-eq (f1 ∷ fs1) (f2 ∷ fs2) SF1 SF2 refl refl refl
... | refl 
  rewrite ∨l-ri-∧r* (f1 ∷ fs1) (f2 ∷ fs2) SF1 |
          f2fs-refl (∨l f1 f2 ∷ ∨l-fs fs1 fs2) SF1 refl |
          ∨l-fs-inv-eq₁ fs1 fs2 | ∨l-fs-inv-eq₂ fs1 fs2 = refl

∨r₁∨l-ri : {Γ : Cxt} {A B C D : Fma}
  → (f : just C ∣ Γ ⊢ri A) (f' : just D ∣ Γ ⊢ri A)
  → ∨r₁-ri {B = B} (∨l-ri f f') ≡ ∨l-ri (∨r₁-ri f) (∨r₁-ri f')
∨r₁∨l-ri f f' with f2fs f | f2fs f' 
... | Φ1 , [] , SF1 , refl | Φ2 , [] , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF1 refl)
... | Φ1 , [] , SF1 , refl | Φ2 , f2 ∷ fs2 , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF1 refl)
... | Φ1 , f1 ∷ fs1 , SF1 , refl | Φ2 , [] , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF2 refl)
... | Φ1 , f1 ∷ fs1 , SF1 , refl | Φ2 , f2 ∷ fs2 , SF2 , refl with fs-succ-eq (f1 ∷ fs1) (f2 ∷ fs2) SF1 SF2 refl refl
... | refl with SF-eq (f1 ∷ fs1) (f2 ∷ fs2) SF1 SF2 refl refl refl
... | refl 
  rewrite ∨l-ri-∧r* (f1 ∷ fs1) (f2 ∷ fs2) SF1 |
          f2fs-refl (∨l f1 f2 ∷ ∨l-fs fs1 fs2) SF1 refl |
          ∨l-fs-inv-eq₁ fs1 fs2 | ∨l-fs-inv-eq₂ fs1 fs2 = refl

∨r₂∨l-ri : {Γ : Cxt} {A B C D : Fma}
  → (f : just C ∣ Γ ⊢ri B) (f' : just D ∣ Γ ⊢ri B)
  → ∨r₂-ri {A = A} (∨l-ri f f') ≡ ∨l-ri (∨r₂-ri f) (∨r₂-ri f')
∨r₂∨l-ri f f' with f2fs f | f2fs f' 
... | Φ1 , [] , SF1 , refl | Φ2 , [] , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF1 refl)
... | Φ1 , [] , SF1 , refl | Φ2 , f2 ∷ fs2 , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF1 refl)
... | Φ1 , f1 ∷ fs1 , SF1 , refl | Φ2 , [] , SF2 , refl = ⊥-elim (SubFmas[]-⊥ SF2 refl)
... | Φ1 , f1 ∷ fs1 , SF1 , refl | Φ2 , f2 ∷ fs2 , SF2 , refl with fs-succ-eq (f1 ∷ fs1) (f2 ∷ fs2) SF1 SF2 refl refl
... | refl with SF-eq (f1 ∷ fs1) (f2 ∷ fs2) SF1 SF2 refl refl refl
... | refl 
  rewrite ∨l-ri-∧r* (f1 ∷ fs1) (f2 ∷ fs2) SF1 |
          f2fs-refl (∨l f1 f2 ∷ ∨l-fs fs1 fs2) SF1 refl |
          ∨l-fs-inv-eq₁ fs1 fs2 | ∨l-fs-inv-eq₂ fs1 fs2 = refl

-- equivalent derivations in SeqCalc are identical in focused calculus
eqfocus :{S : Stp} {Γ : Cxt} {C : Fma}
  → {f f' : S ∣ Γ ⊢ C}
  → f ≗ f'
  → focus f ≡ focus f'
eqfocus refl = refl
eqfocus (~ eq) = sym (eqfocus eq)
eqfocus (eq ∙ eq₁) = trans (eqfocus eq) (eqfocus eq₁)
eqfocus (pass eq) = cong pass-ri (eqfocus eq)
eqfocus (Il eq) = cong Il-ri (eqfocus eq)
eqfocus (⊗l eq) = cong ⊗l-ri (eqfocus eq)
eqfocus (⊗r eq eq₁) = cong₂ (λ x y → ⊗r-ri x y) (eqfocus eq) (eqfocus eq₁)
eqfocus (∧r eq eq₁) = cong₂ (λ x y → ∧r x y) (eqfocus eq) (eqfocus eq₁)
eqfocus (∧l₁ eq) = cong ∧l₁-ri (eqfocus eq)
eqfocus (∧l₂ eq) = cong ∧l₂-ri (eqfocus eq)
eqfocus axI = refl
eqfocus ax⊗ = refl
eqfocus ax∧ = refl
eqfocus ax∨ = refl
eqfocus (⊗rpass {f = f} {g}) = ⊗rpass-ri (focus f) (focus g)
eqfocus (⊗rIl {f = f} {g}) = ⊗rIl-ri (focus f) (focus g)
eqfocus (⊗r⊗l {f = f} {g}) = ⊗r⊗l-ri (focus f) (focus g)
eqfocus (⊗r∧l₁ {f = f} {g}) = ⊗r∧l₁-ri (focus f) (focus g)
eqfocus (⊗r∧l₂ {f = f} {g}) = ⊗r∧l₂-ri (focus f) (focus g)
eqfocus (⊗r∨l {f = f} {f'} {g}) = ⊗r∨l-ri (focus f) (focus f') (focus g)
eqfocus ∧rpass = refl
eqfocus ∧rIl = refl
eqfocus ∧r⊗l = refl
eqfocus ∧r∧l₁ = refl
eqfocus ∧r∧l₂ = refl
eqfocus ∧r∨l = refl
eqfocus (∨r₁ eq) = cong ∨r₁-ri (eqfocus eq)
eqfocus (∨r₂ eq) = cong ∨r₂-ri (eqfocus eq)
eqfocus (∨l eq1 eq2) = cong₂ (λ x y → ∨l-ri x y) (eqfocus eq1) (eqfocus eq2)
eqfocus (∨r₁pass {f = f}) = ∨r₁pass-ri (focus f)
eqfocus (∨r₁Il {f = f}) = ∨r₁Il-ri (focus f)
eqfocus (∨r₁⊗l {f = f}) = ∨r₁⊗l-ri (focus f)
eqfocus (∨r₁∧l₁ {f = f}) = ∨r₁∧l₁-ri (focus f)
eqfocus (∨r₁∧l₂ {f = f}) = ∨r₁∧l₂-ri (focus f)
eqfocus (∨r₁∨l {f = f} {g}) = ∨r₁∨l-ri (focus f) (focus g)
eqfocus (∨r₂pass {f = f}) = ∨r₂pass-ri (focus f)
eqfocus (∨r₂Il {f = f}) = ∨r₂Il-ri (focus f)
eqfocus (∨r₂⊗l {f = f}) = ∨r₂⊗l-ri (focus f)
eqfocus (∨r₂∧l₁ {f = f}) = ∨r₂∧l₁-ri (focus f)
eqfocus (∨r₂∧l₂ {f = f}) = ∨r₂∧l₂-ri (focus f)
eqfocus (∨r₂∨l {f = f} {g}) = ∨r₂∨l-ri (focus f) (focus g)                 