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

pass'-li : {Γ : Cxt} {A : Fma}
 → Σ Pos (λ C → just A ∣ Γ ⊢li C) 
 → Σ Pos (λ C → - ∣ A ∷ Γ ⊢li C)
pass'-li (C , f) = C , f2li (pass f)

pass'-li-fs-eq : {Γ : Cxt} {A : Fma}
  → (fs : List (Σ Pos (λ C → just A ∣ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) (mapList pass'-li fs) ≡ mapList (λ x → pos (proj₁ x)) fs
pass'-li-fs-eq [] = refl
pass'-li-fs-eq ((C , f) ∷ fs) = cong₂ _∷_ refl (pass'-li-fs-eq fs)

-- ∧r* commute with pass
pass-ri∧r* : {Γ : Cxt} {A A' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A') Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
  → pass-ri (∧r* fs SF eq) ≡ ∧r* (mapList pass'-li fs) SF eq
pass-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
pass-ri∧r* {Γ} {A' = A'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-white-refl - (A' ∷ Γ) {C} {C'} {f2li (pass f)} {f2li (pass f')} (mapList (λ z → proj₁ z , f2li (pass (proj₂ z))) fs') (mapList (λ z → proj₁ z , f2li (pass (proj₂ z))) fs'') = 
    cong₂ ∧r (pass-ri∧r* ((C , f) ∷ fs') SF1 refl) (pass-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
pass-ri∧r* ((C , f) ∷ []) stop refl = refl

check-focus-all-pass : {Γ : Cxt} {A' : Fma} {C : Pos}
  → (f : just A' ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → check-focus (C , f2li (pass f)) (mapList pass'-li fs) ≡ inj₁ (inj₂ (inj₂ (A' , Γ , ((C , f) ∷ fs) , refl , refl , refl))) 
check-focus-all-pass f [] = refl
check-focus-all-pass f ((C' , f') ∷ fs) rewrite check-focus-all-pass f' fs = refl

-- ⊗r commute with pass
⊗rpass-ri : {Γ Δ : Cxt} {A' A B : Fma}
  → (f : just A' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (pass-ri f) g ≡ pass-ri (⊗r-ri f g)
⊗rpass-ri f g with f2fs f
... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl
  rewrite pass-ri∧r* ((C , f') ∷ fs) SF refl |
          f2fs-refl ((C , f2li (pass f')) ∷ mapList pass'-li fs) SF refl |
          check-focus-all-pass f' fs |
          f2li-pass-fs-eq fs = refl

Il' : {Γ : Cxt}
  → Σ Pos (λ C → - ∣ Γ ⊢li C)
  → Σ Pos (λ C → just I ∣ Γ ⊢li C)
Il' (C , f) = C , Il f

Il-fs-eq : {Γ : Cxt}
  → (fs : List (Σ Pos (λ C → - ∣ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) (mapList Il' fs) ≡ mapList (λ x → pos (proj₁ x)) fs
Il-fs-eq [] = refl
Il-fs-eq ((C , f) ∷ fs) = cong₂ _∷_ refl (Il-fs-eq fs)
{-# REWRITE Il-fs-eq #-}

-- ∧r* commute with Il
Il-ri∧r* : {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ - Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
  → Il-ri (∧r* fs SF eq) ≡ ∧r* (mapList Il' fs) SF eq
Il-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
Il-ri∧r* {Γ} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-white-refl (just I) Γ {C} {C'} {Il f} {Il f'} (mapList (λ z → proj₁ z , Il (proj₂ z)) fs') (mapList (λ z → proj₁ z , Il (proj₂ z)) fs'') = cong₂ ∧r (Il-ri∧r* ((C , f) ∷ fs') SF1 refl) (Il-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
Il-ri∧r* ((C , f) ∷ []) stop refl = refl

-- Il and Il-inv are inverses of each other
IlIl-inv-eq-fs : {Γ : Cxt}
  → (fs : List (Σ Pos (_∣_⊢li_ - Γ)))
  → Il-inv-fs (mapList Il' fs) ≡ fs
IlIl-inv-eq-fs [] = refl
IlIl-inv-eq-fs ((C , f) ∷ fs) = cong₂ _∷_ refl (IlIl-inv-eq-fs fs)
{-# REWRITE IlIl-inv-eq-fs #-}

-- ⊗r commute with Il
⊗rIl-ri : {Γ Δ : Cxt} {A B : Fma}
  → (f : - ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (Il-ri f) g ≡ Il-ri (⊗r-ri f g)
⊗rIl-ri f g with f2fs f
... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
  rewrite Il-ri∧r* ((C , f') ∷ fs) SF refl | 
          f2fs-refl ((C , Il f') ∷ mapList Il' fs) SF refl | 
          Il-inv-fs-eq (mapList Il' fs) = refl

⊗l' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just A ∣ B ∷ Γ ⊢li C)
  → Σ Pos (λ C → just (A ⊗ B) ∣ Γ ⊢li C)
⊗l' (C , f) = C , ⊗l f

⊗l-fs-eq : {A' B' : Fma} {Γ : Cxt}
  → (fs : List (Σ Pos (λ C → just A' ∣ B' ∷ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) (mapList ⊗l' fs) ≡ mapList (λ x → pos (proj₁ x)) fs
⊗l-fs-eq [] = refl
⊗l-fs-eq ((C , f) ∷ fs) = cong₂ _∷_ refl (⊗l-fs-eq fs)
{-# REWRITE ⊗l-fs-eq #-}
-- we use global rewriting here to avoid convoluted definition and proof of ⊗l-ri∧r*
-- without global rewrting the last line of def ⊗l-ri∧r* would be 
-- ⊗l-ri (∧r* SF fs eq) ≡ ∧r* SF (mapList ⊗l' fs) (trans eq (sym (⊗l-fs-eq fs)))

-- ∧r* commute with ⊗l
⊗l-ri∧r* : {Γ : Cxt} {A A' B' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A') (B' ∷ Γ))))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
  → ⊗l-ri (∧r* fs SF eq) ≡ ∧r* (mapList ⊗l' fs) SF eq
⊗l-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
⊗l-ri∧r* {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-white-refl (just (A' ⊗ B')) Γ {C} {C'} {⊗l f} {⊗l f'} (mapList (λ z → proj₁ z , ⊗l (proj₂ z)) fs') (mapList (λ z → proj₁ z , ⊗l (proj₂ z)) fs'') = cong₂ ∧r (⊗l-ri∧r* ((C , f) ∷ fs') SF1 refl) (⊗l-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
⊗l-ri∧r* ((C , f) ∷ []) stop refl = refl

-- ⊗l and ⊗l-inv are inverses of each other
⊗l⊗l-inv-eq-fs : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A) (B ∷ Γ))))
  → ⊗l-inv-fs (mapList ⊗l' fs) ≡ fs
⊗l⊗l-inv-eq-fs [] = refl
⊗l⊗l-inv-eq-fs ((C , f) ∷ fs) = cong₂ _∷_ refl (⊗l⊗l-inv-eq-fs fs)
{-# REWRITE ⊗l⊗l-inv-eq-fs #-}

-- ⊗r commute with ⊗l
⊗r⊗l-ri : {Γ Δ : Cxt} {A' B' A B : Fma}
  → (f : just A' ∣ B' ∷ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (⊗l-ri f) g ≡ ⊗l-ri (⊗r-ri f g)
⊗r⊗l-ri f g with f2fs f
... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
  rewrite ⊗l-ri∧r* ((C , f') ∷ fs) SF refl | 
          f2fs-refl ((C , ⊗l f') ∷ mapList ⊗l' fs) SF refl | 
          ⊗l-inv-fs-eq (mapList ⊗l' fs) = refl

∧l₁'-li : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just A ∣ Γ ⊢li C)
  → Σ Pos (λ C → just (A ∧ B) ∣ Γ ⊢li C)
∧l₁'-li (C , f) = C , f2li (∧l₁ f)

-- ∧r* commute with ∧l₁
∧l₁-ri∧r* : {Γ : Cxt} {A A' B' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A') Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
  → ∧l₁-ri {B = B'} (∧r* fs SF eq) ≡ ∧r* (mapList ∧l₁'-li fs) SF eq
∧l₁-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
∧l₁-ri∧r* {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-white-refl (just (A' ∧ B')) Γ {C} {C'} {f2li (∧l₁ f)} {f2li (∧l₁ f')} (mapList (λ z → proj₁ z , f2li (∧l₁ (proj₂ z))) fs') (mapList (λ z → proj₁ z , f2li (∧l₁ (proj₂ z))) fs'') = cong₂ ∧r (∧l₁-ri∧r* ((C , f) ∷ fs') SF1 refl) (∧l₁-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
∧l₁-ri∧r* ((C , f) ∷ []) stop refl = refl

check-focus-all-∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
  → (f : just A ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
  → check-focus (C , f2li (∧l₁ {B = B} f)) (mapList ∧l₁'-li fs) ≡ inj₁ (inj₁ (A , B , (C , f) ∷ fs , refl , refl))
check-focus-all-∧l₁ f [] = refl
check-focus-all-∧l₁ {B = B} f ((C , f') ∷ fs) rewrite check-focus-all-∧l₁ {B = B} f' fs = refl

-- ⊗r commute with ∧l₁
⊗r∧l₁-ri : {Γ Δ : Cxt} {A' B' A B : Fma}
  → (f : just A' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (∧l₁-ri {B = B'} f) g ≡ ∧l₁-ri (⊗r-ri f g)
⊗r∧l₁-ri {B' = B'} f g with f2fs f
... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
  rewrite ∧l₁-ri∧r* {B' = B'} ((C , f') ∷ fs) SF refl |
          f2fs-refl ((C , f2li (∧l₁ {B = B'} f')) ∷ mapList ∧l₁'-li fs) SF refl |
          check-focus-all-∧l₁ {B = B'} f' fs |
          f2li-∧l₁-fs-eq {B = B'} fs = refl
  
∧l₂'-li : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just B ∣ Γ ⊢li C)
  → Σ Pos (λ C → just (A ∧ B) ∣ Γ ⊢li C)
∧l₂'-li (C , f) = C , f2li (∧l₂ f)

-- ∧r* commute with ∧l₂
∧l₂-ri∧r* : {Γ : Cxt} {A A' B' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B') Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
  → ∧l₂-ri {A = A'} (∧r* fs SF eq) ≡ ∧r* (mapList ∧l₂'-li fs) SF eq
∧l₂-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
∧l₂-ri∧r* {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-white-refl (just (A' ∧ B')) Γ {C} {C'} {f2li (∧l₂ f)} {f2li (∧l₂ f')} (mapList (λ z → proj₁ z , f2li (∧l₂ (proj₂ z))) fs') (mapList (λ z → proj₁ z , f2li (∧l₂ (proj₂ z))) fs'') = cong₂ ∧r (∧l₂-ri∧r* ((C , f) ∷ fs') SF1 refl) (∧l₂-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
∧l₂-ri∧r* ((C , f) ∷ []) stop refl = refl

check-focus-all-∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
  → (f : just B ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (_∣_⊢li_ (just B) Γ)))
  → check-focus (C , f2li  (∧l₂ {A = A} f)) (mapList ∧l₂'-li fs) ≡ inj₁ (inj₂ (inj₁ (A , B , (C , f) ∷ fs , refl , refl)))
check-focus-all-∧l₂ f [] = refl
check-focus-all-∧l₂ {A = A} f ((C , f') ∷ fs) rewrite check-focus-all-∧l₂ {A = A} f' fs = refl

-- ⊗r commute with ∧l₂
⊗r∧l₂-ri : {Γ Δ : Cxt} {A' B' A B : Fma}
  → (f : just B' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (∧l₂-ri {A = A'} f) g ≡ ∧l₂-ri (⊗r-ri f g)
⊗r∧l₂-ri {A' = A'} f g with f2fs f
... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
  rewrite ∧l₂-ri∧r* {A' = A'} ((C , f') ∷ fs) SF refl |
          f2fs-refl ((C , f2li (∧l₂ {A = A'} f')) ∷ mapList ∧l₂'-li fs) SF refl |
          check-focus-all-∧l₂ {A = A'} f' fs |
          f2li-∧l₂-fs-eq {A = A'} fs = refl

-- equivalent derivations in SeqCalc are identical in Focused calculus
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
eqfocus (⊗rpass {f = f} {g}) = ⊗rpass-ri (focus f) (focus g)
eqfocus (⊗rIl {f = f} {g}) = ⊗rIl-ri (focus f) (focus g)
eqfocus (⊗r⊗l {f = f} {g}) =  ⊗r⊗l-ri (focus f) (focus g)
eqfocus (⊗r∧l₁ {f = f} {g}) = ⊗r∧l₁-ri (focus f) (focus g)
eqfocus (⊗r∧l₂ {f = f} {g}) = ⊗r∧l₂-ri (focus f) (focus g)
eqfocus ∧rpass = refl
eqfocus ∧rIl = refl
eqfocus ∧r⊗l = refl
eqfocus ∧r∧l₁ = refl
eqfocus ∧r∧l₂ = refl             