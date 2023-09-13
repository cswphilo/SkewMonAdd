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

-- pass'-li : {Γ : Cxt} {A : Fma}
--  → Σ Pos (λ C → just A ∣ Γ ⊢li C) 
--  → Σ Pos (λ C → - ∣ A ∷ Γ ⊢li C)
-- pass'-li (C , f) = C , f2li (pass f)

-- pass'-li-fs-eq : {Γ : Cxt} {A : Fma}
--   → (fs : List (Σ Pos (λ C → just A ∣ Γ ⊢li C)))
--   → mapList (λ x → pos (proj₁ x)) (mapList pass'-li fs) ≡ mapList (λ x → pos (proj₁ x)) fs
-- pass'-li-fs-eq [] = refl
-- pass'-li-fs-eq ((C , f) ∷ fs) = cong₂ _∷_ refl (pass'-li-fs-eq fs)

-- pass-ri∧r* : {Γ : Cxt} {A A' : Fma}
--   → {Φ : List Fma}
--   → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A') Γ)))
--   → (SF : SubFmas Φ A)
--   → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
--   → pass-ri (∧r* fs SF eq) ≡ ∧r* (mapList pass'-li fs) SF eq
-- pass-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
-- pass-ri∧r* {Γ} {A' = A'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
--   rewrite fsDist-white-refl - (A' ∷ Γ) {C} {C'} {f2li (pass f)} {f2li (pass f')} (mapList (λ z → proj₁ z , f2li (pass (proj₂ z))) fs') (mapList (λ z → proj₁ z , f2li (pass (proj₂ z))) fs'') = 
--     cong₂ ∧r (pass-ri∧r* ((C , f) ∷ fs') SF1 refl) (pass-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
-- pass-ri∧r* ((C , f) ∷ []) stop refl = refl

-- check-focus-all-pass : {Γ : Cxt} {A' : Fma} {C : Pos}
--   → (f : just A' ∣ Γ ⊢li C)
--   → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
--   → check-focus (C , f2li (pass f)) (mapList pass'-li fs) ≡ inj₁ (inj₂ (inj₂ (A' , Γ , ((C , f) ∷ fs) , refl , refl , refl))) 
-- check-focus-all-pass f [] = refl
-- check-focus-all-pass f ((C' , f') ∷ fs) rewrite check-focus-all-pass f' fs = refl

-- ⊗rpass-ri : {Γ Δ : Cxt} {A' A B : Fma}
--   → (f : just A' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
--   → ⊗r-ri (pass-ri f) g ≡ pass-ri (⊗r-ri f g)
-- ⊗rpass-ri f g with f2fs f
-- ... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl
--   rewrite pass-ri∧r* ((C , f') ∷ fs) SF refl |
--           f2fs-refl ((C , f2li (pass f')) ∷ mapList pass'-li fs) SF refl |
--           check-focus-all-pass f' fs |
--           f2li-pass-fs-eq fs = refl

-- Il' : {Γ : Cxt}
--   → Σ Pos (λ C → - ∣ Γ ⊢li C)
--   → Σ Pos (λ C → just I ∣ Γ ⊢li C)
-- Il' (C , f) = C , Il f

-- Il-fs-eq : {Γ : Cxt}
--   → (fs : List (Σ Pos (λ C → - ∣ Γ ⊢li C)))
--   → mapList (λ x → pos (proj₁ x)) (mapList Il' fs) ≡ mapList (λ x → pos (proj₁ x)) fs
-- Il-fs-eq [] = refl
-- Il-fs-eq ((C , f) ∷ fs) = cong₂ _∷_ refl (Il-fs-eq fs)
-- {-# REWRITE Il-fs-eq #-}

-- Il-ri∧r* : {Γ : Cxt} {A : Fma}
--   → {Φ : List Fma}
--   → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ - Γ)))
--   → (SF : SubFmas Φ A)
--   → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
--   → Il-ri (∧r* fs SF eq) ≡ ∧r* (mapList Il' fs) SF eq
-- Il-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
-- Il-ri∧r* {Γ} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
--   rewrite fsDist-white-refl (just I) Γ {C} {C'} {Il f} {Il f'} (mapList (λ z → proj₁ z , Il (proj₂ z)) fs') (mapList (λ z → proj₁ z , Il (proj₂ z)) fs'') = cong₂ ∧r (Il-ri∧r* ((C , f) ∷ fs') SF1 refl) (Il-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
-- Il-ri∧r* ((C , f) ∷ []) stop refl = refl

-- IlIl-inv-eq-fs : {Γ : Cxt}
--   → (fs : List (Σ Pos (_∣_⊢li_ - Γ)))
--   → Il-inv-fs (mapList Il' fs) ≡ fs
-- IlIl-inv-eq-fs [] = refl
-- IlIl-inv-eq-fs ((C , f) ∷ fs) = cong₂ _∷_ refl (IlIl-inv-eq-fs fs)
-- {-# REWRITE IlIl-inv-eq-fs #-}

-- ⊗rIl-ri : {Γ Δ : Cxt} {A B : Fma}
--   → (f : - ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
--   → ⊗r-ri (Il-ri f) g ≡ Il-ri (⊗r-ri f g)
-- ⊗rIl-ri f g with f2fs f
-- ... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
--   rewrite Il-ri∧r* ((C , f') ∷ fs) SF refl | 
--           f2fs-refl ((C , Il f') ∷ mapList Il' fs) SF refl | 
--           Il-inv-fs-eq (mapList Il' fs) = refl

-- ⊗l' : {A B : Fma} {Γ : Cxt}
--   → Σ Pos (λ C → just A ∣ B ∷ Γ ⊢li C)
--   → Σ Pos (λ C → just (A ⊗ B) ∣ Γ ⊢li C)
-- ⊗l' (C , f) = C , ⊗l f

-- ⊗l-fs-eq : {A' B' : Fma} {Γ : Cxt}
--   → (fs : List (Σ Pos (λ C → just A' ∣ B' ∷ Γ ⊢li C)))
--   → mapList (λ x → pos (proj₁ x)) (mapList ⊗l' fs) ≡ mapList (λ x → pos (proj₁ x)) fs
-- ⊗l-fs-eq [] = refl
-- ⊗l-fs-eq ((C , f) ∷ fs) = cong₂ _∷_ refl (⊗l-fs-eq fs)
-- {-# REWRITE ⊗l-fs-eq #-}
-- -- we use global rewriting here to avoid convoluted definition and proof of ⊗l-ri∧r*
-- -- without global rewrting the last line of def ⊗l-ri∧r* would be 
-- -- ⊗l-ri (∧r* SF fs eq) ≡ ∧r* SF (mapList ⊗l' fs) (trans eq (sym (⊗l-fs-eq fs)))

-- ⊗l-ri∧r* : {Γ : Cxt} {A A' B' : Fma}
--   → {Φ : List Fma}
--   → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A') (B' ∷ Γ))))
--   → (SF : SubFmas Φ A)
--   → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
--   → ⊗l-ri (∧r* fs SF eq) ≡ ∧r* (mapList ⊗l' fs) SF eq
-- ⊗l-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
-- ⊗l-ri∧r* {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
--   rewrite fsDist-white-refl (just (A' ⊗ B')) Γ {C} {C'} {⊗l f} {⊗l f'} (mapList (λ z → proj₁ z , ⊗l (proj₂ z)) fs') (mapList (λ z → proj₁ z , ⊗l (proj₂ z)) fs'') = cong₂ ∧r (⊗l-ri∧r* ((C , f) ∷ fs') SF1 refl) (⊗l-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
-- ⊗l-ri∧r* ((C , f) ∷ []) stop refl = refl

-- ⊗l⊗l-inv-eq-fs : {Γ : Cxt} {A B : Fma}
--   → (fs : List (Σ Pos (_∣_⊢li_ (just A) (B ∷ Γ))))
--   → ⊗l-inv-fs (mapList ⊗l' fs) ≡ fs
-- ⊗l⊗l-inv-eq-fs [] = refl
-- ⊗l⊗l-inv-eq-fs ((C , f) ∷ fs) = cong₂ _∷_ refl (⊗l⊗l-inv-eq-fs fs)
-- {-# REWRITE ⊗l⊗l-inv-eq-fs #-}

-- ⊗r⊗l-ri : {Γ Δ : Cxt} {A' B' A B : Fma}
--   → (f : just A' ∣ B' ∷ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
--   → ⊗r-ri (⊗l-ri f) g ≡ ⊗l-ri (⊗r-ri f g)
-- ⊗r⊗l-ri f g with f2fs f
-- ... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
--   rewrite ⊗l-ri∧r* ((C , f') ∷ fs) SF refl | 
--           f2fs-refl ((C , ⊗l f') ∷ mapList ⊗l' fs) SF refl = refl
--           -- ⊗l-inv-fs-eq (mapList ⊗l' fs) = refl

-- ∧l₁'-li : {A B : Fma} {Γ : Cxt}
--   → Σ Pos (λ C → just A ∣ Γ ⊢li C)
--   → Σ Pos (λ C → just (A ∧ B) ∣ Γ ⊢li C)
-- ∧l₁'-li (C , f) = C , f2li (∧l₁ f)

-- ∧l₁-ri∧r* : {Γ : Cxt} {A A' B' : Fma}
--   → {Φ : List Fma}
--   → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A') Γ)))
--   → (SF : SubFmas Φ A)
--   → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
--   → ∧l₁-ri {B = B'} (∧r* fs SF eq) ≡ ∧r* (mapList ∧l₁'-li fs) SF eq
-- ∧l₁-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
-- ∧l₁-ri∧r* {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
--   rewrite fsDist-white-refl (just (A' ∧ B')) Γ {C} {C'} {f2li (∧l₁ f)} {f2li (∧l₁ f')} (mapList (λ z → proj₁ z , f2li (∧l₁ (proj₂ z))) fs') (mapList (λ z → proj₁ z , f2li (∧l₁ (proj₂ z))) fs'') = cong₂ ∧r (∧l₁-ri∧r* ((C , f) ∷ fs') SF1 refl) (∧l₁-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
-- ∧l₁-ri∧r* ((C , f) ∷ []) stop refl = refl

-- check-focus-all-∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
--   → (f : just A ∣ Γ ⊢li C)
--   → (fs : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
--   → check-focus (C , f2li (∧l₁ {B = B} f)) (mapList ∧l₁'-li fs) ≡ inj₁ (inj₁ (A , B , (C , f) ∷ fs , refl , refl))
-- check-focus-all-∧l₁ f [] = refl
-- check-focus-all-∧l₁ {B = B} f ((C , f') ∷ fs) rewrite check-focus-all-∧l₁ {B = B} f' fs = refl

-- ⊗r∧l₁-ri : {Γ Δ : Cxt} {A' B' A B : Fma}
--   → (f : just A' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
--   → ⊗r-ri (∧l₁-ri {B = B'} f) g ≡ ∧l₁-ri (⊗r-ri f g)
-- ⊗r∧l₁-ri {B' = B'} f g with f2fs f
-- ... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
--   rewrite ∧l₁-ri∧r* {B' = B'} ((C , f') ∷ fs) SF refl |
--           f2fs-refl ((C , f2li (∧l₁ {B = B'} f')) ∷ mapList ∧l₁'-li fs) SF refl |
--           check-focus-all-∧l₁ {B = B'} f' fs = refl
--           -- f2li∧l₁-fs-eq {B = B'} fs = refl
  
-- ∧l₂'-li : {A B : Fma} {Γ : Cxt}
--   → Σ Pos (λ C → just B ∣ Γ ⊢li C)
--   → Σ Pos (λ C → just (A ∧ B) ∣ Γ ⊢li C)
-- ∧l₂'-li (C , f) = C , f2li (∧l₂ f)

-- ∧l₂-ri∧r* : {Γ : Cxt} {A A' B' : Fma}
--   → {Φ : List Fma}
--   → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B') Γ)))
--   → (SF : SubFmas Φ A)
--   → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
--   → ∧l₂-ri {A = A'} (∧r* fs SF eq) ≡ ∧r* (mapList ∧l₂'-li fs) SF eq
-- ∧l₂-ri∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
-- ∧l₂-ri∧r* {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
--   rewrite fsDist-white-refl (just (A' ∧ B')) Γ {C} {C'} {f2li (∧l₂ f)} {f2li (∧l₂ f')} (mapList (λ z → proj₁ z , f2li (∧l₂ (proj₂ z))) fs') (mapList (λ z → proj₁ z , f2li (∧l₂ (proj₂ z))) fs'') = cong₂ ∧r (∧l₂-ri∧r* ((C , f) ∷ fs') SF1 refl) (∧l₂-ri∧r* ((C' , f') ∷ fs'') SF2 refl)
-- ∧l₂-ri∧r* ((C , f) ∷ []) stop refl = refl

-- check-focus-all-∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
--   → (f : just B ∣ Γ ⊢li C)
--   → (fs : List (Σ Pos (_∣_⊢li_ (just B) Γ)))
--   → check-focus (C , f2li (∧l₂ {A = A} f)) (mapList ∧l₂'-li fs) ≡ inj₁ (inj₂ (inj₁ (A , B , (C , f) ∷ fs , refl , refl)))
-- check-focus-all-∧l₂ f [] = refl
-- check-focus-all-∧l₂ {A = A} f ((C , f') ∷ fs) rewrite check-focus-all-∧l₂ {A = A} f' fs = refl

-- ⊗r∧l₂-ri : {Γ Δ : Cxt} {A' B' A B : Fma}
--   → (f : just B' ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
--   → ⊗r-ri (∧l₂-ri {A = A'} f) g ≡ ∧l₂-ri (⊗r-ri f g)
-- ⊗r∧l₂-ri {A' = A'} f g with f2fs f
-- ... | (C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f') ∷ fs)) , refl , SF , refl 
--   rewrite ∧l₂-ri∧r* {A' = A'} ((C , f') ∷ fs) SF refl |
--           f2fs-refl ((C , f2li (∧l₂ {A = A'} f')) ∷ mapList ∧l₂'-li fs) SF refl |
--           check-focus-all-∧l₂ {A = A'} f' fs = refl
--           -- f2li∧l₂-fs-eq {A = A'} fs = refl

-- ∨l' : {Γ : Cxt} {A B : Fma}
--   → (fs1 : Σ Pos (_∣_⊢li_ (just A) Γ))
--   → (fs2 : Σ Pos (_∣_⊢li_ (just B) Γ))
--   → (eq : proj₁ fs1 ≡ proj₁ fs2)
--   → Σ Pos (_∣_⊢li_ (just (A ∨ B)) Γ)
-- ∨l' (C , f) (.C , g) refl = C , ∨l f g

isPosProp : (A : Fma)
  → (p q : isPos A)
  → p ≡ q
isPosProp A p q = {!   !}
lem2 : {A B : Fma}
  → (p : isPos A) (q : isPos B)
  → A ≡ B
  → (A , p) ≡ (B , q)
lem2 p q refl = {!   !}

∨l-fs : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
  → (gs : List (Σ Pos (_∣_⊢li_ (just B) Γ)))
  → (eq : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) gs)
  → List (Σ Pos (_∣_⊢li_ (just (A ∨ B)) Γ))
∨l-fs [] [] refl = []
∨l-fs (((C , snd) , f) ∷ fs) (((C' , snd₁) , g) ∷ gs) eq = 
  ((C , snd) , (∨l f (subst (λ y → just _ ∣ _ ⊢li y) (lem2 _ _ (sym (proj₁ (inj∷ eq)))) g))) ∷ ∨l-fs fs gs (proj₂ (inj∷ eq))
-- ∨l-fs (((` x , snd) , f) ∷ fs) (((C' , snd₁) , g) ∷ gs) eq = ((` x , _) , (∨l f (subst (λ y → just _ ∣ _ ⊢li (y , _)) (sym (proj₁ (inj∷ eq))) g))) ∷ ∨l-fs fs gs (proj₂ (inj∷ eq))
-- ∨l-fs (((I , snd) , f) ∷ fs) (((C' , snd₁) , g) ∷ gs) eq = ((I , _) , (∨l f (subst (λ y → just _ ∣ _ ⊢li (y , _)) (sym (proj₁ (inj∷ eq))) g))) ∷ ∨l-fs fs gs (proj₂ (inj∷ eq))
-- ∨l-fs (((C ⊗ C₃ , snd) , f) ∷ fs) (((C' , snd₁) , g) ∷ gs) eq = ((C ⊗ C₃ , _) , (∨l f (subst (λ y → just _ ∣ _ ⊢li (y , _)) (sym (proj₁ (inj∷ eq))) g))) ∷ ∨l-fs fs gs (proj₂ (inj∷ eq))
-- ∨l-fs (((C ∨ C₃ , snd) , f) ∷ fs) (((C' , snd₁) , g) ∷ gs) eq = ((C ∨ C₃ , _) , (∨l f (subst (λ y → just _ ∣ _ ⊢li (y , _)) (sym (proj₁ (inj∷ eq))) g))) ∷ ∨l-fs fs gs (proj₂ (inj∷ eq))
-- with inj∷ eq
-- ∨l-fs (((` x , snd) , f) ∷ fs) (((.(` x) , snd₁) , g) ∷ gs) eq | refl , eq1 = ((` x , _) , (∨l f g)) ∷ ∨l-fs fs gs eq1
-- ∨l-fs (((I , snd) , f) ∷ fs) (((.I , snd₁) , g) ∷ gs) eq | refl , eq1 = ((I , _) , (∨l f g)) ∷ ∨l-fs fs gs eq1
-- ∨l-fs (((C ⊗ C' , snd) , f) ∷ fs) (((.(C ⊗ C') , snd₁) , g) ∷ gs) eq | refl , eq1 = ((C ⊗ C' , _) , (∨l f g)) ∷ ∨l-fs fs gs eq1
-- ∨l-fs (((C ∨ C' , snd) , f) ∷ fs) (((.(C ∨ C') , snd₁) , g) ∷ gs) eq | refl , eq1 = ((C ∨ C' , _) , (∨l f g)) ∷ ∨l-fs fs gs eq1

fs-succ-eq : {S S' : Stp} {Γ : Cxt} {A : Fma}
  → {Φ Ψ : List Fma}
  → {f : S ∣ Γ ⊢ri A} {f' : S' ∣ Γ ⊢ri A}
  → (fs : List (Σ Pos (_∣_⊢li_ S Γ)))
  → (fs' : List (Σ Pos (_∣_⊢li_ S' Γ)))
  → (eq1 : Φ ≡ mapList (λ x → proj₁ (proj₁ x)) fs) (eq2 : Ψ ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → (SF1 : SubFmas Φ A)
  → (SF2 : SubFmas Ψ A)
  → (eq3 : f ≡ ∧r* fs SF1 eq1) (eq4 : f' ≡ ∧r* fs' SF2 eq2)
  → Φ ≡ Ψ
-- fs-succ-eq fs fs' eq1 eq2 (conj {Φ} {Ψ} SF1 SF2) (conj {Φ'} {Ψ'} SF3 SF4) eq3 eq4 with fsDist-white Φ Ψ fs eq1 | fsDist-white Φ' Ψ' fs' eq2
-- fs-succ-eq .((((A , snd) , snd₁) ∷ fs₁) ++ f₁ ∷ fs₂)` .((((A' , snd₂) , snd₃) ∷ fs'₁) ++ f'₁ ∷ fs'₂) refl refl (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs₁)} {.(mapList (λ x → proj₁ (proj₁ x)) fs₂)} SF1 SF2) (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs'₁)} {.(mapList (λ x → proj₁ (proj₁ x)) fs'₂)} SF3 SF4) eq3 eq4 | ((A , snd) , snd₁) ∷ fs₁ , f₁ ∷ fs₂ , refl , refl , refl | ((A' , snd₂) , snd₃) ∷ fs'₁ , f'₁ ∷ fs'₂ , refl , refl , refl = 
--   cong₂ _++_ (fs-succ-eq (((A , snd) , snd₁) ∷ fs₁) (((A' , snd₂) , snd₃) ∷ fs'₁) refl refl SF1 SF3 refl refl) (fs-succ-eq (f₁ ∷ fs₂) (f'₁ ∷ fs'₂) refl refl SF2 SF4 refl refl) 
-- fs-succ-eq fs (((.(_ ∧ _) , snd) , snd₁) ∷ []) eq1 refl (conj SF1 SF2) stop eq3 eq4 = ⊥-elim snd
-- fs-succ-eq (((.(_ ∧ _) , snd) , snd₁) ∷ []) fs' refl eq2 stop (conj SF2 SF3) eq3 eq4 = ⊥-elim snd
-- fs-succ-eq (f ∷ []) (f' ∷ []) refl refl stop stop eq3 eq4 = refl


∨l-fs-eq : {Γ : Cxt} {A' B' : Fma}
  -- → {Φ Ψ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (fs' : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
  → (eq : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → pos (proj₁ x)) (∨l-fs fs fs' eq)
∨l-fs-eq [] [] refl = refl
∨l-fs-eq (((C , snd) , f) ∷ fs) (((C' , snd₁) , g) ∷ fs') eq with inj∷ eq
∨l-fs-eq (((` x , snd) , f) ∷ fs) (((.(` x) , snd₁) , g) ∷ fs') eq | refl , eq1 = cong ((` x) ∷_) (∨l-fs-eq fs fs' eq1)
∨l-fs-eq (((I , snd) , f) ∷ fs) (((.I , snd₁) , g) ∷ fs') eq | refl , eq1 = cong (I ∷_) (∨l-fs-eq fs fs' eq1)
∨l-fs-eq (((C ⊗ C' , snd) , f) ∷ fs) (((.(C ⊗ C') , snd₁) , g) ∷ fs') eq | refl , eq1 = cong ((C ⊗ C') ∷_) (∨l-fs-eq fs fs' eq1)
∨l-fs-eq (((C ∨ C' , snd) , f) ∷ fs) (((.(C ∨ C') , snd₁) , g) ∷ fs') eq | refl , eq1 = cong ((C ∨ C') ∷_) (∨l-fs-eq fs fs' eq1)

∨l-fs-eq₂ : {Γ : Cxt} {A' B' : Fma}
  -- → {Φ Ψ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (fs' : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
  → (eq : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → mapList (λ x → proj₁ (proj₁ x)) fs' ≡ mapList (λ x → pos (proj₁ x)) (∨l-fs fs fs' eq)

-- fs-fs'-rewrite : {Γ : Cxt} {A' B' : Fma}
--   -- → {Φ Ψ : List Fma}
--   → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
--   → (fs' : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
--   → (eq : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
--   → Σ (List Fma) λ Φ → mapList (λ x → proj₁ (proj₁ x)) fs ≡ Φ
-- fs-fs'-rewrite [] [] refl = [] , refl
-- fs-fs'-rewrite (x ∷ fs) (x₁ ∷ fs') eq with inj∷ eq
-- ... | refl , eq1 with fs-fs'-rewrite fs fs' eq1
-- ... | Φ , eq2 = proj₁ (proj₁ x₁) ∷ Φ , cong (proj₁ (proj₁ x₁) ∷_) eq2

∨l++ : {Γ : Cxt} {A B : Fma}
  → (fs1 fs2 : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
  → (gs1 gs2 : List (Σ Pos (_∣_⊢li_ (just B) Γ)))
  → (eq : mapList (λ x → proj₁ (proj₁ x)) fs1 ≡ mapList (λ x → proj₁ (proj₁ x)) gs1)
  → (eq2 : mapList (λ x → proj₁ (proj₁ x)) fs2 ≡ mapList (λ x → proj₁ (proj₁ x)) gs2)
  → (eq3 : mapList (λ x → proj₁ (proj₁ x)) (fs1 ++ fs2) ≡ mapList (λ x → proj₁ (proj₁ x)) (gs1 ++ gs2))
  → ∨l-fs (fs1 ++ fs2) (gs1 ++ gs2) eq3 ≡ (∨l-fs fs1 gs1 eq) ++ (∨l-fs fs2 gs2 eq2)
-- {-# REWRITE ∨l++ #-}



SubFmas-∨l : {Γ : Cxt} {A' B' A : Fma}
  → {Φ Ψ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (fs' : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
  → (eq1 : Φ ≡ mapList (λ x → proj₁ (proj₁ x)) fs) (eq2 : Ψ ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → (eq3 : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → (SF1 : SubFmas Φ A) (SF2 : SubFmas Ψ A)
  → SubFmas (mapList (λ x → pos (proj₁ x)) (∨l-fs fs fs' eq3)) A
-- SubFmas-∨l fs fs' eq1 eq2 eq3 (conj {Φ = Φ} {Ψ} SF1 SF2) (conj {Φ = Φ'} {Ψ'} SF3 SF4) 
SubFmas-∨l fs fs' eq1 eq2 eq3 (conj {Φ = Φ} {Ψ} SF1 SF2) (conj {Φ = Φ'} {Ψ'} SF3 SF4) with fsDist-white Φ Ψ fs eq1 | fsDist-white Φ' Ψ' fs' eq2 
SubFmas-∨l .((f1 ∷ fs1) ++ f2 ∷ fs2) .((f1' ∷ fs1') ++ f2' ∷ fs2') refl refl eq3 (conj {Φ = .(mapList (λ x → proj₁ (proj₁ x)) fs1)} {.(mapList (λ x → proj₁ (proj₁ x)) fs2)} SF1 SF2) (conj {Φ = .(mapList (λ x → proj₁ (proj₁ x)) fs1')} {.(mapList (λ x → proj₁ (proj₁ x)) fs2')} SF3 SF4) | f1 ∷ fs1 , f2 ∷ fs2 , refl , refl , refl | f1' ∷ fs1' , f2' ∷ fs2' , refl , refl , refl = subst (λ y → SubFmas (_ ∷ mapList (λ x → proj₁ (proj₁ x)) y) (_ ∧ _)) (sym
 (proj₂
  (inj∷
   (∨l++ (f1 ∷ fs1) (f2 ∷ fs2) (f1' ∷ fs1') (f2' ∷ fs2')
    (fs-succ-eq (f1 ∷ fs1) (f1' ∷ fs1') refl refl SF1 SF3 refl refl)
    (fs-succ-eq (f2 ∷ fs2) (f2' ∷ fs2') refl refl SF2 SF4 refl refl)
    eq3))))
  (conj (SubFmas-∨l (f1 ∷ fs1) (f1' ∷ fs1') refl refl (fs-succ-eq (f1 ∷ fs1) (f1' ∷ fs1') refl refl SF1 SF3 refl refl) SF1 SF3) (SubFmas-∨l (f2 ∷ fs2) (f2' ∷ fs2') refl refl (fs-succ-eq _ _ refl refl SF2 SF4 refl refl) SF2 SF4))
  -- rewrite proj₂ (inj∷ (∨l++ (f1 ∷ fs1) (f2 ∷ fs2) (f1' ∷ fs1') (f2' ∷ fs2') (fs-succ-eq (f1 ∷ fs1) (f1' ∷ fs1') refl refl SF1 SF3 refl refl) (fs-succ-eq (f2 ∷ fs2) (f2' ∷ fs2') refl refl SF2 SF4 refl refl) eq3)) = conj (SubFmas-∨l (f1 ∷ fs1) (f1' ∷ fs1') refl refl (fs-succ-eq (f1 ∷ fs1) (f1' ∷ fs1') refl refl SF1 SF3 refl refl) SF1 SF3) (SubFmas-∨l (f2 ∷ fs2) (f2' ∷ fs2') refl refl (fs-succ-eq _ _ refl refl SF2 SF4 refl refl) SF2 SF4)
SubFmas-∨l fs fs' eq1 eq2 eq3 (conj SF1 SF2) stop = {!   !}
SubFmas-∨l fs fs' eq1 eq2 eq3 stop (conj SF2 SF3) = {!   !}
SubFmas-∨l (((` x , snd) , f) ∷ []) (((.(` x) , snd₂) , f') ∷ []) refl refl refl stop stop = stop
SubFmas-∨l (((I , snd) , f) ∷ []) (((.I , snd₂) , f') ∷ []) refl refl refl stop stop = stop
SubFmas-∨l (((A ⊗ A₁ , snd) , f) ∷ []) (((.(A ⊗ A₁) , snd₂) , f') ∷ []) refl refl refl stop stop = stop
SubFmas-∨l (((A ∨ A₁ , snd) , f) ∷ []) (((.(A ∨ A₁) , snd₂) , f') ∷ []) refl refl refl stop stop = stop
-- ∨l-fs (((A , _) , _) ∷ []) (((A , _) , _) ∷ []) refl , {!   !}

∨l-ri-∧r* : {Γ : Cxt} {A' B' A : Fma}
  -- → {Φ Ψ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (fs' : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
  → (SF1 : SubFmas (mapList (λ x → proj₁ (proj₁ x)) fs) A)
  → (SF2 : SubFmas (mapList (λ x → proj₁ (proj₁ x)) fs') A)
  → (eq : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → ∨l-ri (∧r* fs SF1 refl) (∧r* fs' SF2 refl) ≡ ∧r* (∨l-fs fs fs' eq) (SubFmas-∨l fs fs' refl refl eq SF1 SF2) refl
--   -- (SubFmas-∨l fs fs' refl refl eq SF1 SF2) refl
--   -- ∧r* (∨l-fs fs fs' eq) SF1 (∨l-fs-eq fs fs' eq)

-- lem : {Γ : Cxt} {A A' B' : Fma}
--   → (f' : just B' ∣ Γ ⊢ri A)
--   → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A') Γ))) 
--   -- → (Φ : List Fma)
--   -- → (eq : Φ ≡ mapList (λ x → proj₁ (proj₁ x)) fs)
--   → (SF : SubFmas (mapList (λ x → proj₁ (proj₁ x)) fs) A)
--   → Σ (List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B') Γ))) λ fs' → f2fs f' ≡ (fs' , mapList (λ x → proj₁ (proj₁ x)) fs , {!   !} , SF , {!   !})
-- lem fs Φ eq SF = ?


lem3 : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
  → (gs : List (Σ Pos (_∣_⊢li_ (just B) Γ)))
  → (eq : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) gs)
  → proj₁ (∨l-inv-fs (∨l-fs fs gs eq)) ≡ fs
lem3 [] [] refl = refl
lem3 (x ∷ fs) (x₁ ∷ gs) eq with inj∷ eq
... | refl , eq1 = cong (x ∷_) (lem3 fs gs eq1)

lem4 : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
  → (gs : List (Σ Pos (_∣_⊢li_ (just B) Γ)))
  → (eq : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) gs)
  → proj₂ (∨l-inv-fs (∨l-fs fs gs eq)) ≡ gs
lem4 [] [] refl = refl
lem4 (x ∷ fs) (x₁ ∷ gs) eq with inj∷ eq
lem4 (((.(proj₁ (proj₁ x₁)) , snd) , snd₁) ∷ fs) (x₁ ∷ gs) eq | refl , eq1 
  rewrite isPosProp (proj₁ (proj₁ x₁)) snd (proj₂ (proj₁ x₁)) = cong (x₁ ∷_) (lem4 fs gs eq1) -- cong₂ _∷_ {! cong (λ y → y , (proj₂ x₁))  !} {!   !} -- cong₂ _∷_ {! lem2 _ _ refl!} (lem4 fs gs eq1) -- cong (x₁ ∷_) (lem4 fs gs eq1)

SubFmas-∨l-eq : {Γ : Cxt} {A' B' A : Fma}
  → {Φ Ψ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (fs' : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
  → (eq1 : Φ ≡ mapList (λ x → proj₁ (proj₁ x)) fs) (eq2 : Ψ ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → (eq3 : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → (eq4 : mapList (λ x → pos (proj₁ x)) (∨l-fs fs fs' eq3) ≡ Φ)
  → (SF1 : SubFmas Φ A) (SF2 : SubFmas Ψ A)
  → subst (λ y → SubFmas y A) eq4 (SubFmas-∨l fs fs' eq1 eq2 eq3 SF1 SF2) ≡ SF1
SubFmas-∨l-eq fs fs' eq1 eq2 eq3 eq4 (conj {Φ = Φ} {Ψ} SF1 SF2) (conj {Φ = Φ₁} {Ψ₁} SF3 SF4) with fsDist-white Φ Ψ fs eq1 | fsDist-white Φ₁ Ψ₁ fs' eq2 
SubFmas-∨l-eq .((((fst , snd) , snd₁) ∷ fs1) ++ f2 ∷ fs2) .((((fst₁ , snd₂) , snd₃) ∷ fs1') ++ f2' ∷ fs2') refl refl eq3 eq4 (conj {Φ = .(mapList (λ x → proj₁ (proj₁ x)) fs1)} {.(mapList (λ x → proj₁ (proj₁ x)) fs2)} SF1 SF2) (conj {Φ = .(mapList (λ x → proj₁ (proj₁ x)) fs1')} {.(mapList (λ x → proj₁ (proj₁ x)) fs2')} SF3 SF4) | ((fst , snd) , snd₁) ∷ fs1 , f2 ∷ fs2 , refl , refl , refl | ((fst₁ , snd₂) , snd₃) ∷ fs1' , f2' ∷ fs2' , refl , refl , refl = {!   !}
  -- rewrite proj₂ (inj∷ (∨l++ (((fst , snd) , snd₁) ∷ fs1) (f2 ∷ fs2) (((fst₁ , snd₂) , snd₃) ∷ fs1') (f2' ∷ fs2') (fs-succ-eq (_ ∷ fs1) (_ ∷ fs1') refl refl SF1 SF3 refl refl) (fs-succ-eq (f2 ∷ fs2) (f2' ∷ fs2') refl refl SF2 SF4 refl refl) eq3)) = ?
SubFmas-∨l-eq fs fs' eq1 eq2 eq3 eq4 (conj SF1 SF2) stop = {!   !}
SubFmas-∨l-eq fs fs' eq1 eq2 eq3 eq4 stop (conj SF2 SF3) = {!   !}
SubFmas-∨l-eq fs fs' eq1 eq2 eq3 eq4 stop stop = {!   !}

SubFmas-∨l-eq₁ : {Γ : Cxt} {A' B' A : Fma}
  → {Φ Ψ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (fs' : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
  → (eq1 : Φ ≡ mapList (λ x → proj₁ (proj₁ x)) fs) (eq2 : Ψ ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → (eq3 : mapList (λ x → proj₁ (proj₁ x)) fs ≡ mapList (λ x → proj₁ (proj₁ x)) fs')
  → (eq4 : mapList (λ x → pos (proj₁ x)) (∨l-fs fs fs' eq3) ≡ Ψ)
  → (SF1 : SubFmas Φ A) (SF2 : SubFmas Ψ A)
  → subst (λ y → SubFmas y A) eq4 (SubFmas-∨l fs fs' eq1 eq2 eq3 SF1 SF2) ≡ SF2

gen⊗r-eq : {S : Stp} {Γ Δ : Cxt} {A B : Fma} {C C' : Pos}
  → {Φ Ψ : List Fma}
  → (f : S ∣ Γ ⊢li C)
  → (f' : S ∣ Γ ⊢li C')
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → (gs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → (SF1 : SubFmas Φ A)
  → (SF2 : SubFmas Ψ A)
  → (g : - ∣ Δ ⊢ri B)
  → (eq : Φ ≡ ((proj₁ C) ∷ mapList (λ x₂ → proj₁ (proj₁ x₂)) fs))
  → (eq' : Ψ ≡ ((proj₁ C') ∷ mapList (λ x₂ → proj₁ (proj₁ x₂)) gs))
  → (eq'' : Φ ≡ Ψ) (eq''' : C ≡ C')
  → (eq0 : subst (λ y → S ∣ Γ ⊢li y) eq''' f ≡ f')
  → (eq1 : fs ≡ gs)
  → (eq2 : subst (λ y → SubFmas y A) eq'' SF1 ≡ SF2)
  → gen⊗r-li f fs eq SF1 g ≡ gen⊗r-li f' gs eq' SF2 g
gen⊗r-eq f f' fs gs SF1 SF2 g refl refl refl refl refl refl refl = refl 

⊗r∨l-ri : {Γ Δ : Cxt} {A A' B B' : Fma}
  → (f : just A' ∣ Γ ⊢ri A) (f' : just B' ∣ Γ ⊢ri A)
  → (g : - ∣ Δ ⊢ri B)
  → ⊗r-ri (∨l-ri f f') g ≡ ∨l-ri (⊗r-ri f g) (⊗r-ri f' g)
⊗r∨l-ri f f' g with f2fs f | f2fs f'  
... | x ∷ fs , .(mapList (λ x₂ → proj₁ (proj₁ x₂)) (x ∷ fs)) , refl , SF1 , refl | x₁ ∷ fs' , .(mapList (λ x₂ → proj₁ (proj₁ x₂)) (x₁ ∷ fs')) , refl , SF2 , refl 
  rewrite ∨l-ri-∧r* (x ∷ fs) (x₁ ∷ fs') SF1 SF2 (fs-succ-eq (x ∷ fs) (x₁ ∷ fs') refl refl SF1 SF2 refl refl) | f2fs-refl (∨l-fs (x ∷ fs) (x₁ ∷ fs') (fs-succ-eq (x ∷ fs) (x₁ ∷ fs') refl refl SF1 SF2 refl refl)) (SubFmas-∨l (x ∷ fs) (x₁ ∷ fs') refl refl
           (fs-succ-eq (x ∷ fs) (x₁ ∷ fs') refl refl SF1 SF2 refl refl) SF1
           SF2) refl  = cong li2ri (cong₂ ∨l {!   !} {!   !})
--           cong li2ri (cong₂ ∨l (gen⊗r-eq (proj₂ x) _ _ fs _ _ _ _ _ (cong (pos (proj₁ x) ∷_) (sym (∨l-fs-eq fs fs' _))) refl refl ((lem3 fs fs' (proj₂
--           (inj∷
--            (fs-succ-eq (x ∷ fs) (x₁ ∷ fs') refl refl SF1 SF2 refl refl))))) (SubFmas-∨l-eq (x ∷ fs) (x₁ ∷ fs') refl refl _ _ SF1 SF2)) (gen⊗r-eq
--  (subst (_∣_⊢li_ (just _) _)
--   (lem2 (proj₂ (proj₁ x₁)) (proj₂ (proj₁ x))
--    (sym
--     (proj₁
--      (inj∷
--       (fs-succ-eq (x ∷ fs) (x₁ ∷ fs') refl refl SF1 SF2 refl refl)))))
--   (proj₂ x₁))
--  (proj₂ x₁) _ fs' _ SF2 g _ _ ((cong₂ (_∷_) ((proj₁
--      (inj∷
--       (fs-succ-eq (x ∷ fs) (x₁ ∷ fs') refl refl SF1 SF2 refl refl)))) (sym (∨l-fs-eq₂ fs fs' _)))) (sym (lem2 (proj₂ (proj₁ x₁)) (proj₂ (proj₁ x))
--    (sym
--     (proj₁
--      (inj∷
--       (fs-succ-eq (x ∷ fs) (x₁ ∷ fs') refl refl SF1 SF2 refl refl)))))) {!  !} (lem4 fs fs' _) ((SubFmas-∨l-eq₁ (x ∷ fs) (x₁ ∷ fs') refl refl _ _ SF1 SF2))))


-- ⊗r∨l-ri f f' g with f2fs f | f2fs f' 
-- ... | fs , Φ , eq1 , SF1 , eq2 | fs' , Ψ , eq3 , SF2 , eq4 with fs-succ-eq fs fs' eq1 eq3 SF1 SF2 eq2 eq4
-- ⊗r∨l-ri .(∧r* (f ∷ fs) SF1 refl) .(∧r* (f' ∷ fs') SF2 refl) g | f ∷ fs , .(mapList (λ x₂ → proj₁ (proj₁ x₂)) (f ∷ fs)) , refl , SF1 , refl | f' ∷ fs' , .(mapList (λ x₂ → proj₁ (proj₁ x₂)) (f' ∷ fs')) , refl , SF2 , refl | eq5 with inj∷ eq5
-- ⊗r∨l-ri .(∧r* (((` x , snd) , f) ∷ fs) SF1 refl) .(∧r* (((` x , snd₃) , f') ∷ fs') SF2 refl) g | ((` x , snd) , f) ∷ fs , .(mapList _ (((` x , snd) , f) ∷ fs)) , refl , SF1 , refl | ((.(` x) , snd₃) , f') ∷ fs' , .(mapList _ (((` x , snd₃) , f') ∷ fs')) , refl , SF2 , refl | eq5 | refl , eq6 = {! z  !}
-- ⊗r∨l-ri .(∧r* (((I , snd) , f) ∷ fs) SF1 refl) .(∧r* (((I , snd₃) , snd₂) ∷ fs') SF2 refl) g | ((I , snd) , f) ∷ fs , .(mapList _ (((I , snd) , f) ∷ fs)) , refl , SF1 , refl | ((.I , snd₃) , snd₂) ∷ fs' , .(mapList _ (((I , snd₃) , snd₂) ∷ fs')) , refl , SF2 , refl | eq5 | refl , eq6 = {!   !}
-- ⊗r∨l-ri .(∧r* (((A ⊗ A₁ , snd) , f) ∷ fs) SF1 refl) .(∧r* (((A ⊗ A₁ , snd₃) , snd₂) ∷ fs') SF2 refl) g | ((A ⊗ A₁ , snd) , f) ∷ fs , .(mapList _ (((A ⊗ A₁ , snd) , f) ∷ fs)) , refl , SF1 , refl | ((.(A ⊗ A₁) , snd₃) , snd₂) ∷ fs' , .(mapList _ (((A ⊗ A₁ , snd₃) , snd₂) ∷ fs')) , refl , SF2 , refl | eq5 | refl , eq6 = {!   !}
-- ⊗r∨l-ri .(∧r* (((A ∨ A₁ , snd) , f) ∷ fs) SF1 refl) .(∧r* (((A ∨ A₁ , snd₃) , snd₂) ∷ fs') SF2 refl) g | ((A ∨ A₁ , snd) , f) ∷ fs , .(mapList _ (((A ∨ A₁ , snd) , f) ∷ fs)) , refl , SF1 , refl | ((.(A ∨ A₁) , snd₃) , snd₂) ∷ fs' , .(mapList _ (((A ∨ A₁ , snd₃) , snd₂) ∷ fs')) , refl , SF2 , refl | eq5 | refl , eq6 = {!   !}

-- equivalent derivations in SeqCalc are identical in Focused
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
eqfocus (⊗rpass {f = f} {g}) = {!   !} -- ⊗rpass-ri (focus f) (focus g)
eqfocus (⊗rIl {f = f} {g}) = {!   !} -- ⊗rIl-ri (focus f) (focus g)
eqfocus (⊗r⊗l {f = f} {g}) = {!   !} -- ⊗r⊗l-ri (focus f) (focus g)
eqfocus (⊗r∧l₁ {f = f} {g}) = {!   !} -- ⊗r∧l₁-ri (focus f) (focus g)
eqfocus (⊗r∧l₂ {f = f} {g}) = {!   !} -- ⊗r∧l₂-ri (focus f) (focus g)
eqfocus (⊗r∨l {f = f} {f'} {g}) = {!   !} -- ⊗r∨l-ri (focus f) (focus f') (focus g)
eqfocus ∧rpass = refl
eqfocus ∧rIl = refl
eqfocus ∧r⊗l = refl
eqfocus ∧r∧l₁ = refl
eqfocus ∧r∧l₂ = refl
eqfocus ∧r∨l = refl
eqfocus (∨r₁ eq) = {!   !} -- cong ∨r₁-ri (eqfocus eq)
eqfocus (∨r₂ eq) = {!   !} -- cong ∨r₂-ri (eqfocus eq)
eqfocus (∨l eq1 eq2) = cong₂ (λ x y → ∨l-ri x y) (eqfocus eq1) (eqfocus eq2)
eqfocus ∨r₁pass = {!   !}
eqfocus ∨r₁Il = {!   !}
eqfocus ∨r₁⊗l = {!   !}
eqfocus ∨r₁∧l₁ = {!   !}
eqfocus ∨r₁∧l₂ = {!   !}
eqfocus ∨r₁∨l = {!   !}
eqfocus ∨r₂pass = {!   !}
eqfocus ∨r₂Il = {!   !}
eqfocus ∨r₂⊗l = {!   !}
eqfocus ∨r₂∧l₁ = {!   !}
eqfocus ∨r₂∧l₂ = {!   !}
eqfocus ∨r₂∨l = {!   !}                