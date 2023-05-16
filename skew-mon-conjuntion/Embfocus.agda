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
-- open import Eqfocus

fsDist-seq : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (Φ Ψ : List Fma) (fs : List (Σ Pos (λ C → S ∣ Γ ⊢ pos C))) (eq : A ∷ Φ ++ B ∷ Ψ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → Σ (List (Σ Pos (λ C → S ∣ Γ ⊢ pos C))) (λ fs' → Σ (List (Σ Pos (λ C → S ∣ Γ ⊢ pos C))) (λ fs'' 
    → fs ≡ fs' ++ fs'' × A ∷ Φ ≡ mapList (λ x → pos (proj₁ x)) fs' × B ∷ Ψ ≡ mapList (λ x → pos (proj₁ x)) fs''))
fsDist-seq [] [] (x ∷ x₁ ∷ []) refl = x ∷ [] , x₁ ∷ [] , refl , refl , refl
fsDist-seq [] (x₁ ∷ Ψ) (x ∷ fs) eq with fsDist-seq [] Ψ fs (proj₂ (inj∷ eq))
... | x₂ ∷ [] , x₃ ∷ fs'' , refl , refl , refl = x ∷ [] , x₂ ∷ x₃ ∷ fs'' , refl , cong (λ x → x ∷ []) (proj₁ (inj∷ eq)) , refl
fsDist-seq (x₁ ∷ Φ) Ψ (x ∷ fs) eq with fsDist-seq Φ Ψ fs (proj₂ (inj∷ eq))
... | x₂ ∷ fs' , x₃ ∷ fs'' , refl , refl , refl = x ∷ x₂ ∷ fs' , x₃ ∷ fs'' , refl , cong (λ x → x ∷ proj₁ (proj₁ x₂) ∷ mapList (λ x₄ → proj₁ (proj₁ x₄)) fs') (proj₁ (inj∷ eq)) , refl

fsDist-seq-refl : (S : Stp) (Γ : Cxt) {A B : Pos}
  → {f : S ∣ Γ ⊢ pos A} {g : S ∣ Γ ⊢ pos B}
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢ pos C)))
  → (gs : List (Σ Pos (λ C → S ∣ Γ ⊢ pos C)))
  → fsDist-seq ((mapList (λ z → proj₁ (proj₁ z)) fs)) ((mapList (λ z → proj₁ (proj₁ z)) gs)) ((A , f) ∷ fs ++ (B , g) ∷ gs) refl ≡ ((A , f) ∷ fs , (B , g) ∷ gs , refl , refl , refl)
fsDist-seq-refl S Γ [] [] = refl
fsDist-seq-refl S Γ {B = B} {g = g} [] ((C , h) ∷ gs) with fsDist-seq [] (mapList (λ z → proj₁ (proj₁ z)) gs) ((B , g) ∷ (C , h) ∷ gs) refl
... | .(B , g) ∷ [] , .(C , h) ∷ .gs , refl , refl , refl = refl
fsDist-seq-refl S Γ {A} {B} {f} {g} ((A' , f') ∷ fs) gs 
  rewrite fsDist-seq-refl S Γ {A'} {B} {f'} {g} fs gs = refl

fsDist-refl : {t t' : Tag} (S : Irr) (Γ : Cxt) {A B : Pos}
  → {f : t ∣ S ∣ Γ ⊢pT A} {g : t' ∣ S ∣ Γ ⊢pT B}
  → (fs : List (Σ Tag (λ t₁ → Σ Pos (_∣_∣_⊢pT_ t₁ S Γ))))
  → (gs : List (Σ Tag (λ t₁ → Σ Pos (_∣_∣_⊢pT_ t₁ S Γ))))
  → fsDist ((mapList (λ z → proj₁ (proj₁ (proj₂ z))) fs)) ((mapList (λ z → proj₁ (proj₁ (proj₂ z))) gs)) ((t , A , f) ∷ fs ++ (t' , B , g) ∷ gs) refl ≡ ((t , A , f) ∷ fs , (t' , B , g) ∷ gs , refl , refl , refl)
fsDist-refl S Γ [] [] = refl
fsDist-refl {t' = t'} S Γ {B = B} {g = g} [] ((t , C , h) ∷ gs) with fsDist [] (mapList (λ z → proj₁ (proj₁ (proj₂ z))) gs) ((t' , B , g) ∷ (t , C , h) ∷ gs) refl
... | .(t' , B , g) ∷ [] , .(t , C , h) ∷ .gs , refl , refl , refl = refl
fsDist-refl {t} S Γ {A} {B} {f} {g} ((t' , A' , f') ∷ fs) gs 
  rewrite fsDist-refl S Γ {A'} {B} {f'} {g} fs gs = refl

∧r*-seq : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢ pos C)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → S ∣ Γ ⊢ A
∧r*-seq fs (conj {Φ} {Ψ} {A' = A'} {B' = B'} SF SF₁) eq with fsDist-seq Φ Ψ fs eq 
... | x ∷ fs' , x₁ ∷ fs'' , refl , refl , refl = ∧r (∧r*-seq (x ∷ fs') SF refl) (∧r*-seq (x₁ ∷ fs'') SF₁ refl)
∧r*-seq ((C , f) ∷ []) stop refl = f

emb-li' : {S : Stp} {Γ : Cxt}
  → (f : Σ Pos (_∣_⊢li_ S Γ))
  → Σ Pos (λ C → S ∣ Γ ⊢ pos C)
emb-li' (C , f) = C , emb-li f

emb-li-fs-eq : {S : Stp} {Γ : Cxt}
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) (mapList emb-li' fs) ≡ mapList (λ x → pos (proj₁ x)) fs
emb-li-fs-eq [] = refl
emb-li-fs-eq (x ∷ fs) = cong₂ _∷_ refl (emb-li-fs-eq fs)
{-# REWRITE emb-li-fs-eq #-}

emb∧r* : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ S Γ))) 
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → proj₁ (proj₁ x)) fs)
  → emb-ri (∧r* fs SF eq) ≗ ∧r*-seq (mapList emb-li' fs) SF eq
emb∧r* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
emb∧r* {S} {Γ} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-seq-refl S Γ {C} {C'} {emb-li f} {emb-li f'} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs') (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs'') = 
    ∧r (emb∧r* ((C , f) ∷ fs') SF1 refl) (emb∧r* ((C' , f') ∷ fs'') SF2 refl)
emb∧r* ((C , f) ∷ []) stop refl = refl

emb-riT∧r* : {l : List Tag} {S : Irr} {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢pT_ t S Γ)))) 
  → (SF : SubFmas Φ A)
  → (eq1 : Φ ≡ mapList (λ x → proj₁ (proj₁ (proj₂ x))) fs)
  → (eq2 : l ≡ mapList proj₁ fs)
  → emb-riT (∧rT* fs SF eq1 eq2) ≗ ∧r*-seq (mapList emb-li' (mapList (λ x₁ → proj₁ (proj₂ x₁) , p2li (untagP (proj₂ (proj₂ x₁)))) fs)) SF eq1
emb-riT∧r* fs (conj {Φ} {Ψ} SF SF₁) eq1 refl with fsDist Φ Ψ fs eq1
emb-riT∧r* {S = S} {Γ} .(((t , C , f) ∷ fs') ++ (t' , C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ (proj₂ x))) fs')} {.(mapList (λ x → proj₁ (proj₁ (proj₂ x))) fs'')} SF1 SF2) refl refl | (t , C , f) ∷ fs' , (t' , C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-refl S Γ {C} {C'} {f} {f'} fs' fs'' |
          fsDist-seq-refl (irr S) Γ {C} {C'} {emb-li (p2li (untagP f))} {emb-li (p2li (untagP f'))} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (mapList (λ z → proj₁ (proj₂ z) , p2li (untagP (proj₂ (proj₂ z)))) fs')) (mapList (λ z → proj₁ z , emb-li (proj₂ z))
          (mapList (λ z → proj₁ (proj₂ z) , p2li (untagP (proj₂ (proj₂ z))))
           fs'')) = ∧r (emb-riT∧r* ((t , C , f) ∷ fs') SF1 refl refl) (emb-riT∧r* ((t' , C' , f') ∷ fs'') SF2 refl refl)
emb-riT∧r* ((.P , C , passT f) ∷ []) stop refl refl = refl
emb-riT∧r* ((.E , .(` _ , tt) , f2pT ax) ∷ []) stop refl refl = refl
emb-riT∧r* ((.E , .(I , tt) , f2pT Ir) ∷ []) stop refl refl = refl
emb-riT∧r* ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok refl f g)) ∷ []) stop refl refl = refl
emb-riT∧r* ((.L , C , f2pT (∧l₁T f)) ∷ []) stop refl refl = refl
emb-riT∧r* ((.R , C , f2pT (∧l₂T f)) ∷ []) stop refl refl = refl

⊗l-inv-fs++ : {A B : Fma} {Γ : Cxt}
  → (fs gs : List (Σ Pos (λ P → just (A ⊗ B) ∣ Γ ⊢li P)))
  → ⊗l-inv-fs (fs ++ gs) ≡ ⊗l-inv-fs fs ++ ⊗l-inv-fs gs
⊗l-inv-fs++ [] gs = refl
⊗l-inv-fs++ ((C , ⊗l f) ∷ fs) gs = cong ((C , f) ∷_) (⊗l-inv-fs++ fs gs)
{-# REWRITE ⊗l-inv-fs++ #-}

∧r*-seq-⊗l : {Γ : Cxt} {A A' B' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just (A' ⊗ B')) Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → ⊗l (∧r*-seq (mapList emb-li' (⊗l-inv-fs fs)) SF eq) ≗ ∧r*-seq (mapList emb-li' fs) SF eq
∧r*-seq-⊗l fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
∧r*-seq-⊗l {Γ} {A' = A'} {B'} .(((C , ⊗l f) ∷ fs') ++ (C' , ⊗l f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , ⊗l f) ∷ fs' , (C' , ⊗l f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-seq-refl (just (A' ⊗ B')) Γ {C} {C'} {emb-li (⊗l f)} {emb-li (⊗l f')} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs') (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs'') |
          fsDist-seq-refl (just A') (B' ∷ Γ) {C} {C'} {emb-li f} {emb-li f'} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (⊗l-inv-fs fs')) (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (⊗l-inv-fs fs'')) = 
            (~ ∧r⊗l) ∙ ∧r ((∧r*-seq-⊗l ((C , ⊗l f) ∷ fs') SF1 refl)) ((∧r*-seq-⊗l ((C' , ⊗l f') ∷ fs'') SF2 refl))
∧r*-seq-⊗l ((C , ⊗l f) ∷ []) stop refl = refl

Il-inv-fs++ : {Γ : Cxt}
  → (fs gs : List (Σ Pos (λ P → just I ∣ Γ ⊢li P)))
  → Il-inv-fs (fs ++ gs) ≡ Il-inv-fs fs ++ Il-inv-fs gs
Il-inv-fs++ [] gs = refl
Il-inv-fs++ ((C , Il f) ∷ fs) gs = cong ((C , f) ∷_) (Il-inv-fs++ fs gs)
{-# REWRITE Il-inv-fs++ #-}

∧r*-seq-Il : {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just I) Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → Il (∧r*-seq (mapList emb-li' (Il-inv-fs fs)) SF eq) ≗ ∧r*-seq (mapList emb-li' fs) SF eq
∧r*-seq-Il fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
∧r*-seq-Il {Γ} .(((C , Il f) ∷ fs') ++ (C' , Il f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , Il f) ∷ fs' , (C' , Il f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-seq-refl (just I) Γ {C} {C'} {emb-li (Il f)} {emb-li (Il f')} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs') (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs'') |
          fsDist-seq-refl - Γ {C} {C'} {emb-li f} {emb-li f'} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (Il-inv-fs fs')) (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (Il-inv-fs fs'')) = 
            (~ ∧rIl) ∙ ∧r ((∧r*-seq-Il ((C , Il f) ∷ fs') SF1 refl)) ((∧r*-seq-Il ((C' , Il f') ∷ fs'') SF2 refl))
∧r*-seq-Il ((C , Il f) ∷ []) stop refl = refl

∧r*-seq-pass : {Γ : Cxt} {A A' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → pass (∧r*-seq (mapList emb-li' fs) SF eq) 
    ≗ ∧r*-seq (mapList emb-li' (mapList (λ x → proj₁ x , p2li (pass (proj₂ x))) fs)) SF eq
∧r*-seq-pass fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
∧r*-seq-pass {Γ} {A' = A'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite fsDist-seq-refl (just A') Γ {C} {C'} {emb-li f} {emb-li f'} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs') (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs'') |
          fsDist-seq-refl - (A' ∷ Γ) {C} {C'} {pass (emb-li f)} {pass (emb-li f')} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (mapList (λ z → proj₁ z , p2li (pass (proj₂ z))) fs')) (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (mapList (λ z → proj₁ z , p2li (pass (proj₂ z))) fs'')) = 
            ~ ∧rpass ∙ ∧r (∧r*-seq-pass ((C , f) ∷ fs') SF1 refl) (∧r*-seq-pass ((C' , f') ∷ fs'') SF2 refl)
∧r*-seq-pass ((C , f) ∷ []) stop refl = refl

∧r*-seq-∧l₁ : {Γ : Cxt} {A A' B' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → ∧l₁ {B = B'} (∧r*-seq (mapList emb-li' fs) SF eq) 
    ≗ ∧r*-seq (mapList emb-li' (mapList (λ x → proj₁ x , p2li (f2p (∧l₁ (proj₂ x)))) fs)) SF eq
∧r*-seq-∧l₁ fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
∧r*-seq-∧l₁ {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl
  rewrite fsDist-seq-refl (just A') Γ {C} {C'} {emb-li f} {emb-li f'} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs') (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs'') |
          fsDist-seq-refl (just (A' ∧ B')) Γ {C} {C'} {∧l₁ (emb-li f)} {∧l₁ (emb-li f')} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (mapList (λ z → proj₁ z , p2li (f2p (∧l₁ {B = B'} (proj₂ z)))) fs')) (mapList (λ z → proj₁ z , emb-li (proj₂ z))
          (mapList (λ z → proj₁ z , p2li (f2p (∧l₁ {B = B'} (proj₂ z)))) fs'')) = 
            ~ ∧r∧l₁ ∙ ∧r (∧r*-seq-∧l₁ ((C , f) ∷ fs') SF1 refl) (∧r*-seq-∧l₁ ((C' , f') ∷ fs'') SF2 refl)
∧r*-seq-∧l₁ ((C , f) ∷ []) stop refl = refl

∧r*-seq-∧l₂ : {Γ : Cxt} {A A' B' : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just B') Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → ∧l₂ {A = A'} (∧r*-seq (mapList emb-li' fs) SF eq) 
    ≗ ∧r*-seq (mapList emb-li' (mapList (λ x → proj₁ x , p2li (f2p (∧l₂ (proj₂ x)))) fs)) SF eq
∧r*-seq-∧l₂ fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
∧r*-seq-∧l₂ {Γ} {A' = A'} {B'} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl
  rewrite fsDist-seq-refl (just B') Γ {C} {C'} {emb-li f} {emb-li f'} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs') (mapList (λ z → proj₁ z , emb-li (proj₂ z)) fs'') |
          fsDist-seq-refl (just (A' ∧ B')) Γ {C} {C'} {∧l₂ (emb-li f)} {∧l₂ (emb-li f')} (mapList (λ z → proj₁ z , emb-li (proj₂ z)) (mapList (λ z → proj₁ z , p2li (f2p (∧l₂ {A = A'} (proj₂ z)))) fs')) (mapList (λ z → proj₁ z , emb-li (proj₂ z))
          (mapList (λ z → proj₁ z , p2li (f2p (∧l₂ {A = A'} (proj₂ z)))) fs'')) = 
            ~ ∧r∧l₂ ∙ ∧r (∧r*-seq-∧l₂ ((C , f) ∷ fs') SF1 refl) (∧r*-seq-∧l₂ ((C' , f') ∷ fs'') SF2 refl)
∧r*-seq-∧l₂ ((C , f) ∷ []) stop refl = refl

embgen⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma} {C : Pos}
  → (f : S ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → (SF : SubFmas (pos C ∷ mapList (λ x → pos (proj₁ x)) fs) A)
  → (g : - ∣ Δ ⊢ri B)
  → emb-li (gen⊗r-li f fs SF g) ≗ ⊗r (∧r*-seq (emb-li' (C , f) ∷ mapList emb-li' fs) SF refl) (emb-ri g)
embgen⊗r-li (⊗l {C = C} f) fs SF g = 
  ⊗l (embgen⊗r-li f (⊗l-inv-fs fs) SF g) ∙ (~ ⊗r⊗l ∙ ⊗r (∧r*-seq-⊗l ((C , ⊗l f) ∷ fs) SF refl) refl)
embgen⊗r-li (Il {C = C} f) fs SF g = 
  Il (embgen⊗r-li f (Il-inv-fs fs) SF g) ∙ (~ ⊗rIl ∙ ⊗r (∧r*-seq-Il ((C , Il f) ∷ fs) SF refl) refl)
embgen⊗r-li {C = C} (p2li (pass f)) fs SF g with check-focus (C , p2li (pass f)) fs
... | inj₁ (inj₂ (inj₂ (A , Γ , (.C , .f) ∷ fs' , refl , refl , refl))) = 
  pass (embgen⊗r-li f fs' SF g) ∙ (~ ⊗rpass ∙ ⊗r (∧r*-seq-pass ((C , f) ∷ fs') SF refl) refl)
... | inj₂ ((.P , C' , passT .f) ∷ fs' , refl , ok) = ⊗r (emb-riT∧r* ((P , C' , passT f) ∷ fs') SF refl refl) refl
embgen⊗r-li {C = C} (p2li (pass f)) fs SF g | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l {Γ = []} ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
embgen⊗r-li {C = C} (p2li (pass f)) fs SF g | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l {Γ = x ∷ Γ} ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
embgen⊗r-li (p2li (f2p (ax {X}))) fs SF g with check-focus ((` X , tt) , p2li (f2p ax)) fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((.E , (` x , _) , f2pT ax) ∷ fs , refl , ok) = 
  ⊗r (emb-riT∧r* ((E , (` x , tt) , f2pT ax) ∷ fs) SF (cong (_∷_ (` x)) refl) refl 
  ∙ refl) refl
embgen⊗r-li (p2li (f2p Ir)) fs SF g with check-focus ((I , tt) , p2li (f2p Ir)) fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((.E , .(I , tt) , f2pT Ir) ∷ fs , refl , ok) = ⊗r (emb-riT∧r* ((E , (I , tt) , f2pT Ir) ∷ fs) SF refl refl) refl
embgen⊗r-li (p2li {S} (f2p (⊗r l {A = A} {B} ok eq f g₁))) fs SF g with check-focus {S = S} ((A ⊗ B , tt) , p2li (f2p (⊗r l ok eq f g₁))) fs
... | inj₁ (inj₁ (A' , B' , [] , refl , ()))
... | inj₁ (inj₁ (A' , B' , x ∷ fs' , refl , ()))
... | inj₁ (inj₂ (inj₁ (A' , B' , [] , refl , ())))
... | inj₁ (inj₂ (inj₁ (A' , B' , x ∷ fs' , refl , ())))
embgen⊗r-li (p2li (f2p (⊗r l {_} {[]} {A = _} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (A' , Γ' , [] , refl , refl , ())))
embgen⊗r-li (p2li (f2p (⊗r l {_} {[]} {A = _} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (A' , Γ' , x ∷ fs' , refl , refl , ())))
embgen⊗r-li (p2li (f2p (⊗r l {_} {x ∷ Γ} {Δ} {_} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , [] , refl , refl , ())))
embgen⊗r-li (p2li (f2p (⊗r l {_} {x ∷ Γ} {Δ} {_} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , x₁ ∷ fs' , refl , refl , ())))
embgen⊗r-li (p2li {S , snd} (f2p (⊗r l {S , snd} {Γ = []} {A = A} {B} ok refl f g₁))) .(mapList (λ x → proj₁ (proj₂ x) , p2li (untagP (proj₂ (proj₂ x)))) fs') SF g | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT .l .ok refl .f .g₁)) ∷ fs' , refl , ok') = 
  ⊗r (emb-riT∧r* ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok refl f g₁)) ∷ fs') SF refl refl) refl
  -- p2li (f2p (⊗r (E ∷ (mapList proj₁ fs')) tt refl (∧rT* ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok refl f g₁)) ∷ fs') SF refl refl) g))
embgen⊗r-li (p2li {S , snd} (f2p (⊗r l {S , snd} {Γ = x ∷ Γ} {A = A} {B} ok .refl f g₁))) .(mapList (λ x₁ → proj₁ (proj₂ x₁) , p2li (untagP (proj₂ (proj₂ x₁)))) fs') SF g | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT .l .ok refl .f .g₁)) ∷ fs' , refl , ok') = 
  ⊗r (emb-riT∧r* ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok refl f g₁)) ∷ fs') SF refl refl) refl
embgen⊗r-li (p2li (f2p (∧l₁ {B = B} {C = C} f))) fs SF g with check-focus (C , p2li (f2p (∧l₁ f))) fs
... | inj₁ (inj₁ (A , B , (C' , .f) ∷ fs' , refl , refl)) = 
  ∧l₁ (embgen⊗r-li f fs' SF g) ∙ ((~ ⊗r∧l₁) ∙ ⊗r (∧r*-seq-∧l₁ ((C' , f) ∷ fs') SF refl) refl)
... | inj₁ (inj₂ (inj₁ (A , B , [] , refl , ())))
... | inj₁ (inj₂ (inj₁ (A , B , x ∷ fs' , refl , ())))
... | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
... | inj₂ ((.L , C' , f2pT (∧l₁T .f)) ∷ fs' , refl , ok) = ⊗r (emb-riT∧r* ((L , C' , f2pT (∧l₁T f)) ∷ fs') SF refl refl) refl
embgen⊗r-li {C = C} (p2li (f2p (∧l₂ {A = A} f))) fs SF g with check-focus (C , p2li (f2p (∧l₂ f))) fs
... | inj₁ (inj₁ (A , B , [] , refl , ()))
... | inj₁ (inj₁ (A , B , x ∷ fs' , refl , ()))
... | inj₁ (inj₂ (inj₁ (A , B , (C' , .f) ∷ fs' , refl , refl))) = 
  ∧l₂ (embgen⊗r-li f fs' SF g) ∙ ((~ ⊗r∧l₂) ∙ ⊗r (∧r*-seq-∧l₂ ((C' , f) ∷ fs') SF refl) refl)
... | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
... | inj₂ ((.R , C' , f2pT (∧l₂T .f)) ∷ fs' , refl , ok) = ⊗r (emb-riT∧r* ((R , C' , f2pT (∧l₂T f)) ∷ fs') SF refl refl) refl

emb⊗r : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A) (g : - ∣ Δ ⊢ri B)
  → emb-ri (⊗r-ri f g) ≗ ⊗r (emb-ri f) (emb-ri g)
emb⊗r f g with f2fs f
... | (C , f') ∷ fs , .(mapList (λ x₁ → proj₁ (proj₁ x₁)) ((C , f') ∷ fs)) , refl , SF , refl = embgen⊗r-li f' fs SF g ∙ ~ (⊗r (emb∧r* ((C , f') ∷ fs) SF refl) refl)

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

embax : {C : Fma}
  → emb-ri (ax-ri {C = C}) ≗ ax
embax {` x} = refl
embax {I} = ~ axI
embax {C ⊗ D} =
  emb⊗l (⊗r-ri ax-ri (pass-ri ax-ri)) ∙ (⊗l (emb⊗r ax-ri (pass-ri ax-ri)) ∙ (⊗l (⊗r embax (embpass ax-ri ∙ pass embax)) ∙  ~ ax⊗))
embax {C ∧ D} = 
  ∧r (emb∧l₁ ax-ri) (emb∧l₂ ax-ri) ∙ (∧r (∧l₁ (embax {C = C})) (∧l₂ (embax {C = D})) ∙ (~ ax∧))

embIl : {Γ : Cxt} {C : Fma}
  → (f : - ∣ Γ ⊢ri C)
  → emb-ri (Il-ri f) ≗ Il (emb-ri f)
embIl (∧r f g) = ∧r (embIl f) (embIl g) ∙ ∧rIl
embIl (li2ri f) = refl

-- embfocus, every derivation in SeqCalc is ≗-to the its normal form
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