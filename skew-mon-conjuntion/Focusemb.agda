{-# OPTIONS --rewriting #-}

module Focusemb where

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

fT2f : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → (f : t ∣ S ∣ Γ ⊢fT C)
  → S ∣ Γ ⊢f C
fT2f ax = ax
fT2f Ir = Ir
fT2f (⊗rT l ok refl f g) = ⊗r l ok refl f g
fT2f (∧l₁T f) = ∧l₁ f
fT2f (∧l₂T f) = ∧l₂ f

pT2p : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → (f : t ∣ S ∣ Γ ⊢pT C)
  → S ∣ Γ ⊢p C
pT2p (passT f) = pass f
pT2p (f2pT f) = f2p (fT2f f)

riT2ri : {l : List Tag} {S : Irr} {Γ : Cxt} {C : Fma}
  → (f : l ∣ S ∣ Γ ⊢riT C)
  → irr S ∣ Γ ⊢ri C
riT2ri (∧rT f g) = ∧r (riT2ri f) (riT2ri g)
riT2ri (p2riT f) = li2ri (p2li (pT2p f))

fsDist-refl : (S : Irr) (Γ : Cxt) {s t : Tag} {A B : Pos}
  → {f : s ∣ S ∣ Γ ⊢pT A} {g : t ∣ S ∣ Γ ⊢pT B}
  → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t S Γ))))
  → (gs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t S Γ))))
  → fsDist ((mapList (λ z → proj₁ (proj₁ (proj₂ z))) fs)) ((mapList (λ z → proj₁ (proj₁ (proj₂ z))) gs)) ((s , A , f) ∷ fs ++ (t , B , g) ∷ gs) refl ≡ ((s , A , f) ∷ fs , (t , B , g) ∷ gs , refl , refl , refl)
fsDist-refl S Γ [] [] = refl
fsDist-refl S Γ {s} {t} {B = B} {g = g} [] ((u , C , h) ∷ gs) with fsDist [] (mapList (λ z → proj₁ (proj₁ (proj₂ z))) gs) ((t , B , g) ∷ (u , C , h) ∷ gs) refl
... | .(t , B , g) ∷ [] , .(u , C , h) ∷ .gs , refl , refl , refl = refl
fsDist-refl S Γ {A = A} {B} {f} {g} ((u , A' , f') ∷ fs) gs 
  rewrite fsDist-refl S Γ {A = A'} {B} {f'} {g} fs gs = refl
{-# REWRITE fsDist-refl #-}

f2fsT : {l : List Tag}{S : Irr} {Γ : Cxt} {A : Fma}
  → (f : l ∣ S ∣ Γ ⊢riT A)
  → Σ (List (Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢pT C)))) (λ fs → Σ (List Fma) (λ Φ → Σ (Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs) (λ eq1 → Σ (l ≡ mapList (λ x → proj₁ x) fs) (λ eq2 → Σ (SubFmas Φ A) (λ SF → f ≡ ∧rT* fs SF eq1 eq2)))))
f2fsT (∧rT f g) with f2fsT f | f2fsT g
... | (s , C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((s , C , f') ∷ fs)) , refl , refl , SF1 , refl | (t , D , g') ∷ gs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((t , D , g') ∷ gs)) , refl , refl , SF2 , refl = 
  (s , C , f') ∷ fs ++ (t , D , g') ∷ gs , (mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((s , C , f') ∷ fs)) ++ (mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((t , D , g') ∷ gs)) , refl , refl , conj SF1 SF2 , refl
f2fsT (p2riT {t} {C = C} f) = (t , C , f) ∷ [] , pos C ∷ [] , refl , refl , stop , refl

emb-pT-untagP : {S : Irr} {Γ : Cxt}
  → (f : Σ Tag (λ t → Σ Pos (λ C → (t ∣ S ∣ Γ ⊢pT C))))
  → Σ Pos (λ C → irr S ∣ Γ ⊢li C) 
emb-pT-untagP (t , C , f) = C , p2li (untagP f)

emb-pT-untagP-fs-eq : {S : Irr} {Γ : Cxt}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢pT_ t S Γ))))
  → mapList (λ x → pos (proj₁ x)) (mapList (λ x → emb-pT-untagP x) fs) ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs
emb-pT-untagP-fs-eq [] = refl
emb-pT-untagP-fs-eq (x ∷ fs) = refl

emb-pT-p2li'-untagP'-fs-eq : {S : Irr} {Γ : Cxt}
  → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t S Γ))))
  → mapList emb-pT-untagP fs ≡ mapList (λ x → p2li' (untagP' x)) fs
emb-pT-p2li'-untagP'-fs-eq [] = refl
emb-pT-p2li'-untagP'-fs-eq (x ∷ fs) = refl

emb-pT-untagP-pass : {Γ : Cxt} {A : Fma}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢pT_ t (- , tt) (A ∷ Γ)))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList emb-pT-untagP fs ≡ mapList (λ x → proj₁ x , p2li (pass (proj₂ x))) fs'
  → fs ≡ mapList (λ x → passT' x) fs'
emb-pT-untagP-pass [] [] refl = refl
emb-pT-untagP-pass ((.P , C , passT f) ∷ fs) ((C' , f') ∷ fs') eq with inj∷ eq
... | refl , eq1 = cong₂ _∷_ refl (emb-pT-untagP-pass fs fs' eq1)


emb-pT-untagP-∧l₁ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢pT_ t (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList emb-pT-untagP fs ≡ mapList (λ x → proj₁ x , p2li (f2p (∧l₁ (proj₂ x)))) fs'
  → fs ≡ mapList (λ x → f2pT' (∧l₁T' x)) fs'
emb-pT-untagP-∧l₁ [] [] refl = refl
emb-pT-untagP-∧l₁ ((.L , C , f2pT (∧l₁T f)) ∷ fs) ((C' , f') ∷ fs') eq with inj∷ eq
... | refl , eq2 = cong₂ _∷_ refl (emb-pT-untagP-∧l₁ fs fs' eq2)

emb-pT-untagP-∧l₂ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢pT_ t (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B) Γ)))
  → mapList emb-pT-untagP fs ≡ mapList (λ x → proj₁ x , p2li (f2p (∧l₂ (proj₂ x)))) fs'
  → fs ≡ mapList (λ x → f2pT' (∧l₂T' x)) fs'
emb-pT-untagP-∧l₂ [] [] refl = refl
emb-pT-untagP-∧l₂ ((.R , C , f2pT (∧l₂T f)) ∷ fs) ((C' , f') ∷ fs') eq with inj∷ eq
... | refl , eq1 = cong₂ _∷_ refl (emb-pT-untagP-∧l₂ fs fs' eq1)

emb-pT-untagP-f-eq : {t t' : Tag} {S : Irr} {Γ : Cxt} {C C' : Pos}
  → (f : t ∣ S ∣ Γ ⊢pT C)
  → (f' : t' ∣ S ∣ Γ ⊢pT C')
  → emb-pT-untagP (t , C , f) ≡ (C' , p2li (untagP f'))
  → Σ (t ≡ t') (λ eq1 → Σ (C ≡ C') (λ eq2 → f' ≡ subst₂ (λ x → λ y → x ∣ S ∣ Γ ⊢pT y) eq1 eq2 f))
emb-pT-untagP-f-eq (passT f) (passT .f) refl = refl , refl , refl
emb-pT-untagP-f-eq (f2pT ax) (f2pT ax) refl = refl , refl , refl
emb-pT-untagP-f-eq (f2pT Ir) (f2pT Ir) refl = refl , refl , refl
emb-pT-untagP-f-eq (f2pT (⊗rT l ok eq₁ f g)) (f2pT (⊗rT .l .ok .eq₁ .f .g)) refl = refl , refl , refl
emb-pT-untagP-f-eq (f2pT (∧l₁T f)) (f2pT (∧l₁T .f)) refl = refl , refl , refl
emb-pT-untagP-f-eq (f2pT (∧l₂T f)) (f2pT (∧l₂T .f)) refl = refl , refl , refl

emb-pT-untagP-fs : {S : Irr} {Γ : Cxt}
  → (fs fs' : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢pT_ t S Γ))))
  → mapList emb-pT-untagP fs ≡ mapList (λ x → proj₁ (proj₂ x) , p2li (untagP (proj₂ (proj₂ x)))) fs'
  → fs ≡ fs'
emb-pT-untagP-fs [] [] refl  = refl
emb-pT-untagP-fs ((t , C , f) ∷ fs) ((t' , C' , f') ∷ fs') eq with inj∷ eq
... | eq1 , eq2 with emb-pT-untagP-f-eq f f' eq1
... | refl , refl , refl = cong ((t , C , f) ∷_) (emb-pT-untagP-fs fs fs' eq2)


isOKL-refl : (l : List Tag)
  → (ok ok' : isOKL l)
  → ok ≡ ok'
isOKL-refl (E ∷ l) ok ok' = refl
isOKL-refl (L ∷ l) ok ok' = isOKL-refl l ok ok'
isOKL-refl (R ∷ l) ok ok' = refl

isOKL-⊥ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t₁ → Σ Pos (_∣_∣_⊢pT_ t₁ (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList emb-pT-untagP fs ≡ mapList (λ x → proj₁ x , p2li (f2p (∧l₁ (proj₂ x)))) fs'
  → (isOKL (mapList proj₁ fs))
  → ⊥
isOKL-⊥ [] [] eq ()
isOKL-⊥ ((.L , C , f2pT (∧l₁T f)) ∷ fs) ((C' , f') ∷ fs') eq ok = isOKL-⊥ fs fs' (proj₂ (inj∷ eq)) ok

isOKR-refl : (l : List Tag)
  → (ok ok' : isOKR l)
  → ok ≡ ok'
isOKR-refl (E ∷ l) ok ok' = refl
isOKR-refl (L ∷ l) ok ok' = refl
isOKR-refl (R ∷ l) ok ok' = isOKR-refl l ok ok'

isOKR-⊥ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t₁ → Σ Pos (_∣_∣_⊢pT_ t₁ (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B) Γ)))
  → mapList emb-pT-untagP fs ≡ mapList (λ x → proj₁ x , p2li (f2p (∧l₂ (proj₂ x)))) fs'
  → (isOKR (mapList proj₁ fs))
  → ⊥
isOKR-⊥ [] [] eq ()
isOKR-⊥ ((.R , C , f2pT (∧l₂T f)) ∷ fs) ((C' , f') ∷ fs') eq ok = isOKR-⊥ fs fs' (proj₂ (inj∷ eq)) ok

check-focus-all-pass : {Γ : Cxt} {A : Fma} {C : Pos}
  → (f : just A ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
  → check-focus (C , p2li (pass f)) (mapList (λ x → proj₁ x , p2li (pass (proj₂ x))) fs) 
    ≡ inj₁ (inj₂ (inj₂ (A , Γ , (C , f) ∷ fs , refl , refl , refl)))
check-focus-all-pass f [] = refl
check-focus-all-pass f ((C' , f') ∷ fs) rewrite check-focus-all-pass f' fs = refl

check-focus-ok : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → (f : t ∣ S ∣ Γ ⊢pT C)
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢pT_ t S Γ))))
  → (ok : isOK (mapList proj₁ ((t , C , f) ∷ fs)))
  → check-focus (emb-pT-untagP (t , C , f)) (mapList emb-pT-untagP fs) 
    ≡ inj₂ ((t , C , f) ∷ fs , refl , ok)
check-focus-ok (passT f) ((t , C , f') ∷ fs) ok rewrite check-focus-ok f' fs ok = refl
check-focus-ok (f2pT ax) [] ok = refl
check-focus-ok (f2pT ax) ((.E , .(` _ , tt) , f2pT ax) ∷ fs) ok rewrite check-focus-ok (f2pT ax) fs _ = refl
check-focus-ok (f2pT ax) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l {Γ = []} ok₁ refl f g)) ∷ fs) ok 
  rewrite check-focus-ok (f2pT (⊗rT l {Γ = []} ok₁ refl f g)) fs _ = refl
check-focus-ok (f2pT Ir) [] ok = refl
check-focus-ok (f2pT Ir) ((.E , .(I , tt) , f2pT Ir) ∷ fs) ok rewrite check-focus-ok (f2pT Ir) fs _ = refl
check-focus-ok (f2pT Ir) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l {Γ = []} ok₁ refl f g)) ∷ fs) ok 
  rewrite check-focus-ok (f2pT (⊗rT l {Γ = []} ok₁ refl f g)) fs _ = refl
check-focus-ok {S = S , snd} (f2pT (⊗rT l ok₁ refl f g)) [] ok with irr-eq S snd
... | refl with isIrr-unique S snd snd
... | refl = refl
check-focus-ok {S = just .(` _) , .tt} (f2pT (⊗rT l {Γ = []} ok₁ refl f g)) ((.E , .(` _ , tt) , f2pT ax) ∷ fs) ok 
  rewrite check-focus-ok (f2pT ax) fs _ = refl
check-focus-ok {S = just x , snd} (f2pT (⊗rT l ok₁ eq f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ ok₂ eq₁ f₁ g₁)) ∷ fs) ok with check-focus {S = just x , snd} (emb-pT-untagP (E , (_ ⊗ _ , tt) , f2pT (⊗rT l₁ ok₂ eq₁ f₁ g₁))) (mapList emb-pT-untagP fs)
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ())) 
... | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))) 
... | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₂ ok₄ eq₃ f₂ g₂)) ∷ fs' , eq₂ , ok₃) with inj∷ eq₂
... | refl , eq1 with emb-pT-untagP-fs fs fs' eq1
check-focus-ok {_} {just (` x) , snd} (f2pT (⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl 
  rewrite check-focus-ok (f2pT (⊗rT l₁ ok₂ eq₁ f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (` x) , snd} (f2pT (⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl with cases++ Γ' Γ Δ' Δ eq₁
check-focus-ok {_} {just (` x) , snd} (f2pT (⊗rT l {Γ = .(Γ' ++ x₁ ∷ Ω)} {Δ} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₁ (Ω , refl , refl) 
  rewrite check-focus-ok (f2pT (⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (` x) , snd} (f2pT (⊗rT l {Γ = Γ} {.(Ω ++ x₁ ∷ Δ')} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₂ (Ω , refl , refl) 
  rewrite check-focus-ok (f2pT (⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (C ∧ D) , snd} (f2pT (⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl 
  rewrite check-focus-ok (f2pT (⊗rT l₁ ok₂ eq₁ f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (C ∧ D) , snd} (f2pT (⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl with cases++ Γ' Γ Δ' Δ eq₁
check-focus-ok {_} {just (C ∧ D) , snd} (f2pT (⊗rT l {Γ = .(Γ' ++ x₁ ∷ Ω)} {Δ} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₁ (Ω , refl , refl) 
  rewrite check-focus-ok (f2pT (⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (C ∧ D) , snd} (f2pT (⊗rT l {Γ = Γ} {.(Ω ++ x₁ ∷ Δ')} ok₁ refl f g)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₂ (Ω , refl , refl) 
  rewrite check-focus-ok (f2pT (⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {S = just .(_ ∧ _) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok with check-focus (emb-pT-untagP (L , C , f2pT (∧l₁T f₁))) (mapList emb-pT-untagP fs)
... | inj₁ (inj₁ (A , B , [] , refl , ()))
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq2)) with inj∷ eq2 
... | refl , eq3 with emb-pT-untagP-∧l₁ fs fs' eq3
check-focus-ok {_} {just .(A ∧ B) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.L , C , f2pT (∧l₁T f₁)) ∷ .(mapList (λ x → L , proj₁ x , f2pT (∧l₁T (proj₂ x))) fs')) ok | inj₁ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl)) | refl , eq3 | refl = refl
check-focus-ok {_} {just .(A ∧ B) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , [] , refl , ())))
check-focus-ok {_} {just .(A ∧ B) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ())))
check-focus-ok {_} {just .(_ ∧ _) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₂ ((.L , C' , f2pT (∧l₁T f₂)) ∷ fs' , eq , ok₂) with emb-pT-untagP-fs fs fs' (proj₂ (inj∷ eq))
check-focus-ok {_} {just .(_ ∧ _) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₂ ((.L , .C , f2pT (∧l₁T .f₁)) ∷ .fs , refl , ok₂) | refl = refl
check-focus-ok {S = just .(_ ∧ _) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok with check-focus (emb-pT-untagP (R , C , f2pT (∧l₂T f₁))) (mapList emb-pT-untagP fs)
... | inj₁ (inj₁ (A , B , [] , refl , ()))
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))
... | inj₁ (inj₂ (inj₁ (A , B , [] , refl , ())))
... | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-∧l₂ fs fs' eq1
check-focus-ok {_} {just .(A ∧ B) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.R , C , f2pT (∧l₂T f₁)) ∷ .(mapList (λ x → R , proj₁ x , f2pT (∧l₂T (proj₂ x))) fs')) ok | inj₁ (inj₂ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl))) | refl , eq1 | refl = refl
check-focus-ok {S = just .(_ ∧ _) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₂ ((.R , C' , f2pT (∧l₂T f₂)) ∷ fs' , eq , ok₂) with emb-pT-untagP-fs fs fs' (proj₂ (inj∷ eq))
check-focus-ok {_} {just .(_ ∧ _) , .tt} (f2pT (⊗rT l ok₁ refl f g)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₂ ((.R , .C , f2pT (∧l₂T .f₁)) ∷ .fs , refl , ok₂) | refl = refl
check-focus-ok {S = - , tt} (f2pT (⊗rT l {Γ = []} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok with check-focus (emb-pT-untagP (P , C , passT f₁)) (mapList emb-pT-untagP fs)
... | inj₁ (inj₂ (inj₂ (A , Γ' , (C' , f') ∷ fs' , refl , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-pass fs fs' eq1
check-focus-ok {_} { - , tt} (f2pT (⊗rT l {_} {[]} ok₁ refl f g)) ((.P , C , passT f₁) ∷ .(mapList passT' fs')) ok | inj₁ (inj₂ (inj₂ (A , Γ' , (C , f₁) ∷ fs' , refl , refl , refl))) | refl , eq1 | refl = refl
check-focus-ok {_} { - , tt} (f2pT (⊗rT l {_} {[]} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C' , passT f₂) ∷ fs' , eq , ok₂) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-fs fs fs' eq1
check-focus-ok {_} { - , tt} (f2pT (⊗rT l {_} {[]} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C , passT f₁) ∷ .fs , refl , ok₂) | refl , eq1 | refl = refl
check-focus-ok {S = - , tt} (f2pT (⊗rT l {Γ = x ∷ Γ} ok₁ eq f g)) ((.P , C , passT f₁) ∷ fs) ok with check-focus (emb-pT-untagP (P , C , passT f₁)) (mapList emb-pT-untagP fs)
check-focus-ok {_} { - , tt} (f2pT (⊗rT l {_} {.A ∷ Γ} {Δ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₁ (inj₂ (inj₂ (A , .(Γ ++ Δ) , (C' , f') ∷ fs' , refl , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-pass fs fs' eq1
check-focus-ok {_} { - , tt} (f2pT (⊗rT l {_} {.A ∷ Γ} {Δ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ .(mapList passT' fs')) ok | inj₁ (inj₂ (inj₂ (A , .(Γ ++ Δ) , (C , f₁) ∷ fs' , refl , refl , refl))) | refl , refl | refl 
  rewrite check-focus-all-pass f₁ fs' = refl
check-focus-ok {_} { - , tt} (f2pT (⊗rT l {_} {x ∷ Γ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C' , passT f₂) ∷ fs' , eq , ok₂) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-fs fs fs' eq1
check-focus-ok {_} { - , tt} (f2pT (⊗rT l {_} {x ∷ Γ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C , passT f₁) ∷ .fs , refl , ok₂) | refl , eq1 | refl rewrite check-focus-ok (passT f₁) fs ok₂ = refl
check-focus-ok {S = - , tt} (f2pT (⊗rT l {Γ = []} ok₁ refl f g)) ((.E , .(I , tt) , f2pT Ir) ∷ fs) ok 
  rewrite check-focus-ok (f2pT Ir) fs _ = refl
check-focus-ok {S = - , snd} (f2pT (⊗rT l ok₁ eq f g)) ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {A = A} {B} ok₂ eq₁ f₁ g₁)) ∷ fs) ok with check-focus (emb-pT-untagP (E , (A ⊗ B , tt) , f2pT (⊗rT l₁ ok₂ eq₁ f₁ g₁))) (mapList emb-pT-untagP fs)
... | inj₁ (inj₂ (inj₂ (A' , Γ' , (C' , f') ∷ fs' , refl , refl , ())))
... | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₂ ok₄ eq₂ f₂ g₂)) ∷ fs' , eq , ok₃) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-fs fs fs' eq1
check-focus-ok {_} { - , snd} (f2pT (⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Δ)} {[]} {A = A} {B} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Δ)} {[]} ok₂ refl f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl 
  rewrite check-focus-ok (f2pT (⊗rT l₁ {A = A} {B} ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} { - , snd} (f2pT (⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x ∷ Δ'} {A = A} {B} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl with cases++ Γ' Γ Δ' Δ eq₁
check-focus-ok {_} { - , snd} (f2pT (⊗rT l {Γ = .(Γ' ++ x ∷ Ω)} {Δ} ok₁ refl f g)) ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x ∷ .(Ω ++ Δ)} {A = A} {B} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = Γ'} {x ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl | inj₁ (Ω , refl , refl) 
  rewrite check-focus-ok (f2pT (⊗rT l₁ {A = A} {B} ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} { - , snd} (f2pT (⊗rT l {Γ = Γ} {.(Ω ++ x ∷ Δ')} ok₁ refl f g)) ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x ∷ Δ'} {A = A} {B} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.E , .(A ⊗ B , tt) , f2pT (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl | inj₂ (Ω , refl , refl) 
  rewrite check-focus-ok (f2pT (⊗rT l₁ {A = A} {B} ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok (f2pT (∧l₁T f)) ((t , C , f') ∷ fs) ok with check-focus (emb-pT-untagP (t , C , f')) (mapList emb-pT-untagP fs)
check-focus-ok (f2pT (∧l₁T f)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f₁ g)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C , f') ∷ fs' , refl , ()))
check-focus-ok (f2pT (∧l₁T f)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ eq f₁ g)) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C , f') ∷ fs' , refl , ())))
check-focus-ok (f2pT (∧l₁T f)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ eq₁ f₁ g)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l₁ ok₃ eq₂ f₂ g₁)) ∷ fs' , eq , ok₂) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-fs fs fs' eq1
check-focus-ok (f2pT (∧l₁T f)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₂ refl f₁ g)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₂ refl f₁ g)) ∷ fs , refl , ok₁) | refl , eq1 | refl = refl
check-focus-ok (f2pT (∧l₁T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq)) = 
  ⊥-elim (isOKL-⊥ fs fs' (proj₂ (inj∷ eq)) ok)
check-focus-ok (f2pT (∧l₁T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))) 
check-focus-ok (f2pT (∧l₁T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₂ ((t' , C' , f2pT (∧l₁T f')) ∷ fs' , eq , ok₁) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-fs fs fs' eq1 
check-focus-ok (f2pT (∧l₁T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₂ ((.L , C , f2pT (∧l₁T f₁)) ∷ .fs , refl , ok₁) | refl , eq1 | refl rewrite isOKL-refl (mapList proj₁ fs) ok ok₁ = refl
check-focus-ok (f2pT (∧l₁T f)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))
check-focus-ok (f2pT (∧l₁T f)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-∧l₂ fs fs' eq1
check-focus-ok (f2pT (∧l₁T f)) ((.R , C , f2pT (∧l₂T f₁)) ∷ .(mapList (λ x → R , proj₁ x , f2pT (∧l₂T (proj₂ x))) fs')) ok | inj₁ (inj₂ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl))) | refl , eq1 | refl = refl
check-focus-ok (f2pT (∧l₁T f)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₂ ((.R , C' , f2pT (∧l₂T f')) ∷ fs' , eq , ok₁) with inj∷ eq
... | refl , eq1 with emb-pT-untagP-fs fs fs' eq1 
check-focus-ok (f2pT (∧l₁T f)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₂ ((.R , C , f2pT (∧l₂T f₁)) ∷ .fs , refl , ok₁) | refl , eq1 | refl = refl
check-focus-ok (f2pT (∧l₂T f)) ((t , C , f') ∷ fs) ok with check-focus (emb-pT-untagP (t , C , f')) (mapList emb-pT-untagP fs)
check-focus-ok (f2pT (∧l₂T f)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f₁ g)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , ())) 
check-focus-ok (f2pT (∧l₂T f)) ((.R , _ , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , ())) 
check-focus-ok (f2pT (∧l₂T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , eq2)) with inj∷ eq2 
... | refl , eq3 with emb-pT-untagP-∧l₁ fs fs' eq3
check-focus-ok (f2pT (∧l₂T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ .(mapList (λ x → L , proj₁ x , f2pT (∧l₁T (proj₂ x))) fs')) ok | inj₁ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl)) | refl , eq3 | refl = refl 
check-focus-ok (f2pT (∧l₂T f)) ((t , C , f') ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , eq))) = ⊥-elim (isOKR-⊥ ((t , C , f') ∷ fs) ((C' , f'') ∷ fs') eq ok)
check-focus-ok (f2pT (∧l₂T f)) ((t , C , f') ∷ fs) ok | inj₂ ((t' , C' , f'') ∷ fs' , eq , ok₁) with inj∷ eq
... | eq1 , eq2 with cong proj₁ eq1
check-focus-ok (f2pT (∧l₂T f)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₂ eq₁ f₁ g)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT .l .ok₂ .eq₁ .f₁ .g)) ∷ fs' , eq , ok₁) | refl , eq2 | refl with emb-pT-untagP-fs fs fs' eq2 
check-focus-ok (f2pT (∧l₂T f)) ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok₂ refl f₁ g)) ∷ fs) ok | inj₂ ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT .l .ok₂ .refl .f₁ .g)) ∷ .fs , refl , ok₁) | refl , eq2 | refl | refl = refl
check-focus-ok (f2pT (∧l₂T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₂ ((.L , C , f2pT (∧l₁T f₂)) ∷ fs' , eq , ok₁) | refl , eq2 | refl with emb-pT-untagP-fs fs fs' eq2
check-focus-ok (f2pT (∧l₂T f)) ((.L , C , f2pT (∧l₁T f₁)) ∷ fs) ok | inj₂ ((.L , C , f2pT (∧l₁T f₁)) ∷ .fs , refl , ok₁) | refl , eq2 | refl | refl = refl
check-focus-ok (f2pT (∧l₂T f)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₂ ((.R , C , f2pT (∧l₂T f₂)) ∷ fs' , eq , ok₁) | eq1 , eq2 | refl with emb-pT-untagP-fs fs fs' eq2
check-focus-ok (f2pT (∧l₂T f)) ((.R , C , f2pT (∧l₂T f₁)) ∷ fs) ok | inj₂ ((.R , C , f2pT (∧l₂T f₂)) ∷ fs' , refl , ok₁) | eq1 , eq2 | refl | refl rewrite check-focus-ok (f2pT (∧l₂T f₂)) fs' ok₁ | isOKR-refl (mapList proj₁ fs) ok ok₁ = refl


{-
focused derivations are in normal form, 
i.e. running the noralization algorithm would produce the same result 
-}
mutual
  focusemb-∧rT* : {l : List Tag} {S : Irr} {Γ : Cxt} {A : Fma}
    → {Φ : List Fma} 
    → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢pT_ t S Γ))))
    → (SF : SubFmas Φ A)
    → (eq1 : Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs)
    → (eq2 : l ≡ mapList proj₁ fs)
    → focus (emb-riT (∧rT* fs SF eq1 eq2)) ≡ ∧r* (mapList (λ x → emb-pT-untagP x) fs) SF eq1
  focusemb-∧rT* {S = S} {Γ} fs (conj {Φ} {Ψ} SF SF₁) eq1 refl with fsDist Φ Ψ fs eq1
  focusemb-∧rT* {S = S} {Γ} .(((t , C , f) ∷ fs') ++ (t' , C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ (proj₂ x))) fs')} {.(mapList (λ x → proj₁ (proj₁ (proj₂ x))) fs'')} SF SF₁) refl refl | (t , C , f) ∷ fs' , (t' , C' , f') ∷ fs'' , refl , refl , refl 
    rewrite fsDist-white-refl (irr S) Γ {C} {C'} {p2li (untagP f)} {p2li (untagP f')} (mapList (λ z → proj₁ (proj₂ z) , p2li (untagP (proj₂ (proj₂ z)))) fs') (mapList (λ z → proj₁ (proj₂ z) , p2li (untagP (proj₂ (proj₂ z)))) fs'') = 
      cong₂ ∧r (focusemb-∧rT* ((t , C , f) ∷ fs') SF refl refl) (focusemb-∧rT* ((t' , C' , f') ∷ fs'') SF₁ refl refl)
  focusemb-∧rT* ((.P , C , passT f) ∷ []) stop refl refl = trans (cong (pass-ri) (focusemb-li f)) refl
  focusemb-∧rT* ((.E , .(` _ , tt) , f2pT ax) ∷ []) stop refl refl = refl
  focusemb-∧rT* ((.E , .(I , tt) , f2pT Ir) ∷ []) stop refl refl = refl
  focusemb-∧rT* ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l ok refl f g)) ∷ []) stop refl refl with f2fsT f
  ... | (.P , C' , passT f) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((P , C' , passT f) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((P , C' , passT f) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-pT-untagP ((P , C' , passT f) ∷ fs)) SF refl |
            check-focus-ok (passT f) fs ok |
            focusemb-ri g = refl
  ... | (.E , .(` _ , tt) , f2pT ax) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (` _ , tt) , f2pT ax) ∷ fs)) , refl , refl , SF , refl
    rewrite focusemb-∧rT* ((E , (` _  , tt), f2pT ax) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-pT-untagP ((E , (` _  , tt), f2pT ax) ∷ fs)) SF refl |
            check-focus-ok (f2pT ax) fs ok |
            focusemb-ri g = refl
  ... | (.E , .(I , tt) , f2pT Ir) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (I , tt) , f2pT Ir) ∷ fs)) , refl , refl , SF , refl
    rewrite focusemb-∧rT* ((E , (I  , tt), f2pT Ir) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-pT-untagP ((E , (I  , tt), f2pT Ir) ∷ fs)) SF refl |
            check-focus-ok (f2pT Ir) fs ok |
            focusemb-ri g = refl
  focusemb-∧rT* ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT .(mapList proj₁ ((E , (_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((E , (_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g)) ∷ []) stop refl refl | (.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l {Γ = []} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
     rewrite focusemb-∧rT* ((E , (_ ⊗ _  , tt), f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-pT-untagP ((E , (_ ⊗ _  , tt), f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) SF refl |
            check-focus-ok (f2pT (⊗rT l ok₁ refl f g₁)) fs ok |
            focusemb-ri g = refl
  focusemb-∧rT* ((.E , .(_ ⊗ _ , tt) , f2pT (⊗rT .(mapList proj₁ ((E , (_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((E , (_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g)) ∷ []) stop refl refl | (.E , .(_ ⊗ _ , tt) , f2pT (⊗rT l {Γ = x ∷ Γ} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x₁ → proj₁ (proj₁ (proj₂ x₁))) ((E , (_ ⊗ _ , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((E , (_ ⊗ _  , tt), f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-pT-untagP ((E , (_ ⊗ _  , tt), f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) SF refl |
            check-focus-ok (f2pT (⊗rT l ok₁ refl f g₁)) fs ok |
            focusemb-ri g = refl
  ... | (.L , C' , f2pT (∧l₁T f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((L , C' , f2pT (∧l₁T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((L , C' , f2pT (∧l₁T f)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-pT-untagP ((L , C' , f2pT (∧l₁T f)) ∷ fs)) SF refl |
            check-focus-ok (f2pT (∧l₁T f)) fs ok |
            focusemb-ri g = refl
  ... | (.R , C' , f2pT (∧l₂T f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , C' , f2pT (∧l₂T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((R , C' , f2pT (∧l₂T f)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-pT-untagP ((R , C' , f2pT (∧l₂T f)) ∷ fs)) SF refl |
            check-focus-ok (f2pT (∧l₂T f)) fs ok |
            focusemb-ri g = refl
  focusemb-∧rT* ((.L , C , f2pT (∧l₁T f)) ∷ []) stop refl refl = trans (cong ∧l₁-ri (focusemb-li f)) refl
  focusemb-∧rT* ((.R , C , f2pT (∧l₂T f)) ∷ []) stop refl refl = trans (cong ∧l₂-ri (focusemb-li f)) refl

  focusemb-fT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : t ∣ S ∣ Γ ⊢fT C)
    → focus (emb-fT f) ≡ li2ri (p2li (f2p (fT2f f)))
  focusemb-fT ax = refl
  focusemb-fT Ir = refl
  focusemb-fT {S = S} (⊗rT l ok refl f g)with f2fsT f
  ... | (.P , C , passT f) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((P , C , passT f) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((P , C , passT f) ∷ fs) SF refl refl |
            f2fs-refl ((C , p2li (pass f)) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (passT f) fs ok |
            focusemb-ri g = refl
  focusemb-fT {S = .(just (` X) , tt)} (⊗rT .(mapList proj₁ ((E , (` X , tt) , f2pT ax) ∷ fs)) ok refl .(∧rT* ((E , (` X , tt) , f2pT ax) ∷ fs) SF refl refl) g) | (.E , .(` X , tt) , f2pT (ax {X = X})) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (` X , tt) , f2pT ax) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((E , (` X , _) , f2pT ax) ∷ fs) SF refl refl |
            f2fs-refl (((` X , tt) , p2li (f2p ax)) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT ax) fs tt |
            focusemb-ri g = refl
  focusemb-fT {S = .(- , tt)} (⊗rT .(mapList proj₁ ((E , (I , tt) , f2pT Ir) ∷ fs)) ok refl .(∧rT* ((E , (I , tt) , f2pT Ir) ∷ fs) SF refl refl) g) | (.E , .(I , tt) , f2pT Ir) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (I , tt) , f2pT Ir) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((E , (I , _) , f2pT Ir) ∷ fs) SF refl refl |
            f2fs-refl (((I , tt) , p2li (f2p Ir)) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT Ir) fs tt |
            focusemb-ri g = refl
  focusemb-fT {S = S} (⊗rT .(mapList proj₁ ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g) | (.E , .(A ⊗ B , tt) , f2pT (⊗rT l {Γ = []} {A = A} {B} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl
    rewrite focusemb-∧rT*  ((E , (A ⊗ B , _) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (((A ⊗ B , tt) , p2li (f2p (⊗r l ok₁ refl f g₁))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (⊗rT l ok₁ refl f g₁)) fs tt |
            focusemb-ri g = refl
  focusemb-fT {S = S} (⊗rT .(mapList proj₁ ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g) | (.E , .(A ⊗ B , tt) , f2pT (⊗rT l {Γ = x ∷ Γ} {A = A} {B} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x₁ → proj₁ (proj₁ (proj₂ x₁))) ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl
    rewrite focusemb-∧rT*  ((E , (A ⊗ B , _) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (((A ⊗ B , tt) , p2li (f2p (⊗r l ok₁ refl f g₁))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (⊗rT l ok₁ refl f g₁)) fs tt |
            focusemb-ri g = refl
  focusemb-fT {S = .(just (_ ∧ _) , tt)} (⊗rT .(mapList proj₁ ((L , C , f2pT (∧l₁T f)) ∷ fs)) ok refl .(∧rT* ((L , C , f2pT (∧l₁T f)) ∷ fs) SF refl refl) g) | (.L , C , f2pT (∧l₁T {B = B} f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((L , C , f2pT (∧l₁T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((L , C , f2pT (∧l₁T {B = B} f)) ∷ fs) SF refl refl |
            f2fs-refl ((C , p2li (f2p (∧l₁ f))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (∧l₁T {B = B} f)) fs ok |
            focusemb-ri g = refl
  focusemb-fT {S = .(just (_ ∧ _) , tt)} (⊗rT .(mapList proj₁ ((R , C , f2pT (∧l₂T f)) ∷ fs)) ok refl .(∧rT* ((R , C , f2pT (∧l₂T f)) ∷ fs) SF refl refl) g) | (.R , C , f2pT (∧l₂T {A = A} f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , C , f2pT (∧l₂T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((R , C , f2pT (∧l₂T {A = A} f)) ∷ fs) SF refl refl |
            f2fs-refl ((C , p2li (f2p (∧l₂ f))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (∧l₂T {A = A} f)) fs ok |
            focusemb-ri g  = refl
  focusemb-fT (∧l₁T f) = cong ∧l₁-ri (focusemb-li f)
  focusemb-fT (∧l₂T f) = cong ∧l₂-ri (focusemb-li f)
  
  focusemb-f : {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢f C)
    → focus (emb-f f) ≡ li2ri (p2li (f2p f))
  focusemb-f ax = refl
  focusemb-f Ir = refl
  focusemb-f {S} (⊗r l ok refl f g) with f2fsT f
  ... | (.P , C , passT f) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((P , C , passT f) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((P , C , passT f) ∷ fs) SF refl refl |
            f2fs-refl ((C , p2li (pass f)) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (passT f) fs ok |
            focusemb-ri g = refl
  focusemb-f {.(just (` X) , tt)} (⊗r .(mapList proj₁ ((E , (` X , tt) , f2pT ax) ∷ fs)) ok refl .(∧rT* ((E , (` X , tt) , f2pT ax) ∷ fs) SF refl refl) g) | (.E , .(` X , tt) , f2pT (ax {X})) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (` X , tt) , f2pT ax) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((E , (` X , _) , f2pT ax) ∷ fs) SF refl refl |
            f2fs-refl (((` X , tt) , p2li (f2p ax)) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT ax) fs tt |
            focusemb-ri g = refl
  ... | (.E , .(I , tt) , f2pT Ir) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (I , tt) , f2pT Ir) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((E , (I , _) , f2pT Ir) ∷ fs) SF refl refl |
            f2fs-refl (((I , tt) , p2li (f2p Ir)) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT Ir) fs tt |
            focusemb-ri g = refl
  focusemb-f {S} (⊗r .(mapList proj₁ ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g) | (.E , .(A ⊗ B , tt) , f2pT (⊗rT l {Γ = []} {A = A} {B} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((E , (A ⊗ B , _) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (((A ⊗ B , tt) , p2li (f2p (⊗r l ok₁ refl f g₁))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (⊗rT l ok₁ refl f g₁)) fs tt |
            focusemb-ri g = refl
  focusemb-f {S} (⊗r .(mapList proj₁ ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g) | (.E , .(A ⊗ B , tt) , f2pT (⊗rT l {Γ = x ∷ Γ} {A = A} {B} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x₁ → proj₁ (proj₁ (proj₂ x₁))) ((E , (A ⊗ B , tt) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((E , (A ⊗ B , _) , f2pT (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (((A ⊗ B , tt) , p2li (f2p (⊗r l ok₁ refl f g₁))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (⊗rT l ok₁ refl f g₁)) fs tt |
            focusemb-ri g = refl
  focusemb-f {.(just (_ ∧ _) , tt)} (⊗r .(mapList proj₁ ((L , C , f2pT (∧l₁T f)) ∷ fs)) ok refl .(∧rT* ((L , C , f2pT (∧l₁T f)) ∷ fs) SF refl refl) g) | (.L , C , f2pT (∧l₁T {B = B} f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((L , C , f2pT (∧l₁T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((L , C , f2pT (∧l₁T {B = B} f)) ∷ fs) SF refl refl |
            f2fs-refl ((C , p2li (f2p (∧l₁ f))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (∧l₁T {B = B} f)) fs ok |
            focusemb-ri g = refl
  focusemb-f {.(just (A ∧ _) , tt)} (⊗r .(mapList proj₁ ((R , C , f2pT (∧l₂T f)) ∷ fs)) ok refl .(∧rT* ((R , C , f2pT (∧l₂T f)) ∷ fs) SF refl refl) g) | (.R , C , f2pT (∧l₂T {A = A} f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , C , f2pT (∧l₂T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((R , C , f2pT (∧l₂T {A = A} f)) ∷ fs) SF refl refl |
            f2fs-refl ((C , p2li (f2p (∧l₂ f))) ∷ mapList emb-pT-untagP fs) SF refl |
            check-focus-ok (f2pT (∧l₂T {A = A} f)) fs ok |
            focusemb-ri g  = refl
  focusemb-f (∧l₁ f) = cong ∧l₁-ri (focusemb-li f)
  focusemb-f (∧l₂ f) = cong ∧l₂-ri (focusemb-li f)
  
  focusemb-pT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : t ∣ S ∣ Γ ⊢pT C)
    → focus (emb-pT f) ≡ li2ri (p2li (pT2p f))
  focusemb-pT (passT f) = cong pass-ri (focusemb-li f)
  focusemb-pT (f2pT f) = focusemb-fT f

  focusemb-p : {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢p C)
    → focus (emb-p f) ≡ li2ri (p2li f)
  focusemb-p (pass f) = cong pass-ri (focusemb-li f)
  focusemb-p (f2p f) = focusemb-f f
  
  focusemb-li : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    →  focus (emb-li f) ≡ li2ri f
  focusemb-li (⊗l f) = cong ⊗l-ri (focusemb-li f)
  focusemb-li (Il f) = cong Il-ri (focusemb-li f)
  focusemb-li (p2li f) = focusemb-p f
  
  focusemb-riT : {l : List Tag} {S : Irr} {Γ : Cxt} {C : Fma}
    → (f : l ∣ S ∣ Γ ⊢riT C)
    → focus (emb-riT f) ≡ riT2ri f
  focusemb-riT (∧rT f g) = cong₂ ∧r (focusemb-riT f) (focusemb-riT g)
  focusemb-riT (p2riT f) = focusemb-pT f

  focusemb-ri : {S : Stp} {Γ : Cxt} {C : Fma}
    → (f : S ∣ Γ ⊢ri C)
    → focus (emb-ri f) ≡ f
  focusemb-ri (∧r f g) = cong₂ ∧r (focusemb-ri f) (focusemb-ri g)
  focusemb-ri (li2ri f) = focusemb-li f                    