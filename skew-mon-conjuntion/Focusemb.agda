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

{-
In this file, we show that focused derivations are in normal form, 
i.e. running the noralization algorithm on a focused derivation would
obtain a syntactically identical derivation, i.e. focus (emb-ri f) ≡ f
-}

fsDist-refl : (S : Irr) (Γ : Cxt) {s t : Tag} {A B : Pos}
  → {f : s ∣ S ∣ Γ ⊢fT A} {g : t ∣ S ∣ Γ ⊢fT B}
  → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t S Γ))))
  → (gs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t S Γ))))
  → fsDist ((mapList (λ z → proj₁ (proj₁ (proj₂ z))) fs)) ((mapList (λ z → proj₁ (proj₁ (proj₂ z))) gs)) ((s , A , f) ∷ fs ++ (t , B , g) ∷ gs) refl ≡ ((s , A , f) ∷ fs , (t , B , g) ∷ gs , refl , refl , refl)
fsDist-refl S Γ [] [] = refl
fsDist-refl S Γ {s} {t} {B = B} {g = g} [] ((u , C , h) ∷ gs) with fsDist [] (mapList (λ z → proj₁ (proj₁ (proj₂ z))) gs) ((t , B , g) ∷ (u , C , h) ∷ gs) refl
... | .(t , B , g) ∷ [] , .(u , C , h) ∷ .gs , refl , refl , refl = refl
fsDist-refl S Γ {A = A} {B} {f} {g} ((u , A' , f') ∷ fs) gs 
  rewrite fsDist-refl S Γ {A = A'} {B} {f'} {g} fs gs = refl
{-# REWRITE fsDist-refl #-}

f2fsT : {l : List Tag}{S : Irr} {Γ : Cxt} {A : Fma}
  → (f : l ∣ S ∣ Γ ⊢riT A)
  → Σ (List (Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢fT C)))) (λ fs → Σ (List Fma) (λ Φ → Σ (Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs) (λ eq1 → Σ (l ≡ mapList (λ x → proj₁ x) fs) (λ eq2 → Σ (SubFmas Φ A) (λ SF → f ≡ ∧rT* fs SF eq1 eq2)))))
f2fsT (∧rT f g) with f2fsT f | f2fsT g
... | (s , C , f') ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((s , C , f') ∷ fs)) , refl , refl , SF1 , refl | (t , D , g') ∷ gs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((t , D , g') ∷ gs)) , refl , refl , SF2 , refl = 
  (s , C , f') ∷ fs ++ (t , D , g') ∷ gs , (mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((s , C , f') ∷ fs)) ++ (mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((t , D , g') ∷ gs)) , refl , refl , conj SF1 SF2 , refl
f2fsT (f2riT {t} {C = C} f) = (t , C , f) ∷ [] , pos C ∷ [] , refl , refl , stop , refl

emb-fT-untagF : {S : Irr} {Γ : Cxt}
  → (f : Σ Tag (λ t → Σ Pos (λ C → (t ∣ S ∣ Γ ⊢fT C))))
  → Σ Pos (λ C → irr S ∣ Γ ⊢li C) 
emb-fT-untagF (t , C , f) = C , f2li (untagF f)

emb-fT-untagF-fs-eq : {S : Irr} {Γ : Cxt}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢fT_ t S Γ))))
  → mapList (λ x → pos (proj₁ x)) (mapList (λ x → emb-fT-untagF x) fs) ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs
emb-fT-untagF-fs-eq [] = refl
emb-fT-untagF-fs-eq (x ∷ fs) = refl

emb-fT-f2li'-untagF'-fs-eq : {S : Irr} {Γ : Cxt}
  → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t S Γ))))
  → mapList emb-fT-untagF fs ≡ mapList (λ x → f2li' (untagF' x)) fs
emb-fT-f2li'-untagF'-fs-eq [] = refl
emb-fT-f2li'-untagF'-fs-eq (x ∷ fs) = refl

emb-fT-untagF-pass : {Γ : Cxt} {A : Fma}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢fT_ t (- , tt) (A ∷ Γ)))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList emb-fT-untagF fs ≡ mapList (λ x → proj₁ x , f2li (pass (proj₂ x))) fs'
  → fs ≡ mapList (λ x → passT' x) fs'
emb-fT-untagF-pass [] [] refl = refl
emb-fT-untagF-pass ((.P , C , passT f) ∷ fs) ((C' , f') ∷ fs') eq with inj∷ eq
... | refl , eq1 = cong₂ _∷_ refl (emb-fT-untagF-pass fs fs' eq1)


emb-fT-untagF-∧l₁ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢fT_ t (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList emb-fT-untagF fs ≡ mapList (λ x → proj₁ x , f2li (∧l₁ (proj₂ x))) fs'
  → fs ≡ mapList (λ x → ∧l₁T' x) fs'
emb-fT-untagF-∧l₁ [] [] refl = refl
emb-fT-untagF-∧l₁ ((.C₁ , C , ∧l₁T f) ∷ fs) ((C' , f') ∷ fs') eq with inj∷ eq
... | refl , eq2 = cong₂ _∷_ refl (emb-fT-untagF-∧l₁ fs fs' eq2)

emb-fT-untagF-∧l₂ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢fT_ t (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B) Γ)))
  → mapList emb-fT-untagF fs ≡ mapList (λ x → proj₁ x , f2li (∧l₂ (proj₂ x))) fs'
  → fs ≡ mapList (λ x → ∧l₂T' x) fs'
emb-fT-untagF-∧l₂ [] [] refl = refl
emb-fT-untagF-∧l₂ ((.C₂ , C , ∧l₂T f) ∷ fs) ((C' , f') ∷ fs') eq with inj∷ eq
... | refl , eq1 = cong₂ _∷_ refl (emb-fT-untagF-∧l₂ fs fs' eq1)

emb-fT-untagF-f-eq : {t t' : Tag} {S : Irr} {Γ : Cxt} {C C' : Pos}
  → (f : t ∣ S ∣ Γ ⊢fT C)
  → (f' : t' ∣ S ∣ Γ ⊢fT C')
  → emb-fT-untagF (t , C , f) ≡ (C' , f2li (untagF f'))
  → Σ (t ≡ t') (λ eq1 → Σ (C ≡ C') (λ eq2 → f' ≡ subst₂ (λ x → λ y → x ∣ S ∣ Γ ⊢fT y) eq1 eq2 f))
emb-fT-untagF-f-eq (passT f) (passT .f) refl = refl , refl , refl
emb-fT-untagF-f-eq ax ax refl = refl , refl , refl
emb-fT-untagF-f-eq Ir Ir refl = refl , refl , refl
emb-fT-untagF-f-eq (⊗rT l ok eq₁ f g) (⊗rT .l .ok .eq₁ .f .g) refl = refl , refl , refl
emb-fT-untagF-f-eq (∧l₁T f) (∧l₁T .f) refl = refl , refl , refl
emb-fT-untagF-f-eq (∧l₂T f) (∧l₂T .f) refl = refl , refl , refl

emb-fT-untagF-fs : {S : Irr} {Γ : Cxt}
  → (fs fs' : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢fT_ t S Γ))))
  → mapList emb-fT-untagF fs ≡ mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) fs'
  → fs ≡ fs'
emb-fT-untagF-fs [] [] refl  = refl
emb-fT-untagF-fs ((t , C , f) ∷ fs) ((t' , C' , f') ∷ fs') eq with inj∷ eq
... | eq1 , eq2 with emb-fT-untagF-f-eq f f' eq1
... | refl , refl , refl = cong ((t , C , f) ∷_) (emb-fT-untagF-fs fs fs' eq2)


isOKC₁-refl : (l : List Tag)
  → (ok ok' : isOKC₁ l)
  → ok ≡ ok'
isOKC₁-refl (R ∷ l) ok ok' = refl
isOKC₁-refl (C₁ ∷ l) ok ok' = isOKC₁-refl l ok ok'
isOKC₁-refl (C₂ ∷ l) ok ok' = refl

isOKC₁-⊥ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t₁ → Σ Pos (_∣_∣_⊢fT_ t₁ (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList emb-fT-untagF fs ≡ mapList (λ x → proj₁ x , f2li (∧l₁ (proj₂ x))) fs'
  → (isOKC₁ (mapList proj₁ fs))
  → ⊥
isOKC₁-⊥ [] [] eq ()
isOKC₁-⊥ ((.C₁ , C , ∧l₁T f) ∷ fs) ((C' , f') ∷ fs') eq ok = isOKC₁-⊥ fs fs' (proj₂ (inj∷ eq)) ok

isOKC₂-refl : (l : List Tag)
  → (ok ok' : isOKC₂ l)
  → ok ≡ ok'
isOKC₂-refl (R ∷ l) ok ok' = refl
isOKC₂-refl (C₁ ∷ l) ok ok' = refl
isOKC₂-refl (C₂ ∷ l) ok ok' = isOKC₂-refl l ok ok'

isOKC₂-⊥ : {Γ : Cxt} {A B : Fma}
  → (fs : List (Σ Tag (λ t₁ → Σ Pos (_∣_∣_⊢fT_ t₁ (just (A ∧ B) , tt) Γ))))
  → (fs' : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B) Γ)))
  → mapList emb-fT-untagF fs ≡ mapList (λ x → proj₁ x , f2li (∧l₂ (proj₂ x))) fs'
  → (isOKC₂ (mapList proj₁ fs))
  → ⊥
isOKC₂-⊥ [] [] eq ()
isOKC₂-⊥ ((.C₂ , C , ∧l₂T f) ∷ fs) ((C' , f') ∷ fs') eq ok = isOKC₂-⊥ fs fs' (proj₂ (inj∷ eq)) ok

check-focus-all-pass : {Γ : Cxt} {A : Fma} {C : Pos}
  → (f : just A ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (_∣_⊢li_ (just A) Γ)))
  → check-focus (C , f2li (pass f)) (mapList (λ x → proj₁ x , f2li (pass (proj₂ x))) fs) 
    ≡ inj₁ (inj₂ (inj₂ (A , Γ , (C , f) ∷ fs , refl , refl , refl)))
check-focus-all-pass f [] = refl
check-focus-all-pass f ((C' , f') ∷ fs) rewrite check-focus-all-pass f' fs = refl

check-focus-ok : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → (f : t ∣ S ∣ Γ ⊢fT C)
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢fT_ t S Γ))))
  → (ok : isOK (mapList proj₁ ((t , C , f) ∷ fs)))
  → check-focus (emb-fT-untagF (t , C , f)) (mapList emb-fT-untagF fs) 
    ≡ inj₂ ((t , C , f) ∷ fs , refl , ok)
check-focus-ok (passT f) ((t , C , f') ∷ fs) ok rewrite check-focus-ok f' fs ok = refl
check-focus-ok ax [] ok = refl
check-focus-ok ax ((.R , .(` _ , tt) , ax) ∷ fs) ok rewrite check-focus-ok ax fs _ = refl
check-focus-ok ax ((.R , .(_ ⊗ _ , tt) , ⊗rT l {Γ = []} ok₁ refl f g) ∷ fs) ok 
  rewrite check-focus-ok (⊗rT l {Γ = []} ok₁ refl f g) fs _ = refl
check-focus-ok Ir [] ok = refl
check-focus-ok Ir ((.R , .(I , tt) , Ir) ∷ fs) ok rewrite check-focus-ok Ir fs _ = refl
check-focus-ok Ir ((.R , .(_ ⊗ _ , tt) , ⊗rT l {Γ = []} ok₁ refl f g) ∷ fs) ok 
  rewrite check-focus-ok (⊗rT l {Γ = []} ok₁ refl f g) fs _ = refl
check-focus-ok {S = S , snd} (⊗rT l ok₁ refl f g) [] ok with irr-eq S snd
... | refl with isIrr-unique S snd snd
... | refl = refl
check-focus-ok {S = just .(` _) , .tt} ((⊗rT l {Γ = []} ok₁ refl f g)) ((.R , .(` _ , tt) , ax) ∷ fs) ok 
  rewrite check-focus-ok ax fs _ = refl
check-focus-ok {S = just x , snd} ((⊗rT l ok₁ eq f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ ok₂ eq₁ f₁ g₁)) ∷ fs) ok with check-focus {S = just x , snd} (emb-fT-untagF (R , (_ ⊗ _ , tt) , (⊗rT l₁ ok₂ eq₁ f₁ g₁))) (mapList emb-fT-untagF fs)
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ())) 
... | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))) 
... | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₂ ok₄ eq₃ f₂ g₂)) ∷ fs' , eq₂ , ok₃) with inj∷ eq₂
... | refl , eq1 with emb-fT-untagF-fs fs fs' eq1
check-focus-ok {_} {just (` x) , snd} ((⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl 
  rewrite check-focus-ok ((⊗rT l₁ ok₂ eq₁ f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (` x) , snd} ((⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl with cases++ Γ' Γ Δ' Δ eq₁
check-focus-ok {_} {just (` x) , snd} ((⊗rT l {Γ = .(Γ' ++ x₁ ∷ Ω)} {Δ} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₁ (Ω , refl , refl) 
  rewrite check-focus-ok ((⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (` x) , snd} ((⊗rT l {Γ = Γ} {.(Ω ++ x₁ ∷ Δ')} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₂ (Ω , refl , refl) 
  rewrite check-focus-ok ((⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (C ∧ D) , snd} ((⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {[]} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl 
  rewrite check-focus-ok ((⊗rT l₁ ok₂ eq₁ f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (C ∧ D) , snd} ((⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl with cases++ Γ' Γ Δ' Δ eq₁
check-focus-ok {_} {just (C ∧ D) , snd} ((⊗rT l {Γ = .(Γ' ++ x₁ ∷ Ω)} {Δ} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = Γ'} {x₁ ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₁ (Ω , refl , refl) 
  rewrite check-focus-ok ((⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} {just (C ∧ D) , snd} ((⊗rT l {Γ = Γ} {.(Ω ++ x₁ ∷ Δ')} ok₁ refl f g)) ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x₁ ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs , eq₂ , ok₃) | refl , eq1 | refl | inj₂ (Ω , refl , refl) 
  rewrite check-focus-ok ((⊗rT l₁ ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {S = just .(_ ∧ _) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok with check-focus (emb-fT-untagF (C₁ , C , ∧l₁T f₁)) (mapList emb-fT-untagF fs)
... | inj₁ (inj₁ (A , B , [] , refl , ()))
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq2)) with inj∷ eq2 
... | refl , eq3 with emb-fT-untagF-∧l₁ fs fs' eq3
check-focus-ok {_} {just .(A ∧ B) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₁ , C , ∧l₁T f₁) ∷ .(mapList (λ x → C₁ , proj₁ x , ∧l₁T (proj₂ x)) fs')) ok | inj₁ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl)) | refl , eq3 | refl = refl
check-focus-ok {_} {just .(A ∧ B) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , [] , refl , ())))
check-focus-ok {_} {just .(A ∧ B) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ())))
check-focus-ok {_} {just .(_ ∧ _) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₂ ((.C₁ , C' , (∧l₁T f₂)) ∷ fs' , eq , ok₂) with emb-fT-untagF-fs fs fs' (proj₂ (inj∷ eq))
check-focus-ok {_} {just .(_ ∧ _) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₂ ((.C₁ , .C , (∧l₁T .f₁)) ∷ .fs , refl , ok₂) | refl = refl
check-focus-ok {S = just .(_ ∧ _) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok with check-focus (emb-fT-untagF (C₂ , C , ∧l₂T f₁)) (mapList emb-fT-untagF fs)
... | inj₁ (inj₁ (A , B , [] , refl , ()))
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))
... | inj₁ (inj₂ (inj₁ (A , B , [] , refl , ())))
... | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-∧l₂ fs fs' eq1
check-focus-ok {_} {just .(A ∧ B) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₂ , C , ∧l₂T f₁) ∷ .(mapList (λ x → C₂ , proj₁ x , ∧l₂T (proj₂ x)) fs')) ok | inj₁ (inj₂ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl))) | refl , eq1 | refl = refl
check-focus-ok {S = just .(_ ∧ _) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₂ ((.C₂ , C' , ∧l₂T f₂) ∷ fs' , eq , ok₂) with emb-fT-untagF-fs fs fs' (proj₂ (inj∷ eq))
check-focus-ok {_} {just .(_ ∧ _) , .tt} ((⊗rT l ok₁ refl f g)) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₂ ((.C₂ , .C , ∧l₂T .f₁) ∷ .fs , refl , ok₂) | refl = refl
check-focus-ok {S = - , tt} ((⊗rT l {Γ = []} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok with check-focus (emb-fT-untagF (P , C , passT f₁)) (mapList emb-fT-untagF fs)
... | inj₁ (inj₂ (inj₂ (A , Γ' , (C' , f') ∷ fs' , refl , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-pass fs fs' eq1
check-focus-ok {_} { - , tt} ((⊗rT l {_} {[]} ok₁ refl f g)) ((.P , C , passT f₁) ∷ .(mapList passT' fs')) ok | inj₁ (inj₂ (inj₂ (A , Γ' , (C , f₁) ∷ fs' , refl , refl , refl))) | refl , eq1 | refl = refl
check-focus-ok {_} { - , tt} ((⊗rT l {_} {[]} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C' , passT f₂) ∷ fs' , eq , ok₂) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-fs fs fs' eq1
check-focus-ok {_} { - , tt} ((⊗rT l {_} {[]} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C , passT f₁) ∷ .fs , refl , ok₂) | refl , eq1 | refl = refl
check-focus-ok {S = - , tt} ((⊗rT l {Γ = x ∷ Γ} ok₁ eq f g)) ((.P , C , passT f₁) ∷ fs) ok with check-focus (emb-fT-untagF (P , C , passT f₁)) (mapList emb-fT-untagF fs)
check-focus-ok {_} { - , tt} ((⊗rT l {_} {.A ∷ Γ} {Δ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₁ (inj₂ (inj₂ (A , .(Γ ++ Δ) , (C' , f') ∷ fs' , refl , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-pass fs fs' eq1
check-focus-ok {_} { - , tt} ((⊗rT l {_} {.A ∷ Γ} {Δ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ .(mapList passT' fs')) ok | inj₁ (inj₂ (inj₂ (A , .(Γ ++ Δ) , (C , f₁) ∷ fs' , refl , refl , refl))) | refl , refl | refl 
  rewrite check-focus-all-pass f₁ fs' = refl
check-focus-ok {_} { - , tt} ((⊗rT l {_} {x ∷ Γ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C' , passT f₂) ∷ fs' , eq , ok₂) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-fs fs fs' eq1
check-focus-ok {_} { - , tt} ((⊗rT l {_} {x ∷ Γ} ok₁ refl f g)) ((.P , C , passT f₁) ∷ fs) ok | inj₂ ((.P , C , passT f₁) ∷ .fs , refl , ok₂) | refl , eq1 | refl rewrite check-focus-ok (passT f₁) fs ok₂ = refl
check-focus-ok {S = - , tt} ((⊗rT l {Γ = []} ok₁ refl f g)) ((.R , .(I , tt) , Ir) ∷ fs) ok 
  rewrite check-focus-ok Ir fs _ = refl
check-focus-ok {S = - , snd} ((⊗rT l ok₁ eq f g)) ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {A = A} {B} ok₂ eq₁ f₁ g₁)) ∷ fs) ok with check-focus (emb-fT-untagF (R , (A ⊗ B , tt) , (⊗rT l₁ ok₂ eq₁ f₁ g₁))) (mapList emb-fT-untagF fs)
... | inj₁ (inj₂ (inj₂ (A' , Γ' , (C' , f') ∷ fs' , refl , refl , ())))
... | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₂ ok₄ eq₂ f₂ g₂)) ∷ fs' , eq , ok₃) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-fs fs fs' eq1
check-focus-ok {_} { - , snd} ((⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = .(Γ ++ Δ)} {[]} {A = A} {B} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = .(Γ ++ Δ)} {[]} ok₂ refl f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl 
  rewrite check-focus-ok ((⊗rT l₁ {A = A} {B} ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} { - , snd} ((⊗rT l {Γ = Γ} {Δ} ok₁ refl f g)) ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = Γ'} {x ∷ Δ'} {A = A} {B} ok₂ eq₁ f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = Γ'} {x ∷ Δ'} ok₂ eq₁ f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl with cases++ Γ' Γ Δ' Δ eq₁
check-focus-ok {_} { - , snd} ((⊗rT l {Γ = .(Γ' ++ x ∷ Ω)} {Δ} ok₁ refl f g)) ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = Γ'} {x ∷ .(Ω ++ Δ)} {A = A} {B} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = Γ'} {x ∷ .(Ω ++ Δ)} ok₂ refl f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl | inj₁ (Ω , refl , refl) 
  rewrite check-focus-ok ((⊗rT l₁ {A = A} {B} ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok {_} { - , snd} ((⊗rT l {Γ = Γ} {.(Ω ++ x ∷ Δ')} ok₁ refl f g)) ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x ∷ Δ'} {A = A} {B} ok₂ refl f₁ g₁)) ∷ fs) ok | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT l₁ {Γ = .(Γ ++ Ω)} {x ∷ Δ'} ok₂ refl f₁ g₁)) ∷ fs , refl , ok₃) | refl , eq1 | refl | inj₂ (Ω , refl , refl) 
  rewrite check-focus-ok ((⊗rT l₁ {A = A} {B} ok₂ refl f₁ g₁)) fs tt = refl
check-focus-ok (∧l₁T f) ((t , C , f') ∷ fs) ok with check-focus (emb-fT-untagF (t , C , f')) (mapList emb-fT-untagF fs)
check-focus-ok (∧l₁T f) ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₁ refl f₁ g)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C , f') ∷ fs' , refl , ()))
check-focus-ok (∧l₁T f) ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₁ eq f₁ g)) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C , f') ∷ fs' , refl , ())))
check-focus-ok (∧l₁T f) ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₁ eq₁ f₁ g)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l₁ ok₃ eq₂ f₂ g₁)) ∷ fs' , eq , ok₂) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-fs fs fs' eq1
check-focus-ok (∧l₁T f) ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₂ refl f₁ g)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₂ refl f₁ g)) ∷ fs , refl , ok₁) | refl , eq1 | refl = refl
check-focus-ok (∧l₁T f) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq)) = 
  ⊥-elim (isOKC₁-⊥ fs fs' (proj₂ (inj∷ eq)) ok)
check-focus-ok (∧l₁T f) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))) 
check-focus-ok (∧l₁T f) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₂ ((t' , C' , ∧l₁T f') ∷ fs' , eq , ok₁) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-fs fs fs' eq1 
check-focus-ok (∧l₁T f) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₂ ((.C₁ , C , ∧l₁T f₁) ∷ .fs , refl , ok₁) | refl , eq1 | refl rewrite isOKC₁-refl (mapList proj₁ fs) ok ok₁ = refl
check-focus-ok (∧l₁T f) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , ()))
check-focus-ok (∧l₁T f) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq))) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-∧l₂ fs fs' eq1
check-focus-ok (∧l₁T f) ((.C₂ , C , ∧l₂T f₁) ∷ .(mapList (λ x → C₂ , proj₁ x , (∧l₂T (proj₂ x))) fs')) ok | inj₁ (inj₂ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl))) | refl , eq1 | refl = refl
check-focus-ok (∧l₁T f) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₂ ((.C₂ , C' , (∧l₂T f')) ∷ fs' , eq , ok₁) with inj∷ eq
... | refl , eq1 with emb-fT-untagF-fs fs fs' eq1 
check-focus-ok (∧l₁T f) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₂ ((.C₂ , C , ∧l₂T f₁) ∷ .fs , refl , ok₁) | refl , eq1 | refl = refl
check-focus-ok (∧l₂T f) ((t , C , f') ∷ fs) ok with check-focus (emb-fT-untagF (t , C , f')) (mapList emb-fT-untagF fs)
check-focus-ok (∧l₂T f) ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₁ refl f₁ g)) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , ())) 
check-focus-ok (∧l₂T f) ((.C₂ , _ , ∧l₂T f₁) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , ())) 
check-focus-ok (∧l₂T f) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₁ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , eq2)) with inj∷ eq2 
... | refl , eq3 with emb-fT-untagF-∧l₁ fs fs' eq3
check-focus-ok (∧l₂T f) ((.C₁ , C , ∧l₁T f₁) ∷ .(mapList (λ x → C₁ , proj₁ x , ∧l₁T (proj₂ x)) fs')) ok | inj₁ (inj₁ (A , B , (C , f₁) ∷ fs' , refl , refl)) | refl , eq3 | refl = refl 
check-focus-ok (∧l₂T f) ((t , C , f') ∷ fs) ok | inj₁ (inj₂ (inj₁ (A , B , (C' , f'') ∷ fs' , refl , eq))) = ⊥-elim (isOKC₂-⊥ ((t , C , f') ∷ fs) ((C' , f'') ∷ fs') eq ok)
check-focus-ok (∧l₂T f) ((t , C , f') ∷ fs) ok | inj₂ ((t' , C' , f'') ∷ fs' , eq , ok₁) with inj∷ eq
... | eq1 , eq2 with cong proj₁ eq1
check-focus-ok (∧l₂T f) ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₂ eq₁ f₁ g)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT .l .ok₂ .eq₁ .f₁ .g)) ∷ fs' , eq , ok₁) | refl , eq2 | refl with emb-fT-untagF-fs fs fs' eq2 
check-focus-ok (∧l₂T f) ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₂ refl f₁ g)) ∷ fs) ok | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT .l .ok₂ .refl .f₁ .g)) ∷ .fs , refl , ok₁) | refl , eq2 | refl | refl = refl
check-focus-ok (∧l₂T f) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₂ ((.C₁ , C , ∧l₁T f₂) ∷ fs' , eq , ok₁) | refl , eq2 | refl with emb-fT-untagF-fs fs fs' eq2
check-focus-ok (∧l₂T f) ((.C₁ , C , ∧l₁T f₁) ∷ fs) ok | inj₂ ((.C₁ , C , ∧l₁T f₁) ∷ .fs , refl , ok₁) | refl , eq2 | refl | refl = refl
check-focus-ok (∧l₂T f) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₂ ((.C₂ , C , ∧l₂T f₂) ∷ fs' , eq , ok₁) | eq1 , eq2 | refl with emb-fT-untagF-fs fs fs' eq2
check-focus-ok (∧l₂T f) ((.C₂ , C , ∧l₂T f₁) ∷ fs) ok | inj₂ ((.C₂ , C , ∧l₂T f₂) ∷ fs' , refl , ok₁) | eq1 , eq2 | refl | refl rewrite check-focus-ok (∧l₂T f₂) fs' ok₁ | isOKC₂-refl (mapList proj₁ fs) ok ok₁ = refl


-- focus (emb-ri f) ≡ f
mutual
  focusemb-∧rT* : {l : List Tag} {S : Irr} {Γ : Cxt} {A : Fma}
    → {Φ : List Fma} 
    → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t S Γ))))
    → (SF : SubFmas Φ A)
    → (eq1 : Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs)
    → (eq2 : l ≡ mapList proj₁ fs)
    → focus (emb-riT (∧rT* fs SF eq1 eq2)) ≡ ∧r* (mapList (λ x → emb-fT-untagF x) fs) SF eq1
  focusemb-∧rT* {S = S} {Γ} fs (conj {Φ} {Ψ} SF SF₁) eq1 refl with fsDist Φ Ψ fs eq1
  focusemb-∧rT* {S = S} {Γ} .(((t , C , f) ∷ fs') ++ (t' , C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ (proj₂ x))) fs')} {.(mapList (λ x → proj₁ (proj₁ (proj₂ x))) fs'')} SF SF₁) refl refl | (t , C , f) ∷ fs' , (t' , C' , f') ∷ fs'' , refl , refl , refl 
    rewrite fsDist-white-refl (irr S) Γ {C} {C'} {f2li (untagF f)} {f2li (untagF f')} (mapList (λ z → proj₁ (proj₂ z) , f2li (untagF (proj₂ (proj₂ z)))) fs') (mapList (λ z → proj₁ (proj₂ z) , f2li (untagF (proj₂ (proj₂ z)))) fs'') = 
      cong₂ ∧r (focusemb-∧rT* ((t , C , f) ∷ fs') SF refl refl) (focusemb-∧rT* ((t' , C' , f') ∷ fs'') SF₁ refl refl)
  focusemb-∧rT* ((.P , C , passT f) ∷ []) stop refl refl = trans (cong (pass-ri) (focusemb-li f)) refl
  focusemb-∧rT* ((.R , .(` _ , tt) , ax) ∷ []) stop refl refl = refl
  focusemb-∧rT* ((.R , .(I , tt) , Ir) ∷ []) stop refl refl = refl
  focusemb-∧rT* ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok refl f g)) ∷ []) stop refl refl with f2fsT f
  ... | (.P , C' , passT f) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((P , C' , passT f) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((P , C' , passT f) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-fT-untagF ((P , C' , passT f) ∷ fs)) SF refl |
            check-focus-ok (passT f) fs ok |
            focusemb-ri g = refl
  ... | (.R , .(` _ , tt) , ax) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , (` _ , tt) , ax) ∷ fs)) , refl , refl , SF , refl
    rewrite focusemb-∧rT* ((R , (` _  , tt), ax) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-fT-untagF ((R , (` _  , tt), ax) ∷ fs)) SF refl |
            check-focus-ok ax fs ok |
            focusemb-ri g = refl
  ... | (.R , .(I , tt) , Ir) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , (I , tt) , Ir) ∷ fs)) , refl , refl , SF , refl
    rewrite focusemb-∧rT* ((R , (I  , tt), Ir) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-fT-untagF ((R , (I  , tt), Ir) ∷ fs)) SF refl |
            check-focus-ok Ir fs ok |
            focusemb-ri g = refl
  focusemb-∧rT* ((.R , .(_ ⊗ _ , tt) , (⊗rT .(mapList proj₁ ((R , (_ ⊗ _ , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((R , (_ ⊗ _ , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g)) ∷ []) stop refl refl | (.R , .(_ ⊗ _ , tt) , (⊗rT l {Γ = []} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , (_ ⊗ _ , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
     rewrite focusemb-∧rT* ((R , (_ ⊗ _  , tt), (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-fT-untagF ((R , (_ ⊗ _  , tt), (⊗rT l ok₁ refl f g₁)) ∷ fs)) SF refl |
            check-focus-ok ((⊗rT l ok₁ refl f g₁)) fs ok |
            focusemb-ri g = refl
  focusemb-∧rT* ((.R , .(_ ⊗ _ , tt) , (⊗rT .(mapList proj₁ ((R , (_ ⊗ _ , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((R , (_ ⊗ _ , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g)) ∷ []) stop refl refl | (.R , .(_ ⊗ _ , tt) , (⊗rT l {Γ = x ∷ Γ} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x₁ → proj₁ (proj₁ (proj₂ x₁))) ((R , (_ ⊗ _ , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((R , (_ ⊗ _  , tt), (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-fT-untagF ((R , (_ ⊗ _  , tt), (⊗rT l ok₁ refl f g₁)) ∷ fs)) SF refl |
            check-focus-ok ((⊗rT l ok₁ refl f g₁)) fs ok |
            focusemb-ri g = refl
  ... | (.C₁ , C' , (∧l₁T f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((C₁ , C' , (∧l₁T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((C₁ , C' , (∧l₁T f)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-fT-untagF ((C₁ , C' , (∧l₁T f)) ∷ fs)) SF refl |
            check-focus-ok (∧l₁T f) fs ok |
            focusemb-ri g = refl
  ... | (.C₂ , C' , (∧l₂T f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((C₂ , C' , (∧l₂T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT* ((C₂ , C' , (∧l₂T f)) ∷ fs) SF refl refl |
            f2fs-refl (mapList emb-fT-untagF ((C₂ , C' , (∧l₂T f)) ∷ fs)) SF refl |
            check-focus-ok  (∧l₂T f) fs ok |
            focusemb-ri g = refl
  focusemb-∧rT* ((.C₁ , C , (∧l₁T f)) ∷ []) stop refl refl = trans (cong ∧l₁-ri (focusemb-li f)) refl
  focusemb-∧rT* ((.C₂ , C , (∧l₂T f)) ∷ []) stop refl refl = trans (cong ∧l₂-ri (focusemb-li f)) refl
  
  focusemb-f : {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢f C)
    → focus (emb-f f) ≡ li2ri (f2li f)
  focusemb-f ax = refl
  focusemb-f Ir = refl
  focusemb-f (pass f) = cong pass-ri (focusemb-li f)
  focusemb-f {S} (⊗r l ok refl f g) with f2fsT f
  ... | (.P , C , passT f) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((P , C , passT f) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((P , C , passT f) ∷ fs) SF refl refl |
            f2fs-refl ((C , f2li (pass f)) ∷ mapList emb-fT-untagF fs) SF refl |
            check-focus-ok (passT f) fs ok |
            focusemb-ri g = refl
  focusemb-f {.(just (` X) , tt)} (⊗r .(mapList proj₁ ((R , (` X , tt) , ax) ∷ fs)) ok refl .(∧rT* ((R , (` X , tt) , ax) ∷ fs) SF refl refl) g) | (.R , .(` X , tt) , (ax {X})) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , (` X , tt) , ax) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((R , (` X , _) , ax) ∷ fs) SF refl refl |
            f2fs-refl (((` X , tt) , f2li (ax)) ∷ mapList emb-fT-untagF fs) SF refl |
            check-focus-ok ax fs tt |
            focusemb-ri g = refl
  ... | (.R , .(I , tt) , Ir) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , (I , tt) , Ir) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((R , (I , _) , Ir) ∷ fs) SF refl refl |
            f2fs-refl (((I , tt) , f2li (Ir)) ∷ mapList emb-fT-untagF fs) SF refl |
            check-focus-ok Ir fs tt |
            focusemb-ri g = refl
  focusemb-f {S} (⊗r .(mapList proj₁ ((R , (A ⊗ B , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((R , (A ⊗ B , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g) | (.R , .(A ⊗ B , tt) , (⊗rT l {Γ = []} {A = A} {B} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((R , (A ⊗ B , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((R , (A ⊗ B , _) , (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (((A ⊗ B , tt) , f2li ((⊗r l ok₁ refl f g₁))) ∷ mapList emb-fT-untagF fs) SF refl |
            check-focus-ok ((⊗rT l ok₁ refl f g₁)) fs tt |
            focusemb-ri g = refl
  focusemb-f {S} (⊗r .(mapList proj₁ ((R , (A ⊗ B , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) ok refl .(∧rT* ((R , (A ⊗ B , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl) g) | (.R , .(A ⊗ B , tt) , (⊗rT l {Γ = x ∷ Γ} {A = A} {B} ok₁ refl f g₁)) ∷ fs , .(mapList (λ x₁ → proj₁ (proj₁ (proj₂ x₁))) ((R , (A ⊗ B , tt) , (⊗rT l ok₁ refl f g₁)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((R , (A ⊗ B , _) , (⊗rT l ok₁ refl f g₁)) ∷ fs) SF refl refl |
            f2fs-refl (((A ⊗ B , tt) , f2li ((⊗r l ok₁ refl f g₁))) ∷ mapList emb-fT-untagF fs) SF refl |
            check-focus-ok ((⊗rT l ok₁ refl f g₁)) fs tt |
            focusemb-ri g = refl
  focusemb-f {.(just (_ ∧ _) , tt)} (⊗r .(mapList proj₁ ((C₁ , C , (∧l₁T f)) ∷ fs)) ok refl .(∧rT* ((C₁ , C , (∧l₁T f)) ∷ fs) SF refl refl) g) | (.C₁ , C , (∧l₁T {B = B} f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((C₁ , C , (∧l₁T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((C₁ , C , (∧l₁T {B = B} f)) ∷ fs) SF refl refl |
            f2fs-refl ((C , f2li ((∧l₁ f))) ∷ mapList emb-fT-untagF fs) SF refl |
            check-focus-ok ((∧l₁T {B = B} f)) fs ok |
            focusemb-ri g = refl
  focusemb-f {.(just (A ∧ _) , tt)} (⊗r .(mapList proj₁ ((C₂ , C , (∧l₂T f)) ∷ fs)) ok refl .(∧rT* ((C₂ , C , (∧l₂T f)) ∷ fs) SF refl refl) g) | (.C₂ , C , (∧l₂T {A = A} f)) ∷ fs , .(mapList (λ x → proj₁ (proj₁ (proj₂ x))) ((C₂ , C , (∧l₂T f)) ∷ fs)) , refl , refl , SF , refl 
    rewrite focusemb-∧rT*  ((C₂ , C , (∧l₂T {A = A} f)) ∷ fs) SF refl refl |
            f2fs-refl ((C , f2li ((∧l₂ f))) ∷ mapList emb-fT-untagF fs) SF refl |
            check-focus-ok ((∧l₂T {A = A} f)) fs ok |
            focusemb-ri g  = refl
  focusemb-f (∧l₁ f) = cong ∧l₁-ri (focusemb-li f)
  focusemb-f (∧l₂ f) = cong ∧l₂-ri (focusemb-li f)
  
  
  focusemb-li : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    →  focus (emb-li f) ≡ li2ri f
  focusemb-li (⊗l f) = cong ⊗l-ri (focusemb-li f)
  focusemb-li (Il f) = cong Il-ri (focusemb-li f)
  focusemb-li (f2li f) = focusemb-f f

  focusemb-ri : {S : Stp} {Γ : Cxt} {C : Fma}
    → (f : S ∣ Γ ⊢ri C)
    → focus (emb-ri f) ≡ f
  focusemb-ri (∧r f g) = cong₂ ∧r (focusemb-ri f) (focusemb-ri g)
  focusemb-ri (li2ri f) = focusemb-li f                    