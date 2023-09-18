{-# OPTIONS --rewriting #-}

module CheckFocus where

open import Data.List renaming (map to mapList; zip to zipList)
open import Data.List.Relation.Unary.All renaming (map to mapAll; reduce to reduceAll)
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
open import TagUntag

{-
Given a list of sequents in phase li,
the shape of the proof must be in one 
of four cases below:
i) All sequents are conclusion of ∧l₁.
ii) All sequents are conclusion of ∧l₂.
iii) All sequents are conclusion of pass.
iv) The list of sequents can generate 
a list of sequents in phase fT.
-}

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
    (Σ (List (Tag × Pos)) λ Ψ → Σ (All (match-fT S Γ) Ψ) λ fs' 
      →  Σ (proj₁ (tagF-fs {S} (f ∷ fs)) ≡ Ψ) λ eq → fs' ≡ subst (λ x → All (match-fT S Γ) x) eq (proj₂ (tagF-fs (f ∷ fs))) × isOK (mapList proj₁ Ψ))
check-focus (f2li ax) [] = inj₂ ((R , _) ∷ [] , ax ∷ [] , refl , refl , _)
check-focus (f2li Ir) [] = inj₂ ((R , _) ∷ [] , Ir ∷ [] , refl , refl , _)
check-focus (f2li (pass f)) [] = inj₁ (inj₂ (inj₂ (_ , _ , f ∷ [] , refl , refl , refl)))
check-focus {S , p} (f2li {.(irr (S , p)) , q} (⊗r l ok eq f g)) [] 
  rewrite irr-eq S p | isIrr-unique S p q  = inj₂ ((R , _) ∷ [] , ⊗rT l ok eq f g ∷ [] , refl , refl , _)
check-focus (f2li (∧l₁ f)) [] = inj₁ (inj₁ (_ , _ , f ∷ [] , refl , refl))
check-focus (f2li (∧l₂ f)) [] = inj₁ (inj₂ (inj₁ (_ , _ , f ∷ [] , refl , refl)))
check-focus {S , p} (f2li {.(irr (S , p)) , q} (∨r₁ l ok f)) []
  rewrite irr-eq S p | isIrr-unique S p q = inj₂ ((R , _) ∷ [] , ∨r₁T l ok f ∷ [] , refl , refl , _)
check-focus {S , p} (f2li {.(irr (S , p)) , q} (∨r₂ l ok f)) []
  rewrite irr-eq S p | isIrr-unique S p q =  inj₂ ((R , _) ∷ [] , ∨r₂T l ok f ∷ [] , refl , refl , _)
check-focus {.(just (` _)) , snd} (f2li {.(irr (just (` _) , snd)) , .tt} ax) (f' ∷ fs) = inj₂ (_ ∷ _ , ax ∷ proj₂ (tagF-fs (f' ∷ fs)) , refl , refl , _)
check-focus {.- , snd} (f2li {.(irr (- , snd)) , .tt} Ir) (f' ∷ fs) = inj₂ (_ ∷ _ , Ir ∷ proj₂ (tagF-fs (f' ∷ fs)) , refl , refl , _)
check-focus {.- , snd} (f2li {.(irr (- , snd)) , .tt} (pass f)) (f' ∷ fs) with check-focus  f' fs
... | inj₁ (inj₂ (inj₂ (A , Γ , f'' ∷ fs' , refl , refl , refl))) = inj₁ (inj₂ (inj₂ (A , Γ , f ∷ f'' ∷ fs' , refl , refl , refl)))
check-focus {.(irr (- , tt)) , snd} (f2li {.- , .tt} (pass f)) (f2li (pass f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (pass f₁) ∷ fs)))) , refl , refl , ok) = inj₂ (_ ∷ _ , passT f ∷ passT f₁ ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (- , tt)) , snd} (f2li {.- , .tt} (pass f)) (f2li (⊗r l ok₁ eq₁ f₁ g) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (⊗r l ok₁ eq₁ f₁ g) ∷ fs)))) , refl , refl , ok) = inj₂ (_ ∷ _ , passT f ∷ ⊗rT l ok₁ eq₁ f₁ g ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (- , tt)) , snd} (f2li {.- , .tt} (pass f)) (f2li (∨r₁ l ok₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (∨r₁ l ok₁ f₁) ∷ fs)))) , refl , refl , ok) = inj₂ (_ ∷ _ , passT f ∷ ∨r₁T l ok₁ f₁ ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (- , tt)) , snd} (f2li {.- , .tt} (pass f)) (f2li (∨r₂ l ok₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (∨r₂ l ok₁ f₁) ∷ fs)))) , refl , refl , ok) = inj₂ (_ ∷ _ , passT f ∷ ∨r₂T l ok₁ f₁ ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {S , p} (f2li {.(irr (S , p)) , q} (⊗r l ok eq f g)) (f' ∷ fs) 
  rewrite irr-eq S p | isIrr-unique S p q =  inj₂ (_ ∷ _ , ⊗rT l ok eq f g ∷ proj₂ (tagF-fs (f' ∷ fs)) , refl , refl , _)
check-focus {.(just (_ ∧ _)) , snd} (f2li {.(irr (just (_ ∧ _) , snd)) , .tt} (∧l₁ f)) (f' ∷ fs) with check-focus  f' fs
... | inj₁ (inj₁ (A , B , f'' ∷ fs' , refl , refl)) = inj₁ (inj₁ (A , B , f ∷ f'' ∷ fs' , refl , refl))
... | inj₁ (inj₂ (inj₁ (A , B , f'' ∷ fs' , refl , refl))) = inj₂ (_ ∷ _ , ∧l₁T f ∷ proj₂ (tagF-fs (f2li-fs (∧l₂-fs (f'' ∷ fs')))) , refl , refl , _)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₁ f)) (f2li (⊗r l ok₁ eq₁ f₁ g) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (⊗r l ok₁ eq₁ f₁ g) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₁T f ∷ ⊗rT l ok₁ eq₁ f₁ g ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₁ f)) (f2li (∧l₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₁ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₁T f ∷ ∧l₁T f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₁ f)) (f2li (∧l₂ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₂ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₁T f ∷ ∧l₂T f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₁ f)) (f2li (∨r₁ l ok₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₁ l ok₁ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₁T f ∷ ∨r₁T l ok₁ f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₁ f)) (f2li (∨r₂ l ok₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₂ l ok₁ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₁T f ∷ ∨r₂T l ok₁ f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(just (_ ∧ _)) , snd} (f2li {.(irr (just (_ ∧ _) , snd)) , .tt} (∧l₂ f)) (f' ∷ fs) with check-focus  f' fs
... | inj₁ (inj₁ (A , B , f'' ∷ fs' , refl , refl)) = inj₂ (_ ∷ _ , ∧l₂T f ∷ proj₂ (tagF-fs (f2li-fs (∧l₁-fs (f'' ∷ fs')))) , refl , refl , _)
... | inj₁ (inj₂ (inj₁ (A , B , f'' ∷ fs' , refl , refl))) = inj₁ (inj₂ (inj₁ (A , B , f ∷ f'' ∷ fs' , refl , refl)))
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₂ f)) (f2li (⊗r l ok₁ eq₁ f₁ g) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (⊗r l ok₁ eq₁ f₁ g) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₂T f ∷ ⊗rT l ok₁ eq₁ f₁ g ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₂ f)) (f2li (∧l₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₁ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₂T f ∷ ∧l₁T f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₂ f)) (f2li (∧l₂ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₂ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₂T f ∷ ∧l₂T f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₂ f)) (f2li (∨r₁ l ok₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₁ l ok₁ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₂T f ∷ ∨r₁T l ok₁ f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {.(irr (just (_ ∧ _) , tt)) , snd} (f2li {.(just (_ ∧ _)) , .tt} (∧l₂ f)) (f2li (∨r₂ l ok₁ f₁) ∷ fs) | inj₂ (_ ∷ _ , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₂ l ok₁ f₁) ∷ fs)))) , refl , refl , ok) = 
  inj₂ (_ ∷ _ , ∧l₂T f ∷ ∨r₂T l ok₁ f₁  ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus {S , p} (f2li {.(irr (S , p)) , q} (∨r₁ l ok f)) (f' ∷ fs) 
  rewrite irr-eq S p | isIrr-unique S p q =  inj₂ (_ ∷ _ , ∨r₁T l ok f ∷ proj₂ (tagF-fs (f' ∷ fs)) , refl , refl , _)
check-focus {S , p} (f2li {.(irr (S , p)) , q} (∨r₂ l ok f)) (f' ∷ fs) 
  rewrite irr-eq S p | isIrr-unique S p q =  inj₂ (_ ∷ _ , ∨r₂T l ok f ∷ proj₂ (tagF-fs (f' ∷ fs)) , refl , refl , _)

isOKC₁-refl : (l : List Tag)
  → (ok ok' : isOKC₁ l)
  → ok ≡ ok'
isOKC₁-refl (R ∷ l) ok ok' = refl
isOKC₁-refl (C₁ ∷ l) ok ok' = isOKC₁-refl l ok ok'
isOKC₁-refl (C₂ ∷ l) ok ok' = refl

isOKC₁-⊥ : {Γ : Cxt} {Φ : List Pos} {A B : Fma}
  → (fs' : All (_∣_⊢li_ (just A) Γ) Φ)
  → (ok : isOKC₁ (mapList (λ r → proj₁ r) (proj₁ (tagF-fs (f2li-fs (∧l₁-fs {B = B} fs'))))))
  → ⊥
isOKC₁-⊥ (px ∷ fs') ok = isOKC₁-⊥ fs' ok

isOKC₂-refl : (l : List Tag)
  → (ok ok' : isOKC₂ l)
  → ok ≡ ok'
isOKC₂-refl (R ∷ l) ok ok' = refl
isOKC₂-refl (C₁ ∷ l) ok ok' = refl
isOKC₂-refl (C₂ ∷ l) ok ok' = isOKC₂-refl l ok ok'

isOKC₂-⊥ : {Γ : Cxt} {Φ : List Pos} {A B : Fma}
  → (fs' : All (_∣_⊢li_ (just B) Γ) Φ)
  → (ok : isOKC₂ (mapList (λ r → proj₁ r) (proj₁ (tagF-fs (f2li-fs (∧l₂-fs {A = A} fs'))))))
  → ⊥
isOKC₂-⊥ (px ∷ fs') ok = isOKC₂-⊥ fs' ok

isOK-refl : (l : List Tag)
  → (ok ok' : isOK l)
  → ok ≡ ok'
isOK-refl (R ∷ l) ok ok' = refl
isOK-refl (C₁ ∷ l) ok ok' = isOKC₁-refl l ok ok'
isOK-refl (C₂ ∷ l) ok ok' = isOKC₂-refl l ok ok'
isOK-refl (P ∷ l) ok ok' = isOK-refl l ok ok'

isOK-⊥ : {Γ : Cxt} {Φ : List Pos} {A : Fma}
  → (fs' : All (_∣_⊢li_ (just A) Γ) Φ)
  → (ok : isOK (mapList (λ r → proj₁ r) (proj₁ (tagF-fs (f2li-fs (pass-fs fs'))))))
  → ⊥
isOK-⊥ (px ∷ fs') ok = isOK-⊥ fs' ok

{-
Given a list of sequents, if we have 
already known the shape of their proofs,
then check-focus on them would return themselves. 
-}

check-focus-ok-ax : {X : At}
  → {Φ : List Pos}
  → (fs : All (_∣_⊢li_ (just (` X)) []) Φ)
  → check-focus (f2li ax) fs
    ≡ inj₂ ((R , (` X , _)) ∷  (proj₁ (tagF-fs fs)) , ax ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-ax [] = refl
check-focus-ok-ax (f ∷ fs) = refl

check-focus-ok-Ir : {Φ : List Pos}
  → (fs : All (_∣_⊢li_ - []) Φ)
  → check-focus (f2li Ir) fs
    ≡ inj₂ ((R , (I , _)) ∷ (proj₁ (tagF-fs fs)) , Ir ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-Ir [] = refl
check-focus-ok-Ir (f ∷ fs) = refl

check-focus-ok-pass : {Γ : Cxt} {A : Fma} {C : Pos}
  → {Φ : List Pos}
  → (f : just A ∣ Γ ⊢li C)
  → (fs : All (_∣_⊢li_ - (A ∷ Γ)) Φ)
  → (ok : isOK (mapList (λ r → proj₁ r) (proj₁ (tagF-fs fs))))
  → check-focus (f2li (pass f)) fs 
    ≡ inj₂ ((P , C) ∷ (proj₁ (tagF-fs fs)) , passT f ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus-ok-pass f (f' ∷ fs) ok with check-focus f' fs
... | inj₁ (inj₂ (inj₂ (A , Γ , f'' ∷ fs' , refl , refl , refl))) = ⊥-elim (isOK-⊥ fs' ok)
check-focus-ok-pass f (f2li (pass f₁) ∷ fs) ok | inj₂ (.(proj₁ (tagF-fs (f2li (pass f₁) ∷ fs))) , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (pass f₁) ∷ fs)))) , refl , refl , ok') 
  rewrite isOK-refl (mapList (λ r → proj₁ r) (proj₁ (tagF-fs fs))) ok ok' = refl
check-focus-ok-pass f (f2li (⊗r l ok₁ eq f₁ g) ∷ fs) ok | inj₂ (.(proj₁ (tagF-fs (f2li (⊗r l ok₁ eq f₁ g) ∷ fs))) , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (⊗r l ok₁ eq f₁ g) ∷ fs)))) , refl , refl , ok') = refl
check-focus-ok-pass f (f2li (∨r₁ l ok₁ f₁) ∷ fs) ok | inj₂ (.(proj₁ (tagF-fs (f2li (∨r₁ l ok₁ f₁) ∷ fs))) , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (∨r₁ l ok₁ f₁) ∷ fs)))) , refl , refl , ok') = refl
check-focus-ok-pass f (f2li (∨r₂ l ok₁ f₁) ∷ fs) ok | inj₂ (.(proj₁ (tagF-fs (f2li (∨r₂ l ok₁ f₁) ∷ fs))) , .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs (f2li (∨r₂ l ok₁ f₁) ∷ fs)))) , refl , refl , ok') = refl

check-focus-ok-∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos}
  → (f : just A ∣ Γ ⊢li C)
  → (fs : All (_∣_⊢li_ (just (A ∧ B)) Γ) Φ)
  → (ok : isOKC₁ (mapList (λ r → proj₁ r) (proj₁ (tagF-fs fs))))
  → check-focus (f2li (∧l₁ f)) fs
    ≡ inj₂ ((C₁ , C) ∷  (proj₁ (tagF-fs fs)) , ∧l₁T f ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus-ok-∧l₁ f (f' ∷ fs) ok with check-focus f' fs
... | inj₁ (inj₁ (A , B , f'' ∷ fs' , refl , refl)) = ⊥-elim (isOKC₁-⊥ fs' ok)
... | inj₁ (inj₂ (inj₁ (A , B , f'' ∷ fs' , refl , refl))) = refl
check-focus-ok-∧l₁ f (f2li (⊗r l ok₂ eq f₁ g) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (⊗r l ok₂ eq f₁ g) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (⊗r l ok₂ eq f₁ g) ∷ fs)))) , refl , refl , ok) = refl 
check-focus-ok-∧l₁ f (f2li (∧l₁ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∧l₁ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₁ f₁) ∷ fs)))) , refl , refl , ok) 
  rewrite isOKC₁-refl (mapList (λ r → proj₁ r) (proj₁ (tagF-fs fs))) ok ok₁ = refl
check-focus-ok-∧l₁ f (f2li (∧l₂ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∧l₂ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₂ f₁) ∷ fs)))) , refl , refl , ok) = refl
check-focus-ok-∧l₁ f (f2li (∨r₁ l ok₂ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∨r₁ l ok₂ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₁ l ok₂ f₁) ∷ fs)))) , refl , refl , ok) = refl
check-focus-ok-∧l₁ f (f2li (∨r₂ l ok₂ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∨r₂ l ok₂ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₂ l ok₂ f₁) ∷ fs)))) , refl , refl , ok) = refl

check-focus-ok-∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos}
  → (f : just B ∣ Γ ⊢li C)
  → (fs : All (_∣_⊢li_ (just (A ∧ B)) Γ) Φ)
  → (ok : isOKC₂ (mapList (λ r → proj₁ r) (proj₁ (tagF-fs fs))))
  → check-focus (f2li (∧l₂ f)) fs
    ≡ inj₂ ((C₂ , C) ∷  (proj₁ (tagF-fs fs)) , ∧l₂T f ∷ proj₂ (tagF-fs fs) , refl , refl , ok)
check-focus-ok-∧l₂ f (f' ∷ fs) ok with check-focus f' fs
... | inj₁ (inj₁ (A , B , f'' ∷ fs' , refl , refl)) = refl
... | inj₁ (inj₂ (inj₁ (A , B , f'' ∷ fs' , refl , refl))) = ⊥-elim (isOKC₂-⊥ fs' ok)
check-focus-ok-∧l₂ f (f2li (⊗r l ok₂ eq f₁ g) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (⊗r l ok₂ eq f₁ g) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (⊗r l ok₂ eq f₁ g) ∷ fs)))) , refl , refl , ok) = refl 
check-focus-ok-∧l₂ f (f2li (∧l₁ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∧l₁ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₁ f₁) ∷ fs)))) , refl , refl , ok) = refl
check-focus-ok-∧l₂ f (f2li (∧l₂ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∧l₂ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∧l₂ f₁) ∷ fs)))) , refl , refl , ok) 
  rewrite isOKC₂-refl (mapList (λ r → proj₁ r) (proj₁ (tagF-fs fs))) ok ok₁ = refl
check-focus-ok-∧l₂ f (f2li (∨r₁ l ok₂ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∨r₁ l ok₂ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₁ l ok₂ f₁) ∷ fs)))) , refl , refl , ok) = refl
check-focus-ok-∧l₂ f (f2li (∨r₂ l ok₂ f₁) ∷ fs) ok₁ | inj₂ (.(proj₁ (tagF-fs (f2li (∨r₂ l ok₂ f₁) ∷ fs))) , .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs (f2li (∨r₂ l ok₂ f₁) ∷ fs)))) , refl , refl , ok) = refl

check-focus-ok-⊗r-atomS : {X : At} {l : List Tag} {Γ Δ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (f : l ∣ ((just (` X)) , tt) ∣ Γ ⊢riT A)
  → (fs : All (_∣_⊢li_ (just (` X)) (Γ ++ Δ)) Φ)
  → (ok : isOK l)
  → (g : - ∣ Δ ⊢ri B)
  → check-focus (f2li (⊗r l ok refl f g)) fs
    ≡ inj₂ ((R , A ⊗ B , _) ∷ (proj₁ (tagF-fs fs)) , ⊗rT l ok refl f g ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-⊗r-atomS f [] ok g = refl
check-focus-ok-⊗r-atomS f (px ∷ fs) ok g = refl

check-focus-ok-⊗r-∧S : {l : List Tag} {Γ Δ : Cxt} {A A' B B' : Fma}
  → {Φ : List Pos}
  → (f : l ∣ ((just (A' ∧ B')) , tt) ∣ Γ ⊢riT A)
  → (fs : All (_∣_⊢li_ (just (A' ∧ B')) (Γ ++ Δ)) Φ)
  → (ok : isOK l)
  → (g : - ∣ Δ ⊢ri B)
  → check-focus (f2li (⊗r l ok refl f g)) fs
    ≡ inj₂ ((R , A ⊗ B , _) ∷ (proj₁ (tagF-fs fs)) , ⊗rT l ok refl f g ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-⊗r-∧S f [] ok g = refl
check-focus-ok-⊗r-∧S f (px ∷ fs) ok g = refl

check-focus-ok-⊗r-emptyS : {l : List Tag} {Γ Δ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (f : l ∣ (- , tt) ∣ Γ ⊢riT A)
  → (fs : All (_∣_⊢li_ - (Γ ++ Δ)) Φ)
  → (ok : isOK l)
  → (g : - ∣ Δ ⊢ri B)
  → check-focus (f2li (⊗r l ok refl f g)) fs
    ≡ inj₂ ((R , A ⊗ B , _) ∷ (proj₁ (tagF-fs fs)) , ⊗rT l ok refl f g ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-⊗r-emptyS f [] ok g = refl
check-focus-ok-⊗r-emptyS f (px ∷ fs) ok g = refl

check-focus-ok-∨r₁-atomS : {X : At} {l : List Tag} {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (f : l ∣ ((just (` X)) , tt) ∣ Γ ⊢riT A)
  → (fs : All (_∣_⊢li_ (just (` X)) Γ) Φ)
  → (ok : isOK l)
  → check-focus (f2li (∨r₁ l ok f)) fs
    ≡ inj₂ ((R , A ∨ B , _) ∷ (proj₁ (tagF-fs fs)) , ∨r₁T l ok f ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-∨r₁-atomS f [] ok = refl
check-focus-ok-∨r₁-atomS f (px ∷ fs) ok = refl

check-focus-ok-∨r₁-∧S : {l : List Tag} {Γ : Cxt} {A A' B B' : Fma}
  → {Φ : List Pos}
  → (f : l ∣ ((just (A' ∧ B')) , tt) ∣ Γ ⊢riT A)
  → (fs : All (_∣_⊢li_ (just (A' ∧ B')) Γ) Φ)
  → (ok : isOK l)
  → check-focus (f2li (∨r₁ l ok f)) fs
    ≡ inj₂ ((R , A ∨ B , _) ∷ (proj₁ (tagF-fs fs)) , ∨r₁T l ok f ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-∨r₁-∧S f [] ok = refl
check-focus-ok-∨r₁-∧S f (px ∷ fs) ok = refl

check-focus-ok-∨r₁-emptyS : {l : List Tag} {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (f : l ∣ (- , tt) ∣ Γ ⊢riT A)
  → (fs : All (_∣_⊢li_ - Γ) Φ)
  → (ok : isOK l)
  → check-focus (f2li (∨r₁ l ok f)) fs
    ≡ inj₂ ((R , A ∨ B , _) ∷ (proj₁ (tagF-fs fs)) , ∨r₁T l ok f ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-∨r₁-emptyS f [] ok = refl
check-focus-ok-∨r₁-emptyS f (px ∷ fs) ok = refl

check-focus-ok-∨r₂-atomS : {X : At} {l : List Tag} {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (f : l ∣ ((just (` X)) , tt) ∣ Γ ⊢riT B)
  → (fs : All (_∣_⊢li_ (just (` X)) Γ) Φ)
  → (ok : isOK l)
  → check-focus (f2li (∨r₂ l ok f)) fs
    ≡ inj₂ ((R , A ∨ B , _) ∷ (proj₁ (tagF-fs fs)) , ∨r₂T l ok f ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-∨r₂-atomS f [] ok = refl
check-focus-ok-∨r₂-atomS f (px ∷ fs) ok = refl

check-focus-ok-∨r₂-∧S : {l : List Tag} {Γ : Cxt} {A A' B B' : Fma}
  → {Φ : List Pos}
  → (f : l ∣ ((just (A' ∧ B')) , tt) ∣ Γ ⊢riT B)
  → (fs : All (_∣_⊢li_ (just (A' ∧ B')) Γ) Φ)
  → (ok : isOK l)
  → check-focus (f2li (∨r₂ l ok f)) fs
    ≡ inj₂ ((R , A ∨ B , _) ∷ (proj₁ (tagF-fs fs)) , ∨r₂T l ok f ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-∨r₂-∧S f [] ok = refl
check-focus-ok-∨r₂-∧S f (px ∷ fs) ok = refl

check-focus-ok-∨r₂-emptyS : {l : List Tag} {Γ : Cxt} {A B : Fma}
  → {Φ : List Pos}
  → (f : l ∣ (- , tt) ∣ Γ ⊢riT B)
  → (fs : All (_∣_⊢li_ - Γ) Φ)
  → (ok : isOK l)
  → check-focus (f2li (∨r₂ l ok f)) fs
    ≡ inj₂ ((R , A ∨ B , _) ∷ (proj₁ (tagF-fs fs)) , ∨r₂T l ok f ∷ proj₂ (tagF-fs fs) , refl , refl , _)
check-focus-ok-∨r₂-emptyS f [] ok = refl
check-focus-ok-∨r₂-emptyS f (px ∷ fs) ok = refl