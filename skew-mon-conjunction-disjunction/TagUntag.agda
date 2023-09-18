{-# OPTIONS --rewriting #-}

module TagUntag where

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

{-
Functions generating lists of tagged sequents
from untagged sequents their properties and 
equalities.
-}

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
untagF-fs (f ∷ fs) refl = untagF f ∷ untagF-fs fs refl

tagF-fs : {S : Irr} {Γ : Cxt} {Φ : List Pos}
  → (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ)
  → Σ (List (Tag × Pos)) λ Ψ → All (match-fT S Γ) Ψ
tagF-fs [] = [] , []
tagF-fs (f2li ax ∷ fs) = (R , _) ∷ proj₁ (tagF-fs fs) , ax ∷ proj₂ (tagF-fs fs)
tagF-fs (f2li Ir ∷ fs) = (R , _) ∷ proj₁ (tagF-fs fs) , Ir ∷ proj₂ (tagF-fs fs)
tagF-fs (f2li (pass f) ∷ fs) = (P , _) ∷ proj₁ (tagF-fs fs) , passT f ∷ proj₂ (tagF-fs fs)
tagF-fs {S , p} (f2li {.(irr (S , p)) , q} (⊗r l ok eq f g) ∷ fs)
  rewrite irr-eq S p | isIrr-unique S p q = (R , _) ∷ proj₁ (tagF-fs fs) , ⊗rT l ok eq f g ∷ proj₂ (tagF-fs fs)
tagF-fs (f2li (∧l₁ f) ∷ fs) = (C₁ , _) ∷ proj₁ (tagF-fs fs) , ∧l₁T f ∷ proj₂ (tagF-fs fs)
tagF-fs (f2li (∧l₂ f) ∷ fs) = (C₂ , _) ∷ proj₁ (tagF-fs fs) , ∧l₂T f ∷ proj₂ (tagF-fs fs)
tagF-fs {S , p} (f2li {.(irr (S , p)) , q} (∨r₁ l {B = B} ok f) ∷ fs) 
  rewrite irr-eq S p | isIrr-unique S p q = (R , _) ∷ proj₁ (tagF-fs fs) , ∨r₁T l {B = B} ok f ∷ proj₂ (tagF-fs fs)
tagF-fs {S , p} (f2li {.(irr (S , p)) , q} (∨r₂ l {A = A} ok f) ∷ fs)
  rewrite irr-eq S p | isIrr-unique S p q = (R , _) ∷ proj₁ (tagF-fs fs) , ∨r₂T l {A = A} ok f ∷ proj₂ (tagF-fs fs)

{-
This equality helps us unitfy List Pos after 
generating tags for a list of sequents.
In particular, in the proofs of genR rules, the type 
SubFmas requires a equality of List Pos.
We could give the equality explicitly with strenthening
the function tagF-fs, but the beauracuracy of equalities 
in Embfocus is annoying.
-}

tagF-fs-tag-eq : {S : Irr} {Γ : Cxt} {Φ : List Pos}
  → (fs : All (λ C → irr S ∣ Γ ⊢li C) Φ)
  → mapList (λ z → proj₂ z) (proj₁ (tagF-fs {S} fs)) ≡ Φ
tagF-fs-tag-eq [] = refl
tagF-fs-tag-eq {.(irr (just (` _) , tt)) , p} (f2li {.(just (` _)) , .tt} ax ∷ fs) = cong (_ ∷_) (tagF-fs-tag-eq fs)
tagF-fs-tag-eq {.(irr (- , tt)) , p} (f2li {.- , .tt} Ir ∷ fs) = cong (_ ∷_) (tagF-fs-tag-eq fs)
tagF-fs-tag-eq {.(irr (- , tt)) , p} (f2li {.- , .tt} (pass f) ∷ fs) = cong (_ ∷_) (tagF-fs-tag-eq fs)
tagF-fs-tag-eq {.(irr (S , q)) , p} (f2li {S , q} (⊗r l ok eq f g) ∷ fs) 
  rewrite irr-eq S p | isIrr-unique S p q = cong (_ ∷_) (tagF-fs-tag-eq fs)
tagF-fs-tag-eq {.(irr (just (_ ∧ _) , tt)) , p} (f2li {.(just (_ ∧ _)) , .tt} (∧l₁ f) ∷ fs) = cong (_ ∷_) (tagF-fs-tag-eq fs)
tagF-fs-tag-eq {.(irr (just (_ ∧ _) , tt)) , p} (f2li {.(just (_ ∧ _)) , .tt} (∧l₂ f) ∷ fs) = cong (_ ∷_) (tagF-fs-tag-eq fs)
tagF-fs-tag-eq {.(irr (S , q)) , p} (f2li {S , q} (∨r₁ l ok f) ∷ fs) 
  rewrite irr-eq S p | isIrr-unique S p q = cong (_ ∷_) (tagF-fs-tag-eq fs)
tagF-fs-tag-eq {.(irr (S , q)) , p} (f2li {S , q} (∨r₂ l ok f) ∷ fs) 
  rewrite irr-eq S p | isIrr-unique S p q = cong (_ ∷_) (tagF-fs-tag-eq fs)
{-# REWRITE tagF-fs-tag-eq #-}

tag-untag : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → {Φ : List (Tag × Pos)}
    → (f : t ∣ S ∣ Γ ⊢fT C)
    → (fs : All (match-fT S Γ) Φ)
    → proj₁ (tagF-fs {S} (f2li (untagF f) ∷ f2li-fs (untagF-fs fs refl))) ≡ (t , C) ∷ Φ
tag-untag ax [] = refl
tag-untag Ir [] = refl
tag-untag (passT f) [] = refl
tag-untag {S = just (` x) , p} (⊗rT l ok eq f g) [] = refl
tag-untag {S = just (x ∧ x₁) , p} (⊗rT l ok eq f g) [] = refl
tag-untag {S = - , p} (⊗rT l ok eq f g) [] = refl
tag-untag (∧l₁T f) [] = refl
tag-untag (∧l₂T f) [] = refl
tag-untag {S = just (` x) , p} (∨r₁T l ok f) [] = refl
tag-untag {S = just (x ∧ x₁) , p} (∨r₁T l ok f) [] = refl
tag-untag {S = - , p} (∨r₁T l ok f) [] = refl
tag-untag {S = just (` x) , p} (∨r₂T l ok f) [] = refl
tag-untag {S = just (x ∧ x₁) , p} (∨r₂T l ok f) [] = refl
tag-untag {S = - , p} (∨r₂T l ok f) [] = refl
tag-untag (ax {X}) (f' ∷ fs) = cong ((R , ` X , _) ∷_) (tag-untag f' fs)
tag-untag Ir (f' ∷ fs) = cong ((R , I , _) ∷_) (tag-untag f' fs)
tag-untag {C = C} (passT f) (f' ∷ fs) = cong ((P , C) ∷_) (tag-untag f' fs)
tag-untag {S = just (` x) , p} (⊗rT l {A = A} {B} ok eq f g) (f' ∷ fs) = cong ((R , A ⊗ B , _) ∷_) (tag-untag f' fs)
tag-untag {S = just (x ∧ x₁) , p} (⊗rT l {A = A} {B} ok eq f g) (f' ∷ fs) = cong ((R , A ⊗ B , _) ∷_) (tag-untag f' fs)
tag-untag {S = - , p} (⊗rT l {A = A} {B} ok eq f g) (f' ∷ fs) = cong ((R , A ⊗ B , _) ∷_) (tag-untag f' fs)
tag-untag {C = C} (∧l₁T f) (f' ∷ fs) = cong ((C₁ , C) ∷_) (tag-untag f' fs)
tag-untag {C = C} (∧l₂T f) (f' ∷ fs) = cong ((C₂ , C) ∷_) (tag-untag f' fs)
tag-untag {S = just (` x) , p} (∨r₁T l {A = A} {B} ok f) (f' ∷ fs) = cong ((R , A ∨ B , _) ∷_) (tag-untag f' fs)
tag-untag {S = just (x ∧ x₁) , p} (∨r₁T l {A = A} {B} ok f) (f' ∷ fs) = cong ((R , A ∨ B , _) ∷_) (tag-untag f' fs)
tag-untag {S = - , p} (∨r₁T l {A = A} {B} ok f) (f' ∷ fs) = cong ((R , A ∨ B , _) ∷_) (tag-untag f' fs)
tag-untag {S = just (` x) , p} (∨r₂T l {A = A} {B} ok f) (f' ∷ fs) = cong ((R , A ∨ B , _) ∷_) (tag-untag f' fs)
tag-untag {S = just (x ∧ x₁) , p} (∨r₂T l {A = A} {B} ok f) (f' ∷ fs) = cong ((R , A ∨ B , _) ∷_) (tag-untag f' fs)
tag-untag {S = - , p} (∨r₂T l {A = A} {B} ok f) (f' ∷ fs) = cong ((R , A ∨ B , _) ∷_) (tag-untag f' fs)
{-# REWRITE tag-untag #-}

tagF-fs-TagPos-eq : {S : Irr} {Γ : Cxt}
  → {Φ : List (Tag × Pos)}
  → (fs : All (match-fT S Γ) Φ)
  → (proj₁ (tagF-fs {S} (f2li-fs (untagF-fs fs refl)))) ≡ Φ
tagF-fs-TagPos-eq [] = refl
tagF-fs-TagPos-eq (ax {X} ∷ fs) = cong ((R , ` X , _) ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq (Ir ∷ fs) = cong ((R , I , _) ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq (passT f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq {just (` x) , p} (⊗rT l ok eq f g ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq {just (x ∧ x₁) , p} (⊗rT l ok eq f g ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq { - , p} (⊗rT l ok eq f g ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq (∧l₁T f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq (∧l₂T f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq {just (` x) , p} (∨r₁T l ok f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq {just (x ∧ x₁) , p} (∨r₁T l ok f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq { - , p} (∨r₁T l ok f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs) 
tagF-fs-TagPos-eq {just (` x) , p} (∨r₂T l ok f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq {just (x ∧ x₁) , p} (∨r₂T l ok f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs)
tagF-fs-TagPos-eq { - , p} (∨r₂T l ok f ∷ fs) = cong (_ ∷_) (tagF-fs-TagPos-eq fs) 
{-# REWRITE tagF-fs-TagPos-eq #-}

tagF-fs-TagPosPos-eq : {S : Irr} {Γ : Cxt}
  → {Φ : List (Tag × Pos)}
  → (fs : All (match-fT S Γ) Φ)
  → mapList proj₂ (proj₁ (tagF-fs {S} (f2li-fs (untagF-fs fs refl)))) ≡ mapList proj₂ Φ
tagF-fs-TagPosPos-eq fs = cong (λ x → mapList proj₂ x) (tagF-fs-TagPos-eq fs)

-- {-# REWRITE tagF-fs-TagPosPos-eq #-}


tag-untag-fs₀ : {S : Irr} {Γ : Cxt}
    → {Φ : List (Tag × Pos)}
    → (fs : All (match-fT S Γ) Φ)
    → proj₂ (tagF-fs (f2li-fs (untagF-fs fs refl))) ≡ fs
tag-untag-fs₀ [] = refl
tag-untag-fs₀ (ax ∷ fs) = cong (ax ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ (Ir ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ (passT f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ {just (` x) , p} (⊗rT l ok eq f g ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ {just (x ∧ x₁) , p} (⊗rT l ok eq f g ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ { - , p} (⊗rT l ok eq f g ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ (∧l₁T f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ (∧l₂T f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ {just (` x) , p} (∨r₁T l ok f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ {just (x ∧ x₁) , p} (∨r₁T l ok f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ { - , p} (∨r₁T l ok f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ {just (` x) , p} (∨r₂T l ok f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ {just (x ∧ x₁) , p} (∨r₂T l ok f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
tag-untag-fs₀ { - , p} (∨r₂T l ok f ∷ fs) = cong (_ ∷_) (tag-untag-fs₀ fs)
{-# REWRITE tag-untag-fs₀ #-}

tag-untag-fs₁ : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → {Φ : List (Tag × Pos)}
    → (f : t ∣ S ∣ Γ ⊢fT C)
    → (fs : All (match-fT S Γ) Φ)
    → proj₂ (tagF-fs (f2li (untagF f) ∷ f2li-fs (untagF-fs fs refl))) ≡ f ∷ fs
tag-untag-fs₁ ax [] = refl
tag-untag-fs₁ Ir [] = refl
tag-untag-fs₁ (passT f) [] = refl
tag-untag-fs₁ {S = just (` x) , p} (⊗rT l ok eq f g) [] = refl
tag-untag-fs₁ {S = just (x ∧ x₁) , p} (⊗rT l ok eq f g) [] = refl
tag-untag-fs₁ {S = - , p} (⊗rT l ok eq f g) [] = refl
tag-untag-fs₁ (∧l₁T f) [] = refl
tag-untag-fs₁ (∧l₂T f) [] = refl
tag-untag-fs₁ {S = just (` x) , p} (∨r₁T l ok f) [] = refl
tag-untag-fs₁ {S = just (x ∧ x₁) , p} (∨r₁T l ok f) [] = refl
tag-untag-fs₁ {S = - , p} (∨r₁T l ok f) [] = refl
tag-untag-fs₁ {S = just (` x) , p} (∨r₂T l ok f) [] = refl
tag-untag-fs₁ {S = just (x ∧ x₁) , p} (∨r₂T l ok f) [] = refl
tag-untag-fs₁ {S = - , p} (∨r₂T l ok f) [] = refl
tag-untag-fs₁ (ax {X}) (f' ∷ fs) = cong (ax ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ Ir (f' ∷ fs) = cong (Ir ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {C = C} (passT f) (f' ∷ fs) = cong (passT f ∷_) (tag-untag-fs₁ f' fs) 
tag-untag-fs₁ {S = just (` x) , p} (⊗rT l {A = A} {B} ok eq f g) (f' ∷ fs) = cong (⊗rT l {A = A} {B} ok eq f g ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = just (x ∧ x₁) , p} (⊗rT l {A = A} {B} ok eq f g) (f' ∷ fs) = cong (⊗rT l {A = A} {B} ok eq f g ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = - , p} (⊗rT l {A = A} {B} ok eq f g) (f' ∷ fs) = cong (⊗rT l {A = A} {B} ok eq f g ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {C = C} (∧l₁T f) (f' ∷ fs) = cong (∧l₁T f ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {C = C} (∧l₂T f) (f' ∷ fs) = cong (∧l₂T f ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = just (` x) , p} (∨r₁T l {A = A} {B} ok f) (f' ∷ fs) = cong (∨r₁T l ok f ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = just (x ∧ x₁) , p} (∨r₁T l {A = A} {B} ok f) (f' ∷ fs) = cong (∨r₁T l ok f ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = - , p} (∨r₁T l {A = A} {B} ok f) (f' ∷ fs) = cong (∨r₁T l ok f ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = just (` x) , p} (∨r₂T l {A = A} {B} ok f) (f' ∷ fs) = cong (∨r₂T l ok f ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = just (x ∧ x₁) , p} (∨r₂T l {A = A} {B} ok f) (f' ∷ fs) = cong (∨r₂T l ok f ∷_) (tag-untag-fs₁ f' fs)
tag-untag-fs₁ {S = - , p} (∨r₂T l {A = A} {B} ok f) (f' ∷ fs) = cong (∨r₂T l ok f ∷_) (tag-untag-fs₁ f' fs)
{-# REWRITE tag-untag-fs₁ #-}

untag-tag : {S : Irr} {Γ : Cxt} 
  → {Φ : List (Tag × Pos)}
  → (fs : All (match-fT S Γ) Φ)
  → Σ (List Pos) λ Ψ → Σ (All (λ C → irr S ∣ Γ ⊢li C) Ψ) λ fs' 
    → Σ (proj₁ (tagF-fs {S} fs') ≡ Φ) λ eq → fs ≡ subst (λ x → All (match-fT S Γ) x) eq (proj₂ (tagF-fs {S} fs'))
untag-tag [] = [] , [] , refl , refl
untag-tag (f ∷ fs) with untag-tag fs
untag-tag (ax {X} ∷ .(subst (All (match-fT (just (` X) , tt) [])) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (` X , _) ∷ Ψ , f2li ax ∷ fs' , refl , refl
untag-tag (Ir ∷ .(subst (All (match-fT (- , tt) [])) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (I , _) ∷ Ψ , f2li Ir ∷ fs' , refl , refl
untag-tag (passT {C = C} f ∷ .(subst (All (match-fT (- , tt) (_ ∷ _))) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  C ∷ Ψ , f2li (pass f) ∷ fs' , refl , refl
untag-tag {just (` x) , tt} (⊗rT l {A = A} {B} ok eq f g ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (A ⊗ B , _) ∷ Ψ , f2li (⊗r l ok eq f g) ∷ fs' , refl , refl
untag-tag {just (x ∧ x₁) , tt} (⊗rT l {A = A} {B} ok eq f g ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (A ⊗ B , _) ∷ Ψ , f2li (⊗r l ok eq f g) ∷ fs' , refl , refl
untag-tag { - , tt} (⊗rT l {A = A} {B} ok eq f g ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl =
  (A ⊗ B , _) ∷ Ψ , f2li (⊗r l ok eq f g) ∷ fs' , refl , refl
untag-tag (∧l₁T {C = C} f ∷ .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  C ∷ Ψ , f2li (∧l₁ f) ∷ fs' , refl , refl
untag-tag (∧l₂T {C = C} f ∷ .(subst (All (match-fT (just (_ ∧ _) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  C ∷ Ψ , f2li (∧l₂ f) ∷ fs' , refl , refl
untag-tag {just (` x) , tt} (∨r₁T l {A = A} {B} ok f ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (A ∨ B , _) ∷ Ψ , f2li (∨r₁ l ok f) ∷ fs' , refl , refl
untag-tag {just (x ∧ x₁) , tt} (∨r₁T l {A = A} {B} ok f ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (A ∨ B , _) ∷ Ψ , f2li (∨r₁ l ok f) ∷ fs' , refl , refl
untag-tag { - , tt} (∨r₁T l {A = A} {B} ok f ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = (A ∨ B , _) ∷ Ψ , f2li (∨r₁ l ok f) ∷ fs' , refl , refl
untag-tag {just (` x) , tt} (∨r₂T l {A = A} {B} ok f ∷ .(subst (All (match-fT (just (` x) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (A ∨ B , _) ∷ Ψ , f2li (∨r₂ l ok f) ∷ fs' , refl , refl
untag-tag {just (x ∧ x₁) , tt} (∨r₂T l {A = A} {B} ok f ∷ .(subst (All (match-fT (just (x ∧ x₁) , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (A ∨ B , _) ∷ Ψ , f2li (∨r₂ l ok f) ∷ fs' , refl , refl
untag-tag { - , tt} (∨r₂T l {A = A} {B} ok f ∷ .(subst (All (match-fT (- , tt) _)) refl (proj₂ (tagF-fs fs')))) | Ψ , fs' , refl , refl = 
  (A ∨ B , _) ∷ Ψ , f2li (∨r₂ l ok f) ∷ fs' , refl , refl

proj₁tagF-fs-All++ : {S : Irr} {Γ : Cxt}
  → {Φ1 Φ2 : List Pos}
  → (fs1 : All (_∣_⊢li_ (irr S) Γ) Φ1)
  → (fs2 : All (_∣_⊢li_ (irr S) Γ) Φ2)
  →  proj₁ (tagF-fs {S} (All++ fs1 fs2)) ≡ proj₁ (tagF-fs {S} fs1) ++ proj₁ (tagF-fs {S} fs2)
proj₁tagF-fs-All++ [] [] = refl
proj₁tagF-fs-All++ [] (px ∷ fs2) = refl
proj₁tagF-fs-All++ {.(just (` _)) , snd} (f2li {.(irr (just (` _) , snd)) , .tt} ax ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.- , snd} (f2li {.(irr (- , snd)) , .tt} Ir ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.- , snd} (f2li {.(irr (- , snd)) , .tt} (pass f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (just (` x) , snd)) , snd₁} (f2li {just (` x) , snd} (⊗r l ok eq f g) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (just (x ∧ x₁) , snd)) , snd₁} (f2li {just (x ∧ x₁) , snd} (⊗r l ok eq f g) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (- , snd)) , snd₁} (f2li { - , snd} (⊗r l ok eq f g) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(just (_ ∧ _)) , snd} (f2li {.(irr (just (_ ∧ _) , snd)) , .tt} (∧l₁ f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(just (_ ∧ _)) , snd} (f2li {.(irr (just (_ ∧ _) , snd)) , .tt} (∧l₂ f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (just (` x) , snd)) , snd₁} (f2li {just (` x) , snd} (∨r₁ l ok f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (just (x ∧ x₁) , snd)) , snd₁} (f2li {just (x ∧ x₁) , snd} (∨r₁ l ok f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (- , snd)) , snd₁} (f2li { - , snd} (∨r₁ l ok f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (just (` x) , snd)) , snd₁} (f2li {just (` x) , snd} (∨r₂ l ok f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (just (x ∧ x₁) , snd)) , snd₁} (f2li {just (x ∧ x₁) , snd} (∨r₂ l ok f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
proj₁tagF-fs-All++ {.(irr (- , snd)) , snd₁} (f2li { - , snd} (∨r₂ l ok f) ∷ fs1) fs2 = cong (_ ∷_) (proj₁tagF-fs-All++ fs1 fs2)
{-# REWRITE proj₁tagF-fs-All++ #-}

tagF-fs-All++ : {S : Irr} {Γ : Cxt}
  → {Φ1 Φ2 : List Pos}
  → (fs1 : All (_∣_⊢li_ (irr S) Γ) Φ1)
  → (fs2 : All (_∣_⊢li_ (irr S) Γ) Φ2)
  → (proj₂ (tagF-fs {S} (All++ fs1 fs2))) ≡ All++ (proj₂ (tagF-fs {S} fs1)) (proj₂ (tagF-fs {S} fs2))
tagF-fs-All++ [] [] = refl
tagF-fs-All++ [] (f ∷ fs2) = refl
tagF-fs-All++ {.(just (` _)) , snd} (f2li {.(irr (just (` _) , snd)) , .tt} ax ∷ fs1) fs2 = cong (ax ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.- , snd} (f2li {.(irr (- , snd)) , .tt} Ir ∷ fs1) fs2 = cong (Ir ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.- , snd} (f2li {.(irr (- , snd)) , .tt} (pass f) ∷ fs1) fs2 = cong (passT f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (just (` x) , snd)) , snd₁} (f2li {just (` x) , snd} (⊗r l ok eq f g) ∷ fs1) fs2 = cong (⊗rT l ok eq f g ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (just (x ∧ x₁) , snd)) , snd₁} (f2li {just (x ∧ x₁) , snd} (⊗r l ok eq f g) ∷ fs1) fs2 = cong (⊗rT l ok eq f g ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (- , snd)) , snd₁} (f2li { - , snd} (⊗r l ok eq f g) ∷ fs1) fs2 = cong (⊗rT l ok eq f g ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(just (_ ∧ _)) , snd} (f2li {.(irr (just (_ ∧ _) , snd)) , .tt} (∧l₁ f) ∷ fs1) fs2 = cong (∧l₁T f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(just (_ ∧ _)) , snd} (f2li {.(irr (just (_ ∧ _) , snd)) , .tt} (∧l₂ f) ∷ fs1) fs2 = cong (∧l₂T f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (just (` x) , snd)) , snd₁} (f2li {just (` x) , snd} (∨r₁ l ok f) ∷ fs1) fs2 = cong (∨r₁T l ok f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (just (x ∧ x₁) , snd)) , snd₁} (f2li {just (x ∧ x₁) , snd} (∨r₁ l ok f) ∷ fs1) fs2 = cong (∨r₁T l ok f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (- , snd)) , snd₁} (f2li { - , snd} (∨r₁ l ok f) ∷ fs1) fs2 = cong (∨r₁T l ok f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (just (` x) , snd)) , snd₁} (f2li {just (` x) , snd} (∨r₂ l ok f) ∷ fs1) fs2 = cong (∨r₂T l ok f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (just (x ∧ x₁) , snd)) , snd₁} (f2li {just (x ∧ x₁) , snd} (∨r₂ l ok f) ∷ fs1) fs2 = cong (∨r₂T l ok f ∷_) (tagF-fs-All++ fs1 fs2)
tagF-fs-All++ {.(irr (- , snd)) , snd₁} (f2li { - , snd} (∨r₂ l ok f) ∷ fs1) fs2 = cong (∨r₂T l ok f ∷_) (tagF-fs-All++ fs1 fs2)