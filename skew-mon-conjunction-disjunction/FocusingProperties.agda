{-# OPTIONS --rewriting #-}

module FocusingProperties where

open import Data.List renaming (map to mapList)
open import Data.List.Relation.Unary.All
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

fsDist-white : {S : Stp} {Γ : Cxt} {Θ : List Pos}
  → (Θ₁ Θ₂ : List Pos) (fs : All (λ C → S ∣ Γ ⊢li C) Θ) (eq : Θ₁ ++ Θ₂ ≡ Θ)
  → Σ (All (λ C → S ∣ Γ ⊢li C) Θ₁) λ fs1 → Σ (All (λ C → S ∣ Γ ⊢li C) Θ₂) λ fs2 → fs ≡ subst (λ x → All (λ C → S ∣ Γ ⊢li C) x) eq (All++ fs1 fs2)
fsDist-white [] [] [] refl = [] , [] , refl
fsDist-white [] .(_ ∷ _) (f ∷ fs) refl = [] , _ ∷ _ , refl
fsDist-white (x ∷ Θ₁) Θ₂ (f ∷ fs) eq with fsDist-white Θ₁ Θ₂ fs (proj₂ (inj∷ eq))
fsDist-white (x ∷ Θ₁) Θ₂ (f ∷ .(subst (All (_∣_⊢li_ _ _)) refl (All++ fs1 fs2))) refl | fs1 , fs2 , refl = f ∷ fs1 , fs2 , refl

fsDist-white-refl : {S : Stp} {Γ : Cxt}
  → {Φ Ψ : List Pos}
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (gs : All (λ C → S ∣ Γ ⊢li C) Ψ)
  → fsDist-white Φ Ψ (All++ fs gs) refl ≡ (fs , gs , refl)
fsDist-white-refl [] [] = refl
fsDist-white-refl [] (g ∷ gs) = refl
fsDist-white-refl (f ∷ fs) gs rewrite fsDist-white-refl fs gs = refl
{-# REWRITE fsDist-white-refl #-}

∧r* : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Pos} 
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas Φ A)
  → S ∣ Γ ⊢ri A
∧r* fs (conj {Φ} {Ψ} SF1 SF2) with fsDist-white Φ Ψ fs refl
... | fs1 , fs2 , refl = ∧r (∧r* fs1 SF1) (∧r* fs2 SF2)
∧r* (f ∷ []) stop = li2ri f

fsDist : {S : Irr} {Γ : Cxt} {Θ : List (Tag × Pos)}
  → (Φ Ψ : List Pos) (fs : All (match-fT S Γ) Θ) (eq : Φ ++ Ψ ≡ mapList (λ x → proj₂ x) Θ)
  → Σ (List (Tag × Pos)) λ Θ₁ → Σ (List (Tag × Pos)) λ Θ₂ 
    → Σ (All (match-fT S Γ) Θ₁) λ fs1 → Σ (All (match-fT S Γ) Θ₂) λ fs2 →  Σ (Θ₁ ++ Θ₂ ≡ Θ) λ eq1 → Φ ≡ mapList (λ x → proj₂ x) Θ₁ × Ψ ≡ mapList (λ x → proj₂ x) Θ₂
      × fs ≡ subst (λ x → All (match-fT S Γ) x) eq1 (All++ fs1 fs2)
fsDist [] [] [] refl = [] , [] , [] , [] , refl , refl , refl , refl
fsDist [] (A ∷ Ψ) (f ∷ fs) refl = [] , _ ∷ _ , [] , f ∷ fs , refl , refl , refl , refl
fsDist (x ∷ Φ) Ψ (f ∷ fs) eq with fsDist Φ Ψ fs (proj₂ (inj∷ eq))
fsDist (._ ∷ .(mapList (λ x → proj₂ x) Θ₁)) .(mapList (λ x → proj₂ x) Θ₂) (f ∷ fs) refl | Θ₁ , Θ₂ , fs1 , fs2 , refl , refl , refl , refl = 
  _ ∷ Θ₁ , Θ₂ , f ∷ fs1 , fs2 , refl , refl , refl , refl

fsDist-refl : {S : Irr} {Γ : Cxt}
  → {Φ Ψ : List (Tag × Pos)}
  → (fs : All (match-fT S Γ) Φ)
  → (gs : All (match-fT S Γ) Ψ)
  → fsDist (mapList (λ r → proj₂ r) Φ) (mapList (λ r → proj₂ r) Ψ) (All++ fs gs) refl ≡ (Φ , Ψ , fs , gs , refl , refl , refl , refl)
fsDist-refl [] [] = refl
fsDist-refl [] (g ∷ gs) = refl
fsDist-refl (f ∷ fs) gs rewrite fsDist-refl fs gs = refl
{-# REWRITE fsDist-refl #-}

∧rT* : {S : Irr} {Γ : Cxt} {A : Fma}
  → {Θ : List (Tag × Pos)} {Φ : List Pos}
  → (fs : All (match-fT S Γ) Θ)
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → proj₂ x) Θ)
  → (mapList (λ x → proj₁ x) Θ) ∣ S ∣ Γ ⊢riT A
∧rT* fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist Φ Ψ fs eq
∧rT* fs (conj {.(mapList (λ x → proj₂ x) Θ₁)} {.(mapList (λ x → proj₂ x) Θ₂)} SF1 SF2) refl | Θ₁ , Θ₂ , fs1 , fs2 , refl , refl , refl , refl = 
  ∧rT (∧rT* fs1 SF1 refl) (∧rT* fs2 SF2 refl)
∧rT* (f ∷ []) stop refl = f2riT f

gen⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos}
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas (C ∷ Φ) A)
  → - ∣ Δ ⊢ri B
  → S ∣ Γ ++ Δ ⊢li (A ⊗ B , _)
gen⊗r-li (⊗l f) fs SF g = ⊗l (gen⊗r-li f (⊗l-inv-fs fs) SF g)
gen⊗r-li (Il f) fs SF g = Il (gen⊗r-li f (Il-inv-fs fs) SF g)
gen⊗r-li (∨l f f') fs SF g = ∨l (gen⊗r-li f (∨l-inv-fs₁ fs) SF g) (gen⊗r-li f' (∨l-inv-fs₂ fs) SF g)
gen⊗r-li (f2li {S} f) fs SF g  with check-focus {S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) =  f2li (∧l₁ (gen⊗r-li f' fs' SF g))
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) =  f2li (∧l₂ (gen⊗r-li f' fs' SF g))
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = f2li (pass (gen⊗r-li f' fs' SF g))
... | inj₂ (.(proj₁ (tagF-fs (f2li f ∷ fs))) , .(subst (All (match-fT S _)) refl (proj₂ (tagF-fs (f2li f ∷ fs)))) , refl , refl , ok) = 
  f2li (⊗r (mapList proj₁ (proj₁ (tagF-fs (f2li f ∷ fs)))) ok refl (∧rT* (proj₂ (tagF-fs (f2li f ∷ fs))) SF refl) g)
  
gen∨r₁-li : {S : Stp} {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos} 
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas (C ∷ Φ) A)
  → S ∣ Γ ⊢li (A ∨ B , _)
gen∨r₁-li (⊗l f) fs SF = ⊗l (gen∨r₁-li f (⊗l-inv-fs fs) SF)
gen∨r₁-li (Il f) fs SF = Il (gen∨r₁-li f (Il-inv-fs fs) SF)
gen∨r₁-li (∨l f f') fs SF = ∨l (gen∨r₁-li f (∨l-inv-fs₁ fs) SF) (gen∨r₁-li f' (∨l-inv-fs₂ fs) SF)
gen∨r₁-li (f2li {S = S} f) fs SF with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = f2li (∧l₁ (gen∨r₁-li f' fs' SF))
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = f2li (∧l₂ (gen∨r₁-li f' fs' SF))
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = f2li (pass (gen∨r₁-li f' fs' SF))
... | inj₂ (.(proj₁ (tagF-fs (f2li f ∷ fs))) , .(subst (All (match-fT S _)) refl (proj₂ (tagF-fs (f2li f ∷ fs)))) , refl , refl , ok) = 
  f2li (∨r₁ (mapList proj₁ (proj₁ (tagF-fs (f2li f ∷ fs)))) ok (∧rT* (proj₂ (tagF-fs (f2li f ∷ fs))) SF refl))

gen∨r₂-li : {S : Stp} {Γ : Cxt} {A B : Fma} {C : Pos}
  → {Φ : List Pos} 
  → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas (C ∷ Φ) B)
  → S ∣ Γ ⊢li (A ∨ B , _)
gen∨r₂-li (⊗l f) fs SF = ⊗l (gen∨r₂-li f (⊗l-inv-fs fs) SF)
gen∨r₂-li (Il f) fs SF = Il (gen∨r₂-li f (Il-inv-fs fs) SF)
gen∨r₂-li (∨l f f') fs SF = ∨l (gen∨r₂-li f (∨l-inv-fs₁ fs) SF) (gen∨r₂-li f' (∨l-inv-fs₂ fs) SF)
gen∨r₂-li (f2li {S = S} f) fs SF with check-focus {S = S} (f2li f) fs
... | inj₁ (inj₁ (A , B , f' ∷ fs' , refl , refl)) = f2li (∧l₁ (gen∨r₂-li f' fs' SF))
... | inj₁ (inj₂ (inj₁ (A , B , f' ∷ fs' , refl , refl))) = f2li (∧l₂ (gen∨r₂-li f' fs' SF))
... | inj₁ (inj₂ (inj₂ (A , Γ , f' ∷ fs' , refl , refl , refl))) = f2li (pass (gen∨r₂-li f' fs' SF))
... | inj₂ (.(proj₁ (tagF-fs (f2li f ∷ fs))) , .(subst (All (match-fT S _)) refl (proj₂ (tagF-fs (f2li f ∷ fs)))) , refl , refl , ok) = 
  f2li (∨r₂ (mapList proj₁ (proj₁ (tagF-fs (f2li f ∷ fs)))) ok (∧rT* (proj₂ (tagF-fs (f2li f ∷ fs))) SF refl))

{-
Phase ri is invertible. 
 -}

f2fs : {S : Stp} {Γ : Cxt} {A : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → Σ (List Pos) λ Φ → Σ (All (λ C → S ∣ Γ ⊢li C) Φ) λ fs → Σ (SubFmas Φ A) λ SF → f ≡ ∧r* fs SF
f2fs (∧r f g) with f2fs f | f2fs g
... | Φ1 , fs1 , SF1 , refl | Φ2 , fs2 , SF2 , refl = 
   Φ1 ++ Φ2 , All++ fs1 fs2 , conj SF1 SF2 , refl
f2fs (li2ri {C = C} f) = C ∷ [] , f ∷ [] , stop , refl

f2fs-refl : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ Ψ : List Pos}
  -- → (f : S ∣ Γ ⊢li C)
  → (fs : All (λ C → S ∣ Γ ⊢li C) Φ)
  → (SF : SubFmas Ψ A)
  → (eq : Ψ ≡ Φ)
  → f2fs (∧r* fs (subst (λ x → SubFmas x A) eq SF)) ≡ (Φ , fs , (subst (λ x → SubFmas x A) eq SF) , refl)
f2fs-refl fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
f2fs-refl .(subst (All (_∣_⊢li_ _ _)) refl (All++ fs1 fs2)) (conj {Φ} {Ψ} SF1 SF2) refl | fs1 , fs2 , refl 
  rewrite f2fs-refl fs1 SF1 refl | f2fs-refl fs2 SF2 refl = refl
f2fs-refl (f ∷ []) stop refl = refl

{-
Phase riT is also invertible.
-}

f2fsT : {l : List Tag} {S : Irr} {Γ : Cxt} {A : Fma}
  → (f : l ∣ S ∣ Γ ⊢riT A)
  → Σ (List (Tag × Pos)) λ Φ → Σ (All (match-fT S Γ) Φ) λ fs → Σ (List Pos) λ Ψ → Σ (Ψ ≡ mapList proj₂ Φ) λ eq1 → 
    Σ (SubFmas Ψ A) λ SF → Σ (mapList proj₁ Φ ≡ l) λ eq2 → f ≡ subst (λ x → x ∣ S ∣ Γ ⊢riT A) eq2 (∧rT* fs SF eq1)
f2fsT (∧rT f g) with f2fsT f | f2fsT g
... | Φ1 , fs1 , .(mapList (λ r → proj₂ r) Φ1) , refl , SF1 , refl , refl | Φ2 , fs2 , .(mapList (λ r → proj₂ r) Φ2) , refl , SF2 , refl , refl = Φ1 ++ Φ2 , All++ fs1 fs2 , (mapList (λ r → proj₂ r) Φ1) ++ (mapList (λ r → proj₂ r) Φ2) , refl , conj SF1 SF2 , refl , refl
f2fsT (f2riT {t} {C = C} f) = (t , C) ∷ [] , f ∷ [] , C ∷ [] , refl , stop , refl , refl

{-
All rules are admissible in phase ri.
-}

⊗r-ri : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → (g : - ∣ Δ ⊢ri B)
  → S ∣ Γ ++ Δ ⊢ri A ⊗ B
⊗r-ri f g with f2fs f
... | .[] , [] , SF , refl = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl = li2ri (gen⊗r-li f fs SF g)

∨r₁-ri : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → S ∣ Γ ⊢ri A ∨ B
∨r₁-ri f with f2fs f
... | .[] , [] , SF , refl = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl = li2ri (gen∨r₁-li f fs SF)

∨r₂-ri : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri B)
  → S ∣ Γ ⊢ri A ∨ B
∨r₂-ri f with f2fs f
... | .[] , [] , SF , refl = ⊥-elim (SubFmas[]-⊥ SF refl)
... | .(_ ∷ _) , f ∷ fs , SF , refl = li2ri (gen∨r₂-li f fs SF)

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
            