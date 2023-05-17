{-# OPTIONS --rewriting #-}

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

mapList++ : {A B : Set} {f : A → B} (xs ys : List A) 
  → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
mapList++ [] ys = refl
mapList++ {f = f} (x ∷ xs) ys = cong (f x ∷_) (mapList++ xs ys)
{-# REWRITE mapList++ #-}

data Tag : Set where
  R : Tag
  C₁ : Tag
  C₂ : Tag
  P : Tag

-- functions checking validity of a list of tags
isOKC₁ : List Tag → Set
isOKC₁ (C₂ ∷ l) = ⊤
isOKC₁ (R ∷ l) = ⊤
isOKC₁ (C₁ ∷ l) = isOKC₁ l
isOKC₁ _ = ⊥

isOKC₂ : List Tag → Set
isOKC₂ (C₁ ∷ l) = ⊤
isOKC₂ (R ∷ l) = ⊤
isOKC₂ (C₂ ∷ l) = isOKC₂ l
isOKC₂ _ = ⊥

isOK : List Tag → Set
isOK [] = ⊥
isOK (R ∷ l) = ⊤
isOK (C₁ ∷ l) = isOKC₁ l
isOK (C₂ ∷ l) = isOKC₂ l
isOK (P ∷ l) = isOK l 

-- the focused calculus has three phases
-- ri = right invertible
data _∣_⊢ri_ : Stp → Cxt → Fma → Set
data _∣_∣_⊢riT_ : (l : List Tag) → Irr → Cxt → Fma → Set

-- l = left invertible 
data _∣_⊢li_ : Stp → Cxt → Pos → Set

-- f = focusing
data _∣_⊢f_ : Irr → Cxt → Pos → Set
data _∣_∣_⊢fT_ : (t : Tag) → Irr → Cxt → Pos → Set

data _∣_⊢ri_ where
  ∧r : {S : Stp} {Γ : Cxt} {A B : Fma}
    → (f : S ∣ Γ ⊢ri A) (g : S ∣ Γ ⊢ri B)
    ---------------------------------------
    →          S ∣ Γ ⊢ri A ∧ B
  li2ri : {S : Stp} {Γ : Cxt} {C : Pos}
    → (f : S ∣ Γ ⊢li C)
    ------------------------
    →      S ∣ Γ ⊢ri pos C

data _∣_∣_⊢riT_ where
  ∧rT : {l l' : List Tag} {S : Irr} {Γ : Cxt} {A B : Fma}
    → (f : l ∣ S ∣ Γ ⊢riT A) (g : l' ∣ S ∣ Γ ⊢riT B)
    ---------------------------------------------------------
    →             (l ++ l') ∣ S ∣ Γ ⊢riT A ∧ B
  f2riT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : t ∣ S ∣ Γ ⊢fT C)
    ------------------------
    →    [ t ] ∣ S ∣ Γ ⊢riT pos C

data _∣_⊢li_ where
  ⊗l : {Γ : Cxt} {A B : Fma} {C : Pos}
       (f : just A ∣ B ∷ Γ ⊢li C) →
    -------------------------------------
          just (A ⊗ B) ∣ Γ ⊢li C
  Il : {Γ : Cxt} {C : Pos}
       (f : - ∣ Γ ⊢li C) →
    -------------------------
            just I ∣ Γ ⊢li C 
  f2li : {S : Irr} {Γ : Cxt} {C : Pos}
        (f : S ∣ Γ ⊢f C) →
        --------------------------
             irr S ∣ Γ ⊢li C

data _∣_⊢f_ where
  ax : {X : At} → 
       (just (` X) , _) ∣ [] ⊢f (` X , _)
  Ir : (- , _) ∣ [] ⊢f (I , _)
  pass : {Γ : Cxt} {A : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) → 
        --------------------------------
            (- , _) ∣ A ∷ Γ ⊢f C
  ⊗r : (l : List Tag) {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma} →
         (ok : isOK l) (eq : Γ' ≡ Γ ++ Δ) →  
         (f : l ∣ S ∣ Γ ⊢riT A) (g : - ∣ Δ  ⊢ri B) → 
         -----------------------------------
              S ∣ Γ' ⊢f (A ⊗ B , _)
  ∧l₁ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) → 
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C
  ∧l₂ : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ⊢li C) → 
        --------------------------------
             (just (A ∧ B) , _) ∣ Γ ⊢f C

data _∣_∣_⊢fT_ where 
  ax : {X : At} → 
       R ∣ (just (` X) , _) ∣ [] ⊢fT (` X , _)
  Ir :  R ∣ (- , _) ∣ [] ⊢fT (I , _)
  passT : {Ω : Cxt} {A : Fma} {C : Pos}
           (f : just A ∣ Ω ⊢li C) → 
           -------------------------------
               P ∣ (- , _) ∣ A ∷ Ω ⊢fT C
  ⊗rT : (l : List Tag) {S : Irr} {Γ Δ Γ' : Cxt} {A B : Fma} →
         (ok : isOK l) (eq : Γ' ≡ Γ ++ Δ)→ 
         (f : l ∣ S ∣ Γ ⊢riT A) (g : - ∣ Δ ⊢ri B) → 
         -----------------------------------
              R ∣ S ∣ Γ' ⊢fT (A ⊗ B , _)
  ∧l₁T : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just A ∣ Γ ⊢li C) → 
        --------------------------------
              C₁ ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C
  ∧l₂T : {Γ : Cxt} {A B : Fma} {C : Pos}
        (f : just B ∣ Γ ⊢li C) → 
        --------------------------------
             C₂ ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C

-- decomposing ∧ in a formula A
data SubFmas : List Fma → Fma → Set where
  conj : {Φ Ψ : List Fma} {A A' B B' : Fma} → 
      SubFmas (A' ∷ Φ) A → SubFmas (B' ∷ Ψ) B → 
      SubFmas (A' ∷ Φ ++ B' ∷ Ψ) (A ∧ B)
  stop : {A : Fma} → 
       SubFmas [ A ]  A

SubFmas∧ : {Φ Ψ : List Fma} {Γ : List Fma} {A' B' A : Fma}
    → SubFmas Γ A → (eq : Γ ≡ (Φ ++ A' ∧ B' ∷ Ψ))
    → SubFmas (Φ ++ A' ∷ B' ∷ Ψ) A
SubFmas∧ {Φ'} {Ψ'} (conj {Φ} {Ψ} {A' = A'} {B' = B'} SF SF₁) eq with cases++ Φ' (A' ∷ Φ) Ψ' (B' ∷ Ψ) eq
SubFmas∧ {[]} {.(Δ ++ B' ∷ Ψ)} (conj {Δ} {Ψ} {A' = A'} {B' = B'} SF SF₁) refl | inj₁ (Δ , refl , refl) = conj {Φ = _ ∷ Δ} (SubFmas∧ {Φ = []} SF refl) SF₁
SubFmas∧ {x ∷ Φ'} {.(Δ ++ B' ∷ Ψ)} {A' = A'} (conj {.(Φ' ++ A' ∧ _ ∷ Δ)} {Ψ} {A' = _} {B' = B'} SF SF₁) refl | inj₁ (Δ , refl , refl) = conj {Φ = Φ' ++ A' ∷ _ ∷ Δ} (SubFmas∧ {Φ = x ∷ Φ'} SF refl) SF₁
SubFmas∧ {.(_ ∷ Φ ++ [])} {Ψ'} (conj {Φ} {.Ψ'} {A' = _} {B' = .(_ ∧ _)} SF SF₁) refl | inj₂ ([] , refl , refl) = conj SF (SubFmas∧ {Φ = []} SF₁ refl)
SubFmas∧ {.(_ ∷ Φ ++ x ∷ Δ)} {Ψ'} (conj {Φ} {.(Δ ++ _ ∧ _ ∷ Ψ')} {A' = _} {B' = .x} SF SF₁) refl | inj₂ (x ∷ Δ , refl , refl) = conj SF (SubFmas∧ {Φ = x ∷ Δ} SF₁ refl)
SubFmas∧ {[]} {[]} stop refl = conj stop stop
SubFmas∧ {x ∷ Φ} {[]} stop eq = ⊥-elim ([]disj∷ Φ (proj₂ (inj∷ eq)))
SubFmas∧ {x ∷ Φ} {x₁ ∷ Ψ} stop eq = ⊥-elim ([]disj∷ Φ (proj₂ (inj∷ eq)))

-- functions splitting a lists of derivations
fsDist : {S : Irr} {Γ : Cxt} {A B : Fma}
  → (Φ Ψ : List Fma) (fs : List (Σ Tag (λ t₁ → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t₁ S Γ)))) (eq : A ∷ Φ ++ B ∷ Ψ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs)
  → Σ (List (Σ Tag (λ t₁ → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t₁ S Γ)))) (λ fs' → Σ (List (Σ Tag (λ t₁ → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t₁ S Γ)))) (λ fs'' 
    → fs ≡ fs' ++ fs'' × A ∷ Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs' × B ∷ Ψ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs''))
fsDist [] [] (x ∷ x₁ ∷ []) refl = x ∷ [] , x₁ ∷ [] , refl , refl , refl
fsDist [] (x₁ ∷ Ψ) (x ∷ fs) eq with fsDist [] Ψ fs (proj₂ (inj∷ eq))
... | x₂ ∷ [] , x₃ ∷ fs'' , refl , refl , refl = x ∷ [] , x₂ ∷ x₃ ∷ fs'' , refl , cong (λ x → x ∷ []) (proj₁ (inj∷ eq)) , refl
fsDist (x₁ ∷ Φ) Ψ (x ∷ fs) eq with fsDist Φ Ψ fs (proj₂ (inj∷ eq))
... | x₂ ∷ fs' , x₃ ∷ fs'' , refl , refl , refl = x ∷ x₂ ∷ fs' , x₃ ∷ fs'' , refl , cong (λ x → x ∷ proj₁ (proj₁ (proj₂ x₂)) ∷ mapList (λ x₄ → proj₁ (proj₁ (proj₂ x₄))) fs') (proj₁ (inj∷ eq)) , refl

fsDist-white : {S : Stp} {Γ : Cxt} {A B : Fma}
  → (Φ Ψ : List Fma) (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C))) (eq : A ∷ Φ ++ B ∷ Ψ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → Σ (List (Σ Pos (λ C → S ∣ Γ ⊢li C))) (λ fs' → Σ (List (Σ Pos (λ C → S ∣ Γ ⊢li C))) (λ fs'' 
    → fs ≡ fs' ++ fs'' × A ∷ Φ ≡ mapList (λ x → pos (proj₁ x)) fs' × B ∷ Ψ ≡ mapList (λ x → pos (proj₁ x)) fs''))
fsDist-white [] [] (x ∷ x₁ ∷ []) refl = x ∷ [] , x₁ ∷ [] , refl , refl , refl
fsDist-white [] (x₁ ∷ Ψ) (x ∷ fs) eq with fsDist-white [] Ψ fs (proj₂ (inj∷ eq))
... | x₂ ∷ [] , x₃ ∷ fs'' , refl , refl , refl = x ∷ [] , x₂ ∷ x₃ ∷ fs'' , refl , cong (λ x → x ∷ []) (proj₁ (inj∷ eq)) , refl
fsDist-white (x₁ ∷ Φ) Ψ (x ∷ fs) eq with fsDist-white Φ Ψ fs (proj₂ (inj∷ eq))
... | x₂ ∷ fs' , x₃ ∷ fs'' , refl , refl , refl = x ∷ x₂ ∷ fs' , x₃ ∷ fs'' , refl , cong (λ x → x ∷ proj₁ (proj₁ x₂) ∷ mapList (λ x₄ → proj₁ (proj₁ x₄)) fs') (proj₁ (inj∷ eq)) , refl

-- several ∧rT in one step
∧rT* : {l : List Tag} {S : Irr} {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t S Γ))))
  → (SF : SubFmas Φ A)
  → (eq1 : Φ ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs)
  → (eq2 : l ≡ mapList proj₁ fs)
  → l ∣ S ∣ Γ ⊢riT A
∧rT* ((t , C , f) ∷ fs) (conj {Φ} {Ψ} {A' = A'} {B' = B'} SF SF₁) eq1 refl with fsDist Φ Ψ ((t , C , f) ∷ fs) eq1
... | (t , .C , .f) ∷ fs' , x₁ ∷ fs'' , refl , refl , refl = ∧rT (∧rT* ((t , C , f) ∷ fs') SF refl refl) ((∧rT* (x₁ ∷ fs'') SF₁ refl refl))
∧rT* ((t , C , f) ∷ []) stop refl refl = f2riT f

-- several ∧r in one step
∧r* : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ mapList (λ x → pos (proj₁ x)) fs)
  → S ∣ Γ ⊢ri A
∧r* ((C , f) ∷ fs) (conj {Φ} {Ψ} SF SF₁) eq with fsDist-white Φ Ψ ((C , f) ∷ fs) eq
... | .(C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl = ∧r (∧r* ((C , f) ∷ fs') SF refl) (∧r* ((C' , f') ∷ fs'') SF₁ refl)
∧r* ((C , f) ∷ []) stop refl = li2ri f

fsDist-white-refl : (S : Stp) (Γ : Cxt) {A B : Pos}
  → {f : S ∣ Γ ⊢li A} {g : S ∣ Γ ⊢li B}
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → (gs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → fsDist-white ((mapList (λ z → proj₁ (proj₁ z)) fs)) ((mapList (λ z → proj₁ (proj₁ z)) gs)) ((A , f) ∷ fs ++ (B , g) ∷ gs) refl ≡ ((A , f) ∷ fs , (B , g) ∷ gs , refl , refl , refl)
fsDist-white-refl S Γ [] [] = refl
fsDist-white-refl S Γ {B = B} {g = g} [] ((C , h) ∷ gs) with fsDist-white [] (mapList (λ z → proj₁ (proj₁ z)) gs) ((B , g) ∷ (C , h) ∷ gs) refl
... | .(B , g) ∷ [] , .(C , h) ∷ .gs , refl , refl , refl = refl
fsDist-white-refl S Γ {A} {B} {f} {g} ((A' , f') ∷ fs) gs 
  rewrite fsDist-white-refl S Γ {A'} {B} {f'} {g} fs gs = refl
{-# REWRITE fsDist-white-refl #-}

-- untag sequents in tagged focusing phase
untagF : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
  → t ∣ S ∣ Γ ⊢fT C
  → S ∣ Γ ⊢f C
untagF ax = ax
untagF Ir = Ir
untagF (passT f) = pass f
untagF (⊗rT l ok eq f g) = ⊗r l ok eq f g
untagF (∧l₁T f) = ∧l₁ f
untagF (∧l₂T f) = ∧l₂ f


-- rules with ' are rules applying to a list of derivations
untagF' :  {S : Irr} {Γ : Cxt}
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢fT C)) 
  → Σ Pos (λ C → S ∣ Γ ⊢f C)
untagF' (t , A , f) = A , untagF f

pass' : {Γ : Cxt} {A : Fma}
 → Σ Pos (λ C → just A ∣ Γ ⊢li C) 
 → Σ Pos (λ C → (- , tt) ∣ A ∷ Γ ⊢f C)
pass' (C , f) = C , pass f

passT' : {Γ : Cxt} {A : Fma}
 → Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ) 
 → Σ Tag (λ t → Σ (Σ Fma isPos) (_∣_∣_⊢fT_ t (- , tt) (A ∷ Γ)))
passT' (C , f) = P , (C , (passT f))

f2li' : {S : Irr} {Γ : Cxt}
  → Σ Pos (λ C → S ∣ Γ ⊢f C) 
  → Σ Pos (λ C → irr S ∣ Γ ⊢li C)
f2li' (C , f) = (C , f2li f)

∧l₁' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just A ∣ Γ ⊢li C)
  → Σ Pos (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C)
∧l₁' (C , f) = C , ∧l₁ f

∧l₂' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just B ∣ Γ ⊢li C)
  → Σ Pos (λ C → (just (A ∧ B) , _) ∣ Γ ⊢f C)
∧l₂' (C , f) = C , ∧l₂ f

∧l₁T' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just A ∣ Γ ⊢li C)
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C))
∧l₁T' (C , f) = C₁ , (C , (∧l₁T f))

∧l₂T' : {A B : Fma} {Γ : Cxt}
  → Σ Pos (λ C → just B ∣ Γ ⊢li C)
  → Σ Tag (λ t → Σ Pos (λ C → t ∣ (just (A ∧ B) , _) ∣ Γ ⊢fT C))
∧l₂T' (C , f) = C₂ , (C , (∧l₂T f))

-- ⊗l and Il are invertible
⊗l-inv-fs : {A B : Fma} {Γ : Cxt}
  → List (Σ Pos (λ P → just (A ⊗ B) ∣ Γ ⊢li P))
  → List (Σ Pos (λ P → just A ∣ B ∷ Γ ⊢li P))
⊗l-inv-fs [] = []
⊗l-inv-fs ((C , ⊗l f) ∷ fs) = (C , f) ∷ ⊗l-inv-fs fs

Il-inv-fs : {Γ : Cxt}
  → List (Σ Pos (λ P → just I ∣ Γ ⊢li P))
  → List (Σ Pos (λ P → - ∣ Γ ⊢li P))
Il-inv-fs [] = []
Il-inv-fs ((C , Il f) ∷ fs) = (C , f) ∷ Il-inv-fs fs

-- equality of irreducible stoups
irr-eq : (S : Stp) (p : isIrr S) → irr (S , p) ≡ S
irr-eq (just (` x)) tt = refl
irr-eq (just (x ∧ x₁)) tt = refl
irr-eq - tt = refl

isIrr-unique : (S : Stp) (p q : isIrr S) → p ≡ q 
isIrr-unique (just (` x)) p q = refl
isIrr-unique (just (x ∧ x₁)) p q = refl
isIrr-unique - p q = refl

-- a bunch of equality of lists of derivations
⊗l-inv-fs-eq : {A' B' : Fma} {Γ : Cxt}
  → (fs : List (Σ Pos (λ C → just (A' ⊗ B') ∣ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) (⊗l-inv-fs fs) ≡ mapList (λ x → pos (proj₁ x)) fs
⊗l-inv-fs-eq [] = refl
⊗l-inv-fs-eq ((C , ⊗l f) ∷ fs) = cong (pos C ∷_) (⊗l-inv-fs-eq fs)
{-# REWRITE ⊗l-inv-fs-eq #-}

Il-inv-fs-eq : {Γ : Cxt}
  → (fs : List (Σ Pos (λ C → just I ∣ Γ ⊢li C)))
  → mapList (λ x → pos (proj₁ x)) (Il-inv-fs fs) ≡ mapList (λ x → pos (proj₁ x)) fs
Il-inv-fs-eq [] = refl
Il-inv-fs-eq ((C , Il f) ∷ fs) = cong (pos C ∷_) (Il-inv-fs-eq fs)
{-# REWRITE Il-inv-fs-eq #-}

f2li-pass-fs-eq : {A : Fma} {Γ : Cxt}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList (λ x → pos (proj₁ x)) (mapList (λ x → proj₁ x , f2li (pass (proj₂ x))) fs) ≡ mapList (λ x → pos (proj₁ x)) fs
f2li-pass-fs-eq [] = refl
f2li-pass-fs-eq ((C , f) ∷ fs) = cong (pos C ∷_) (f2li-pass-fs-eq fs)
{-# REWRITE f2li-pass-fs-eq #-}

f2li-∧l₁-fs-eq : {A B : Fma} {Γ : Cxt}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList (λ x → proj₁ (proj₁ x)) (mapList (λ x → proj₁ x , f2li (∧l₁ {B = B} (proj₂ x))) fs) ≡ mapList (λ x → pos (proj₁ x)) fs
f2li-∧l₁-fs-eq [] = refl
f2li-∧l₁-fs-eq (x ∷ fs) = cong (proj₁ (proj₁ x) ∷_) (f2li-∧l₁-fs-eq fs)
{-# REWRITE f2li-∧l₁-fs-eq #-}

f2li-∧l₂-fs-eq : {A B : Fma} {Γ : Cxt}
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B) Γ)))
  → mapList (λ x → proj₁ (proj₁ x)) (mapList (λ x → proj₁ x , f2li (∧l₂ {A = A} (proj₂ x))) fs) ≡ mapList (λ x → pos (proj₁ x)) fs
f2li-∧l₂-fs-eq [] = refl
f2li-∧l₂-fs-eq (x ∷ fs) = cong (proj₁ (proj₁ x) ∷_) (f2li-∧l₂-fs-eq fs)
{-# REWRITE f2li-∧l₂-fs-eq #-}

f2li-f2li-untagF-∧l₁-fs-eq : {Γ : Cxt} {A B : Fma} 
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just A) Γ)))
  → mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) (mapList (λ x → ∧l₁T' {B = B} x) fs)
    ≡ mapList (λ x → proj₁ x , f2li (∧l₁ (proj₂ x))) fs
f2li-f2li-untagF-∧l₁-fs-eq [] = refl
f2li-f2li-untagF-∧l₁-fs-eq (x ∷ fs) = cong₂ _∷_ refl (f2li-f2li-untagF-∧l₁-fs-eq fs)
{-# REWRITE f2li-f2li-untagF-∧l₁-fs-eq #-}

f2li-f2li-untagF-∧l₂-fs-eq : {Γ : Cxt} {A B : Fma} 
  → (fs : List (Σ (Σ Fma isPos) (_∣_⊢li_ (just B) Γ)))
  → mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) (mapList (λ x → ∧l₂T' {A = A} x) fs)
    ≡ mapList (λ x → proj₁ x , f2li (∧l₂ (proj₂ x))) fs
f2li-f2li-untagF-∧l₂-fs-eq [] = refl
f2li-f2li-untagF-∧l₂-fs-eq (x ∷ fs) = cong₂ _∷_ refl ((f2li-f2li-untagF-∧l₂-fs-eq fs))
{-# REWRITE f2li-f2li-untagF-∧l₂-fs-eq #-}

f2li-pass-f2li-untagF-passT-fs-eq : {Γ : Cxt} {A' : Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ (just A') Γ)))
  → mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) (mapList passT' fs)
    ≡ mapList (λ x → proj₁ x , f2li (pass (proj₂ x))) fs
f2li-pass-f2li-untagF-passT-fs-eq [] = refl
f2li-pass-f2li-untagF-passT-fs-eq (x ∷ fs) = cong₂ _∷_ refl (f2li-pass-f2li-untagF-passT-fs-eq fs)
{-# REWRITE f2li-pass-f2li-untagF-passT-fs-eq #-}

f2li-untagF-fs-eq : {S : Irr} {Γ : Cxt}
  → (fs : List (Σ Tag (λ t → Σ Pos (_∣_∣_⊢fT_ t S Γ))))
  → mapList (λ x → proj₁ (proj₁ x)) (mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) fs)
    ≡ mapList (λ x → pos (proj₁ (proj₂ x))) fs
f2li-untagF-fs-eq [] = refl
f2li-untagF-fs-eq (x ∷ fs) = cong₂ _∷_ refl (f2li-untagF-fs-eq fs)
{-# REWRITE f2li-untagF-fs-eq #-}

-- {- check the shape of a list of derivations,
-- there are three possibilities:
-- i) all end with pass 
-- ii) all end with ∧lᵢ
-- iii) none of the above
-- -}
check-focus : {S : Irr} {Γ : Cxt}
  → (f : Σ Pos (λ C → irr S ∣ Γ ⊢li C))
  → (fs : List (Σ Pos (λ C → irr S ∣ Γ ⊢li C)))
  → (Σ Fma (λ A → Σ Fma (λ B → (Σ (List (Σ Pos (λ C → just A ∣ Γ ⊢li C))) (λ fs' → Σ (irr S ≡ just (A ∧ B)) (λ eq →
      subst (λ x → List (Σ Pos (λ C → x ∣ Γ ⊢li C))) eq (f ∷ fs) ≡ mapList (λ x → f2li'  (∧l₁' {B = B} x)) fs')))))
    ⊎
    Σ Fma (λ A → Σ Fma (λ B → (Σ (List (Σ Pos (λ C → just B ∣ Γ ⊢li C))) (λ fs' → Σ (irr S ≡ just (A ∧ B)) (λ eq →
      subst (λ x → List (Σ Pos (λ C → x ∣ Γ ⊢li C))) eq (f ∷ fs) ≡ mapList (λ x → f2li'  (∧l₂' {A = A} x)) fs')))))
    ⊎ 
    Σ Fma (λ A → Σ Cxt (λ Γ' → Σ (List (Σ Pos (λ C → just A ∣ Γ' ⊢li C))) (λ fs' → Σ (irr S ≡ -) (λ eq1 → Σ (Γ ≡ A ∷ Γ') (λ eq2 
      → subst₂ (λ x → λ y → List (Σ Pos (λ C → x ∣ y ⊢li C))) eq1 eq2 (f ∷ fs) ≡ mapList (λ x → f2li' (pass' x)) fs'))))))
    ⊎
    (Σ (List (Σ Tag (λ t → Σ Pos (λ C → t ∣ S ∣ Γ ⊢fT C)))) (λ fs' → f ∷ fs ≡ mapList (λ x → f2li' (untagF' x)) fs' × isOK (mapList proj₁ fs')))
check-focus (C , f2li (pass {Γ = Γ} {A}  f)) [] = inj₁ (inj₂ (inj₂ (A , (Γ , ((C , f) ∷ []) , (refl , (refl , refl))))))
check-focus (.(` X , tt) , f2li (ax {X})) [] = inj₂ (((R , ((` X , tt) , ax)) ∷ []) , refl , tt)
check-focus (.(I , tt) , f2li Ir) [] = inj₂ (((R , ((I , tt) , Ir)) ∷ []) , (refl , tt))
check-focus {S , q} (.(A ⊗ B , tt) , f2li {.(irr (S , q)) , p} (⊗r l {A = A} {B} ok refl f g)) [] 
  rewrite irr-eq S p | isIrr-unique S p q = inj₂ (((R , ((A ⊗ B , tt) , (⊗rT l ok refl f g))) ∷ []) , refl , tt)
check-focus (C , f2li (∧l₁ {A = A} {B} f)) [] = inj₁ (inj₁ (A , B , (((C , f) ∷ []) , (refl , refl))))
check-focus (C , f2li (∧l₂ {A = A} {B} f)) [] = inj₁ (inj₂ (inj₁ (A , (B , (((C , f) ∷ []) , (refl , refl))))))
check-focus (C , f2li (pass f)) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₂ (inj₂ (A , Γ' , x ∷ fs' , refl , refl , refl))) = inj₁ (inj₂ (inj₂ (A , (Γ' , (((C , f) ∷ x ∷ fs') , (refl , (refl , refl)))))))
... | inj₂ ((t , C' , f₁) ∷ fs' , refl , ok) = inj₂ (((P , C , passT f) ∷ (t , C' , f₁) ∷ fs') , (refl , ok)) 
check-focus (.(` X , tt) , f2li (ax {X})) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((t , C' , f₁) ∷ fs' , refl , ok) = inj₂ (((R , ((` X , tt) , ax)) ∷ (t , C' , f₁) ∷ fs') , refl , tt) 
check-focus (.(I , tt) , f2li Ir) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((t , C' , f₁) ∷ fs' , refl , ok) = inj₂ (((R , ((I , tt) , Ir)) ∷ (t , C' , f₁) ∷ fs') , (refl , tt))
check-focus {S} (.(A ⊗ B , tt) , f2li (⊗r l {A = A} {B} ok refl f g)) (f' ∷ fs) with check-focus {S} f' fs
... | inj₁ (inj₁ (A' , B' , f₁ ∷ fs' , refl , refl)) = inj₂ ((R , ((A ⊗ B , tt) , (⊗rT l ok refl f g))) ∷ mapList (λ x → ∧l₁T' x) (f₁ ∷ fs') , refl , tt) 
... | inj₁ (inj₂ (inj₁ (A' , B' , f₁ ∷ fs' , refl , refl))) = inj₂ ((R , ((A ⊗ B , tt) , (⊗rT l ok refl f g))) ∷ mapList (λ x → ∧l₂T' x) (f₁ ∷ fs') , refl , tt)
check-focus {.- , snd} (.(A ⊗ B , tt) , f2li (⊗r l {Γ = []} {A = A} {B} ok refl f g)) (f' ∷ fs) | inj₁ (inj₂ (inj₂ (A' , Γ' , f₁ ∷ fs' , refl , refl , refl))) = 
  inj₂ (((R , ((A ⊗ B , tt) , (⊗rT l ok refl f g))) ∷ mapList passT' (f₁ ∷ fs')) , (refl , tt))
check-focus {.- , snd} (.(A ⊗ B , tt) , f2li (⊗r l {Γ = x ∷ Γ} {Δ} {A = A} {B} ok refl f g)) (f' ∷ fs) | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , f₁ ∷ fs' , refl , refl , refl))) = 
  inj₂ (((R , ((A ⊗ B , tt) , (⊗rT l ok refl f g))) ∷ mapList passT' (f₁ ∷ fs')) , (refl , tt))
check-focus {just (` x) , snd} (.(A ⊗ B , tt) , f2li (⊗r l {A = A} {B} ok refl f g)) (f' ∷ fs) | inj₂ (x₁ ∷ fs' , refl , ok') = 
  inj₂ (((R , ((A ⊗ B , tt) ,  (⊗rT l ok refl f g))) ∷ (x₁ ∷ fs')) , refl , tt)
check-focus {just (x ∧ x₁) , snd} (.(A ⊗ B , tt) , f2li (⊗r l {A = A} {B} ok refl f g)) (f' ∷ fs) | inj₂ (x₂ ∷ fs' , refl , ok') = 
  inj₂ (((R , ((A ⊗ B , tt) , (⊗rT l ok refl f g))) ∷ (x₂ ∷ fs')) , refl , tt)
check-focus { - , snd} (.(A ⊗ B , tt) , f2li (⊗r l {A = A} {B} ok refl f g)) (.(C , f2li (untagF f₁)) ∷ .(mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) fs')) | inj₂ ((t , C , f₁) ∷ fs' , refl , ok') = 
  inj₂ (((R , ((A ⊗ B , tt) , (⊗rT l ok refl f g))) ∷ (t , C , f₁) ∷ fs') , (refl , tt))
check-focus (C , f2li (∧l₁ f)) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₁ (A , B , fs' , refl , eq2)) = inj₁ (inj₁ (A , B , (C , f) ∷ fs' , refl , cong ((C , f2li (∧l₁ f)) ∷_) eq2))
... | inj₁ (inj₂ (inj₁ (A , B , x ∷ fs' , refl , refl))) = inj₂ (((C₁ , (C , (∧l₁T f))) ∷ mapList (λ x → ∧l₂T' x) (x ∷ fs')) , (refl , tt))
check-focus (C , f2li (∧l₁ f)) (f' ∷ fs) | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT l {A = A} {B} ok₁ refl f₁ g)) ∷ fs' , refl , ok) = 
  inj₂ (((C₁ , (C ,  (∧l₁T f))) ∷ (R , (A ⊗ B , tt) , (⊗rT l {A = A} {B} ok₁ refl f₁ g)) ∷ fs') , (refl , tt))
... | inj₂ ((.C₁ , C' , ∧l₁T f₁) ∷ fs' , refl , ok) = 
  inj₂ (((C₁ , (C , (∧l₁T f))) ∷ (C₁ , C' , ∧l₁T f₁) ∷ fs') , (refl , ok))
... | inj₂ ((.C₂ , C' , ∧l₂T f₁) ∷ fs' , refl , ok) = 
  inj₂ (((C₁ , (C , (∧l₁T f))) ∷ (C₂ , C' , ∧l₂T f₁) ∷ fs') , (refl , tt))
check-focus (C , f2li (∧l₂ f)) (f' ∷ fs) with check-focus f' fs
... | inj₁ (inj₁ (A , B , x ∷ fs' , refl , eq2)) = inj₂ (((C₂ , (C , (∧l₂T f))) ∷ mapList (λ x → ∧l₁T' x) (x ∷ fs')) , cong ((C , f2li (∧l₂ f)) ∷_)  eq2 , _)
... | inj₁ (inj₂ (inj₁ (A , B , fs' , refl , eq2))) = inj₁ (inj₂ (inj₁ (A , B , (C , f) ∷ fs' , refl , cong ((C , f2li (∧l₂ f)) ∷_) eq2)))
check-focus (C , f2li (∧l₂ f)) (f' ∷ fs) | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT l {A = A} {B} ok₁ refl f₁ g)) ∷ fs' , refl , ok) = 
  inj₂ (((C₂ , (C , (∧l₂T f))) ∷ (R , (A ⊗ B , tt) , ⊗rT l {A = A} {B} ok₁ refl f₁ g) ∷ fs') , (refl , tt))
... | inj₂ ((.C₁ , C' , ∧l₁T f₁) ∷ fs' , refl , ok) = 
  inj₂ (((C₂ , (C , (∧l₂T f))) ∷ (C₁ , C' , ∧l₁T f₁) ∷ fs') , (refl , tt))
... | inj₂ ((.C₂ , C' , ∧l₂T f₁) ∷ fs' , refl , ok) = 
  inj₂ (((C₂ , (C , (∧l₂T f))) ∷ (C₂ , C' , ∧l₂T f₁) ∷ fs') , (refl , ok))

-- generalized ⊗r rule
gen⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma} {C : Pos}
  → (f : S ∣ Γ ⊢li C)
  → (fs : List (Σ Pos (λ C → S ∣ Γ ⊢li C)))
  → SubFmas (pos C ∷ mapList (λ x → pos (proj₁ x)) fs) A
  → - ∣ Δ ⊢ri B
  → S ∣ Γ ++ Δ ⊢li (A ⊗ B , _)
gen⊗r-li (⊗l f) fs SF g = ⊗l (gen⊗r-li f (⊗l-inv-fs fs) SF g)
gen⊗r-li (Il f) fs SF g = Il (gen⊗r-li f (Il-inv-fs fs) SF g)
gen⊗r-li {C = C} (f2li (pass f)) fs SF g with check-focus (C , f2li (pass f)) fs
... | inj₁ (inj₂ (inj₂ (A' , Γ' , (C , f) ∷ fs' , refl , refl , refl))) = f2li (pass (gen⊗r-li f fs' SF g))
gen⊗r-li {C = C} (f2li (pass f)) fs SF g | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l {Γ = []} ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
gen⊗r-li {C = C} (f2li (pass f)) fs SF g | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l {Γ = x ∷ Γ} ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
gen⊗r-li {C = .C'} (f2li (pass f)) .(mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) fs') SF g | inj₂ ((.P , C' , passT .f) ∷ fs' , refl , ok) = 
  f2li ((⊗r (P ∷ mapList proj₁ fs') ok refl (∧rT* ((P , C' , passT f) ∷ fs') SF refl refl) g))
gen⊗r-li (f2li ((ax {X}))) fs SF g with check-focus ((` X , tt) , f2li ((ax))) fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((.R , (` X , tt) , ax) ∷ fs' , refl , ok) = 
  f2li ((⊗r (R ∷ mapList proj₁ fs') tt refl (∧rT* ((R , (` X , tt) , ax) ∷ fs') SF refl refl) g))
gen⊗r-li (f2li (Ir)) fs SF g with check-focus ((I , tt) , f2li (Ir)) fs
... | inj₁ (inj₂ (inj₁ ()))
... | inj₁ (inj₂ (inj₂ ()))
... | inj₂ ((.R , (I , tt) , Ir) ∷ fs' , refl , ok) = 
  f2li ((⊗r (R ∷ mapList proj₁ fs') tt refl (∧rT* ((R , (I , tt) , Ir) ∷ fs') SF refl refl) g))
gen⊗r-li (f2li ((⊗r l {S = S} {A = A} {B} ok eq f g₁))) fs SF g with check-focus {S = S} ((A ⊗ B , tt) , (f2li ((⊗r l {A = A} {B} ok eq f g₁)))) fs
... | inj₁ (inj₁ (A' , B' , [] , refl , ()))
... | inj₁ (inj₁ (A' , B' , x ∷ fs' , refl , ()))
... | inj₁ (inj₂ (inj₁ (A' , B' , [] , refl , ())))
... | inj₁ (inj₂ (inj₁ (A' , B' , x ∷ fs' , refl , ())))
gen⊗r-li (f2li ((⊗r l {_} {[]} {A = _} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (A' , Γ' , [] , refl , refl , ())))
gen⊗r-li (f2li ((⊗r l {_} {[]} {A = _} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (A' , Γ' , x ∷ fs' , refl , refl , ())))
gen⊗r-li (f2li ((⊗r l {_} {x ∷ Γ} {Δ} {_} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , [] , refl , refl , ())))
gen⊗r-li (f2li ((⊗r l {_} {x ∷ Γ} {Δ} {_} {_} ok refl f g₁))) fs SF g | inj₁ (inj₂ (inj₂ (.x , .(Γ ++ Δ) , x₁ ∷ fs' , refl , refl , ())))
gen⊗r-li (f2li {S , snd} ((⊗r l {S , snd} {Γ = []} {A = A} {B} ok refl f g₁))) .(mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) fs') SF g | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT .l .ok refl .f .g₁)) ∷ fs' , refl , ok') = 
  f2li ((⊗r (R ∷ (mapList proj₁ fs')) tt refl (∧rT* ((R , (A ⊗ B , tt) , (⊗rT l ok refl f g₁)) ∷ fs') SF refl refl) g))
gen⊗r-li (f2li {S , snd} ((⊗r l {S , snd} {Γ = x ∷ Γ} {A = A} {B} ok .refl f g₁))) .(mapList (λ x₁ → proj₁ (proj₂ x₁) , f2li (untagF (proj₂ (proj₂ x₁)))) fs') SF g | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT .l .ok refl .f .g₁)) ∷ fs' , refl , ok') = 
  f2li ((⊗r (R ∷ (mapList proj₁ fs')) tt refl (∧rT* ((R , (A ⊗ B , tt) , (⊗rT l ok refl f g₁)) ∷ fs') SF refl refl) g))
gen⊗r-li {C = C} (f2li ((∧l₁ f))) fs SF g with check-focus (C , (f2li ((∧l₁ f)))) fs
... | inj₁ (inj₁ (A , B , (C' , .f) ∷ fs' , refl , refl)) = f2li ((∧l₁ (gen⊗r-li f fs' SF g)))
... | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq))) with inj∷ eq
... | () , eq2
gen⊗r-li {C = C} (f2li ((∧l₁ f))) fs SF g | inj₂ ((.R , .(A ⊗ B , tt) , (⊗rT l {A = A} {B} ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
gen⊗r-li {C = .C'} (f2li ((∧l₁ f))) .(mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) fs') SF g | inj₂ ((.C₁ , C' , (∧l₁T .f)) ∷ fs' , refl , ok) = 
  f2li ((⊗r (C₁ ∷ (mapList proj₁ fs')) ok refl (∧rT* ((C₁ , C' , (∧l₁T f)) ∷ fs') SF refl refl) g))
gen⊗r-li {C = C} (f2li ((∧l₂ f))) fs SF g with check-focus (C , (f2li ((∧l₂ f)))) fs
... | inj₁ (inj₁ (A , B , (C' , f') ∷ fs' , refl , eq)) with inj∷ eq
... | () , eq2
gen⊗r-li {C = C} (f2li ((∧l₂ f))) fs SF g | inj₁ (inj₂ (inj₁ (A , B , (C' , f') ∷ fs' , refl , refl))) 
  = f2li ((∧l₂ (gen⊗r-li f fs' SF g)))
gen⊗r-li {C = C} (f2li ((∧l₂ f))) fs SF g | inj₂ ((.R , .(_ ⊗ _ , tt) , (⊗rT l ok₁ refl f₁ g₁)) ∷ fs' , () , ok)
gen⊗r-li {C = .C'} (f2li ((∧l₂ f))) .(mapList (λ x → proj₁ (proj₂ x) , f2li (untagF (proj₂ (proj₂ x)))) fs') SF g | inj₂ ((.C₂ , C' , (∧l₂T .f)) ∷ fs' , refl , ok) = 
  f2li ((⊗r (C₂ ∷ (mapList proj₁ fs')) ok refl (∧rT* ((C₂ , C' , (∧l₂T f)) ∷ fs') SF refl refl) g))

-- phase ri is invertible
f2fs : {S : Stp} {Γ : Cxt} {A : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → Σ (List (Σ Pos (λ C → S ∣ Γ ⊢li C))) (λ fs → Σ (List Fma) (λ Φ → Σ (Φ ≡ mapList (λ x → pos (proj₁ x)) fs) (λ eq → Σ (SubFmas Φ A) (λ SF → f ≡ ∧r* fs SF eq))))
f2fs {S} {Γ} (∧r f g) with f2fs f | f2fs g
... | ((A , snd) , f') ∷ fs , .A ∷ .(mapList (λ x → proj₁ (proj₁ x)) fs) , refl , SF1 , refl | ((B , snd₁) , g') ∷ gs , .B ∷ .(mapList (λ x → proj₁ (proj₁ x)) gs) , refl , SF2 , refl = 
  ((A , snd) , f') ∷ fs ++ ((B , snd₁) , g') ∷ gs , A ∷ (mapList (λ x → proj₁ (proj₁ x)) fs) ++ B ∷ (mapList (λ x → proj₁ (proj₁ x)) gs) , refl , conj SF1 SF2 , refl
f2fs (li2ri {C = C} f) = (C , f) ∷ [] , pos C ∷ [] , refl , stop , refl

f2fs-refl : {S : Stp} {Γ : Cxt} {A : Fma}
  → {Φ : List Fma}
  → (fs : List (Σ Pos (_∣_⊢li_ S Γ)))
  → (SF : SubFmas Φ A)
  → (eq : Φ ≡ (mapList (λ x → proj₁ (proj₁ x)) fs))
  → f2fs (∧r* fs SF eq) ≡ (fs , Φ , eq , SF , refl)
f2fs-refl {S} {Γ} fs (conj {Φ} {Ψ} SF1 SF2) eq with fsDist-white Φ Ψ fs eq
f2fs-refl {S} {Γ} .(((C , f) ∷ fs') ++ (C' , f') ∷ fs'') (conj {.(mapList (λ x → proj₁ (proj₁ x)) fs')} {.(mapList (λ x → proj₁ (proj₁ x)) fs'')} SF1 SF2) refl | (C , f) ∷ fs' , (C' , f') ∷ fs'' , refl , refl , refl 
  rewrite f2fs-refl ((C , f) ∷ fs') SF1 refl | f2fs-refl ((C' , f') ∷ fs'') SF2 refl = refl
f2fs-refl (x ∷ []) stop refl = refl

-- admissible rules
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

⊗r-ri : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
  → (f : S ∣ Γ ⊢ri A)
  → (g : - ∣ Δ ⊢ri B)
  → S ∣ Γ ++ Δ ⊢ri A ⊗ B
⊗r-ri {A = A} f g with f2fs f
... | [] , .[] , refl , () , refl
... | (C , f₁) ∷ fs , .(mapList (λ x → proj₁ (proj₁ x)) ((C , f₁) ∷ fs)) , refl , SF , refl = li2ri (gen⊗r-li f₁ fs SF g)

Ir-ri : - ∣ [] ⊢ri I
Ir-ri = li2ri (f2li Ir)

ax-ri : {C : Fma} → just C ∣ [] ⊢ri C
ax-ri {C = ` x} = li2ri (f2li ax)
ax-ri {C = I} = li2ri (Il (f2li Ir))
ax-ri {C = C ⊗ C'} = ⊗l-ri (⊗r-ri ax-ri (pass-ri ax-ri))
ax-ri {C = C ∧ C'} = ∧r (∧l₁-ri ax-ri) (∧l₂-ri ax-ri)

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

  emb-fT : {t : Tag} {S : Irr} {Γ : Cxt} {C : Pos}
    → (f : t ∣ S ∣ Γ ⊢fT C)
    → irr S ∣ Γ ⊢ pos C
  emb-fT ax = ax
  emb-fT Ir = Ir
  emb-fT (passT f) = pass (emb-li f)
  emb-fT (⊗rT l ok refl f g) = ⊗r (emb-riT f) (emb-ri g)
  emb-fT (∧l₁T f) = ∧l₁ (emb-li f)
  emb-fT (∧l₂T f) = ∧l₂ (emb-li f)       