{-# OPTIONS --safe #-}
module Tags where
open import Data.List
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality

data Tag : Set where
  R : Tag -- the tag for non-left non-invertible rules
  C₁ : Tag -- for ∧l₁
  C₂ : Tag -- for ∧l₂
  P : Tag  -- for pass

{-
The predicates below recognize valid lists of tags.
The tag P is ignored throughout.
In particular, a list of tags
is valid if
i) there is at least one tag R, or
ii) both C₁ and C₂ are in the list.
-}

isOKC₁ : List Tag → Set
isOKC₁ (C₂ ∷ l) = ⊤
isOKC₁ (R ∷ l) = ⊤
isOKC₁ (C₁ ∷ l) = isOKC₁ l
isOKC₁ (P ∷ l) = isOKC₁ l
isOKC₁ [] = ⊥

isOKC₂ : List Tag → Set
isOKC₂ (C₁ ∷ l) = ⊤
isOKC₂ (R ∷ l) = ⊤
isOKC₂ (C₂ ∷ l) = isOKC₂ l
isOKC₂ (P ∷ l) = isOKC₂ l
isOKC₂ [] = ⊥

isOK : List Tag → Set
isOK [] = ⊥
isOK (R ∷ l) = ⊤
isOK (C₁ ∷ l) = isOKC₁ l
isOK (C₂ ∷ l) = isOKC₂ l
isOK (P ∷ l) = isOK l



-- Validity witnesses are unique. This lets constructor equalities ignore
-- the particular proof supplied for a normal-form side condition.
isProp-isOKC₁ : ∀ ts {p q : isOKC₁ ts} → p ≡ q
isProp-isOKC₁ (P ∷ ts) = isProp-isOKC₁ ts
isProp-isOKC₁ (R ∷ ts) = refl
isProp-isOKC₁ (C₁ ∷ ts) = isProp-isOKC₁ ts
isProp-isOKC₁ (C₂ ∷ ts) = refl

isProp-isOKC₂ : ∀ ts {p q : isOKC₂ ts} → p ≡ q
isProp-isOKC₂ (P ∷ ts) = isProp-isOKC₂ ts
isProp-isOKC₂ (R ∷ ts) = refl
isProp-isOKC₂ (C₁ ∷ ts) = refl
isProp-isOKC₂ (C₂ ∷ ts) = isProp-isOKC₂ ts

isProp-isOK : ∀ ts {p q : isOK ts} → p ≡ q
isProp-isOK (R ∷ ts) = refl
isProp-isOK (C₁ ∷ ts) = isProp-isOKC₁ ts
isProp-isOK (C₂ ∷ ts) = isProp-isOKC₂ ts
isProp-isOK (P ∷ ts) = isProp-isOK ts

-- Appending tags preserves validity already established in the prefix.
isOKC₁++1 : ∀ ts {us} → isOKC₁ ts → isOKC₁ (ts ++ us)
isOKC₁++1 (P ∷ ts) okt = isOKC₁++1 ts okt
isOKC₁++1 (R ∷ ts) okt = tt
isOKC₁++1 (C₁ ∷ ts) okt = isOKC₁++1 ts okt
isOKC₁++1 (C₂ ∷ ts) okt = tt

isOKC₂++1 : ∀ ts {us} → isOKC₂ ts → isOKC₂ (ts ++ us)
isOKC₂++1 (P ∷ ts) okt = isOKC₂++1 ts okt
isOKC₂++1 (R ∷ ts) _ = tt
isOKC₂++1 (C₁ ∷ ts) _ = tt
isOKC₂++1 (C₂ ∷ ts) okt = isOKC₂++1 ts okt

isOK++1 : ∀ ts {us} → isOK ts → isOK (ts ++ us)
isOK++1 (R ∷ ts) okt = tt
isOK++1 (C₁ ∷ ts) okt = isOKC₁++1 ts okt
isOK++1 (C₂ ∷ ts) okt = isOKC₂++1 ts okt
isOK++1 (P ∷ ts) okt = isOK++1 ts okt

-- Lists consisting uniformly of one projection cannot be valid.
onlyC₁ : List Tag → Set
onlyC₁ [] = ⊤
onlyC₁ (R ∷ ts) = ⊥
onlyC₁ (P ∷ ts) = ⊥
onlyC₁ (C₁ ∷ ts) = onlyC₁ ts
onlyC₁ (C₂ ∷ ts) = ⊥

onlyC₂ : List Tag → Set
onlyC₂ [] = ⊤
onlyC₂ (R ∷ ts) = ⊥
onlyC₂ (P ∷ ts) = ⊥
onlyC₂ (C₂ ∷ ts) = onlyC₂ ts
onlyC₂ (C₁ ∷ ts) = ⊥

onlyC₁++ : ∀ ts {us} → onlyC₁ ts → onlyC₁ us → onlyC₁ (ts ++ us)
onlyC₁++ [] p q = q
onlyC₁++ (C₁ ∷ ts) p q = onlyC₁++ ts p q

onlyC₂++ : ∀ ts {us} → onlyC₂ ts → onlyC₂ us → onlyC₂ (ts ++ us)
onlyC₂++ [] p q = q
onlyC₂++ (C₂ ∷ ts) p q = onlyC₂++ ts p q

notOK-onlyC₁' : ∀ ts → onlyC₁ ts → isOKC₁ ts → ⊥
notOK-onlyC₁' (C₁ ∷ ts) p ok = notOK-onlyC₁' ts p ok

notOK-onlyC₁ : ∀ ts → onlyC₁ ts → isOK ts → ⊥
notOK-onlyC₁ (C₁ ∷ ts) p ok = notOK-onlyC₁' ts p ok

notOK-onlyC₂' : ∀ ts → onlyC₂ ts → isOKC₂ ts → ⊥
notOK-onlyC₂' (C₂ ∷ ts) p ok = notOK-onlyC₂' ts p ok

notOK-onlyC₂ : ∀ ts → onlyC₂ ts → isOK ts → ⊥
notOK-onlyC₂ (C₂ ∷ ts) p ok = notOK-onlyC₂' ts p ok

-- Combining nonempty lists of opposite projections establishes validity.
isOKC₁++C₂' : ∀ ts {us} → onlyC₁ ts → onlyC₂ us  → (us ≡ [] → ⊥) → isOKC₁ (ts ++ us)
isOKC₁++C₂' [] {[]} p neq q = q refl
isOKC₁++C₂' [] {C₂ ∷ us} p neq q = tt
isOKC₁++C₂' (C₁ ∷ ts) p neq q = isOKC₁++C₂' ts p neq q

isOKC₁++C₂ : ∀ ts {us} → onlyC₁ ts → onlyC₂ us → (ts ≡ [] → ⊥) → (us ≡ [] → ⊥) → isOK (ts ++ us)
isOKC₁++C₂ [] p q neq _ = ⊥-elim (neq refl)
isOKC₁++C₂ (C₁ ∷ ts) p q _ neq = isOKC₁++C₂' ts p q neq

isOKC₂++C₁' : ∀ ts {us} → onlyC₂ ts → onlyC₁ us  → (us ≡ [] → ⊥) → isOKC₂ (ts ++ us)
isOKC₂++C₁' [] {[]} p neq q = q refl
isOKC₂++C₁' [] {C₁ ∷ us} p neq q = tt
isOKC₂++C₁' (C₂ ∷ ts) p neq q = isOKC₂++C₁' ts p neq q

isOKC₂++C₁ : ∀ ts {us} → onlyC₂ ts → onlyC₁ us → (ts ≡ [] → ⊥) → (us ≡ [] → ⊥) → isOK (ts ++ us)
isOKC₂++C₁ [] p q neq _ = ⊥-elim (neq refl)
isOKC₂++C₁ (C₂ ∷ ts) p q _ neq = isOKC₂++C₁' ts p q neq

-- A valid suffix makes any prefix valid; P is ignored in each predicate.
isOK-toC₁ : ∀ ts → isOK ts → isOKC₁ ts
isOK-toC₁ (R ∷ ts) ok = tt
isOK-toC₁ (C₁ ∷ ts) ok = ok
isOK-toC₁ (C₂ ∷ ts) ok = tt
isOK-toC₁ (P ∷ ts) ok = isOK-toC₁ ts ok

isOKC₁++2 : ∀ ts {us} → isOK us → isOKC₁ (ts ++ us)
isOKC₁++2 [] {us} ok = isOK-toC₁ us ok
isOKC₁++2 (R ∷ ts) ok = tt
isOKC₁++2 (C₁ ∷ ts) ok = isOKC₁++2 ts ok
isOKC₁++2 (C₂ ∷ ts) ok = tt
isOKC₁++2 (P ∷ ts) ok = isOKC₁++2 ts ok

isOK-toC₂ : ∀ ts → isOK ts → isOKC₂ ts
isOK-toC₂ (R ∷ ts) ok = tt
isOK-toC₂ (C₂ ∷ ts) ok = ok
isOK-toC₂ (C₁ ∷ ts) ok = tt
isOK-toC₂ (P ∷ ts) ok = isOK-toC₂ ts ok

isOKC₂++2 : ∀ ts {us} → isOK us → isOKC₂ (ts ++ us)
isOKC₂++2 [] {us} ok = isOK-toC₂ us ok
isOKC₂++2 (R ∷ ts) ok = tt
isOKC₂++2 (C₂ ∷ ts) ok = isOKC₂++2 ts ok
isOKC₂++2 (C₁ ∷ ts) ok = tt
isOKC₂++2 (P ∷ ts) ok = isOKC₂++2 ts ok

isOK++2 : ∀ ts {us} → isOK us → isOK (ts ++ us)
isOK++2 [] ok = ok
isOK++2 (R ∷ ts) ok = tt
isOK++2 (C₁ ∷ ts) ok = isOKC₁++2 ts ok
isOK++2 (C₂ ∷ ts) ok = isOKC₂++2 ts ok
isOK++2 (P ∷ ts) ok = isOK++2 ts ok

-- Trees ending uniformly in pass cannot justify a right introduction.
onlyP : List Tag → Set
onlyP [] = ⊤
onlyP (P ∷ ts) = onlyP ts
onlyP (R ∷ ts) = ⊥
onlyP (C₁ ∷ ts) = ⊥
onlyP (C₂ ∷ ts) = ⊥

onlyP++ : ∀ ts {us} → onlyP ts → onlyP us → onlyP (ts ++ us)
onlyP++ [] p q = q
onlyP++ (P ∷ ts) p q = onlyP++ ts p q

notOK-onlyP : ∀ ts → onlyP ts → isOK ts → ⊥
notOK-onlyP (P ∷ ts) p ok = notOK-onlyP ts p ok
