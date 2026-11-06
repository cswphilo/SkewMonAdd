{-# OPTIONS --safe #-}

module Focus.Tags where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; _≟_)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality

-- P n records the position selected by pass, counted from zero.
data Tag : Set where
  R C₁ C₂ : Tag
  P : ℕ → Tag

-- Validity with a remembered projection and pass position.
isOKC₁P : ℕ → List Tag → Set
isOKC₁P n [] = ⊥
isOKC₁P n (R ∷ ts) = ⊤
isOKC₁P n (C₁ ∷ ts) = isOKC₁P n ts
isOKC₁P n (C₂ ∷ ts) = ⊤
isOKC₁P n (P m ∷ ts) with n ≟ m
... | yes _ = isOKC₁P n ts
... | no _ = ⊤

-- A remembered projection also allows two distinct pass positions.
isOKC₁ : List Tag → Set
isOKC₁ [] = ⊥
isOKC₁ (R ∷ ts) = ⊤
isOKC₁ (C₁ ∷ ts) = isOKC₁ ts
isOKC₁ (C₂ ∷ ts) = ⊤
isOKC₁ (P m ∷ ts) = isOKC₁P m ts

-- The symmetric case remembers the second projection.
isOKC₂P : ℕ → List Tag → Set
isOKC₂P n [] = ⊥
isOKC₂P n (R ∷ ts) = ⊤
isOKC₂P n (C₁ ∷ ts) = ⊤
isOKC₂P n (C₂ ∷ ts) = isOKC₂P n ts
isOKC₂P n (P m ∷ ts) with n ≟ m
... | yes _ = isOKC₂P n ts
... | no _ = ⊤

isOKC₂ : List Tag → Set
isOKC₂ [] = ⊥
isOKC₂ (R ∷ ts) = ⊤
isOKC₂ (C₁ ∷ ts) = ⊤
isOKC₂ (C₂ ∷ ts) = isOKC₂ ts
isOKC₂ (P m ∷ ts) = isOKC₂P m ts

-- A remembered pass position also allows opposite projections.
isOKP : ℕ → List Tag → Set
isOKP n [] = ⊥
isOKP n (R ∷ ts) = ⊤
isOKP n (C₁ ∷ ts) = isOKC₁P n ts
isOKP n (C₂ ∷ ts) = isOKC₂P n ts
isOKP n (P m ∷ ts) with n ≟ m
... | yes _ = isOKP n ts
... | no _ = ⊤

-- Validity: R, both projections, or two distinct pass positions.
isOK : List Tag → Set
isOK [] = ⊥
isOK (R ∷ ts) = ⊤
isOK (C₁ ∷ ts) = isOKC₁ ts
isOK (C₂ ∷ ts) = isOKC₂ ts
isOK (P m ∷ ts) = isOKP m ts

-- Each predicate computes to ⊤ or ⊥, so witnesses are unique.
isProp-isOKC₁P : ∀ n ts {p q : isOKC₁P n ts} → p ≡ q
isProp-isOKC₁P n [] {p = ()}
isProp-isOKC₁P n (R ∷ ts) = refl
isProp-isOKC₁P n (C₁ ∷ ts) = isProp-isOKC₁P n ts
isProp-isOKC₁P n (C₂ ∷ ts) = refl
isProp-isOKC₁P n (P m ∷ ts) with n ≟ m
... | yes _ = isProp-isOKC₁P n ts
... | no _ = refl

isProp-isOKC₁ : ∀ ts {p q : isOKC₁ ts} → p ≡ q
isProp-isOKC₁ [] {p = ()}
isProp-isOKC₁ (R ∷ ts) = refl
isProp-isOKC₁ (C₁ ∷ ts) = isProp-isOKC₁ ts
isProp-isOKC₁ (C₂ ∷ ts) = refl
isProp-isOKC₁ (P m ∷ ts) = isProp-isOKC₁P m ts

isProp-isOKC₂P : ∀ n ts {p q : isOKC₂P n ts} → p ≡ q
isProp-isOKC₂P n [] {p = ()}
isProp-isOKC₂P n (R ∷ ts) = refl
isProp-isOKC₂P n (C₁ ∷ ts) = refl
isProp-isOKC₂P n (C₂ ∷ ts) = isProp-isOKC₂P n ts
isProp-isOKC₂P n (P m ∷ ts) with n ≟ m
... | yes _ = isProp-isOKC₂P n ts
... | no _ = refl

isProp-isOKC₂ : ∀ ts {p q : isOKC₂ ts} → p ≡ q
isProp-isOKC₂ [] {p = ()}
isProp-isOKC₂ (R ∷ ts) = refl
isProp-isOKC₂ (C₁ ∷ ts) = refl
isProp-isOKC₂ (C₂ ∷ ts) = isProp-isOKC₂ ts
isProp-isOKC₂ (P m ∷ ts) = isProp-isOKC₂P m ts

isProp-isOKP : ∀ n ts {p q : isOKP n ts} → p ≡ q
isProp-isOKP n [] {p = ()}
isProp-isOKP n (R ∷ ts) = refl
isProp-isOKP n (C₁ ∷ ts) = isProp-isOKC₁P n ts
isProp-isOKP n (C₂ ∷ ts) = isProp-isOKC₂P n ts
isProp-isOKP n (P m ∷ ts) with n ≟ m
... | yes _ = isProp-isOKP n ts
... | no _ = refl

isProp-isOK : ∀ ts {p q : isOK ts} → p ≡ q
isProp-isOK [] {p = ()}
isProp-isOK (R ∷ ts) = refl
isProp-isOK (C₁ ∷ ts) = isProp-isOKC₁ ts
isProp-isOK (C₂ ∷ ts) = isProp-isOKC₂ ts
isProp-isOK (P m ∷ ts) = isProp-isOKP m ts

-- Appending tags preserves validity established in the prefix.
isOKC₁P++1 : ∀ n ts {us} → isOKC₁P n ts → isOKC₁P n (ts ++ us)
isOKC₁P++1 n [] ()
isOKC₁P++1 n (R ∷ ts) ok = tt
isOKC₁P++1 n (C₁ ∷ ts) ok = isOKC₁P++1 n ts ok
isOKC₁P++1 n (C₂ ∷ ts) ok = tt
isOKC₁P++1 n (P m ∷ ts) ok with n ≟ m
... | yes _ = isOKC₁P++1 n ts ok
... | no _ = tt

isOKC₁++1 : ∀ ts {us} → isOKC₁ ts → isOKC₁ (ts ++ us)
isOKC₁++1 [] ()
isOKC₁++1 (R ∷ ts) ok = tt
isOKC₁++1 (C₁ ∷ ts) ok = isOKC₁++1 ts ok
isOKC₁++1 (C₂ ∷ ts) ok = tt
isOKC₁++1 (P m ∷ ts) ok = isOKC₁P++1 m ts ok

isOKC₂P++1 : ∀ n ts {us} → isOKC₂P n ts → isOKC₂P n (ts ++ us)
isOKC₂P++1 n [] ()
isOKC₂P++1 n (R ∷ ts) ok = tt
isOKC₂P++1 n (C₁ ∷ ts) ok = tt
isOKC₂P++1 n (C₂ ∷ ts) ok = isOKC₂P++1 n ts ok
isOKC₂P++1 n (P m ∷ ts) ok with n ≟ m
... | yes _ = isOKC₂P++1 n ts ok
... | no _ = tt

isOKC₂++1 : ∀ ts {us} → isOKC₂ ts → isOKC₂ (ts ++ us)
isOKC₂++1 [] ()
isOKC₂++1 (R ∷ ts) ok = tt
isOKC₂++1 (C₁ ∷ ts) ok = tt
isOKC₂++1 (C₂ ∷ ts) ok = isOKC₂++1 ts ok
isOKC₂++1 (P m ∷ ts) ok = isOKC₂P++1 m ts ok

isOKP++1 : ∀ n ts {us} → isOKP n ts → isOKP n (ts ++ us)
isOKP++1 n [] ()
isOKP++1 n (R ∷ ts) ok = tt
isOKP++1 n (C₁ ∷ ts) ok = isOKC₁P++1 n ts ok
isOKP++1 n (C₂ ∷ ts) ok = isOKC₂P++1 n ts ok
isOKP++1 n (P m ∷ ts) ok with n ≟ m
... | yes _ = isOKP++1 n ts ok
... | no _ = tt

isOK++1 : ∀ ts {us} → isOK ts → isOK (ts ++ us)
isOK++1 [] ()
isOK++1 (R ∷ ts) ok = tt
isOK++1 (C₁ ∷ ts) ok = isOKC₁++1 ts ok
isOK++1 (C₂ ∷ ts) ok = isOKC₂++1 ts ok
isOK++1 (P m ∷ ts) ok = isOKP++1 m ts ok

-- Set-valued presence predicates used when combining premise trees.
hasC₁ : List Tag → Set
hasC₁ [] = ⊥
hasC₁ (C₁ ∷ ts) = ⊤
hasC₁ (_ ∷ ts) = hasC₁ ts

hasC₂ : List Tag → Set
hasC₂ [] = ⊥
hasC₂ (C₂ ∷ ts) = ⊤
hasC₂ (_ ∷ ts) = hasC₂ ts

differsFromP : ℕ → List Tag → Set
differsFromP n [] = ⊥
differsFromP n (R ∷ ts) = differsFromP n ts
differsFromP n (C₁ ∷ ts) = differsFromP n ts
differsFromP n (C₂ ∷ ts) = differsFromP n ts
differsFromP n (P m ∷ ts) with n ≟ m
... | yes _ = differsFromP n ts
... | no _ = ⊤

differentP : List Tag → Set
differentP [] = ⊥
differentP (R ∷ ts) = differentP ts
differentP (C₁ ∷ ts) = differentP ts
differentP (C₂ ∷ ts) = differentP ts
differentP (P n ∷ ts) = differsFromP n ts

-- Presence of the opposite projection establishes validity.
valid-C₁P : ∀ n ts → hasC₂ ts → isOKC₁P n ts
valid-C₁P n [] ()
valid-C₁P n (R ∷ ts) p = tt
valid-C₁P n (C₁ ∷ ts) p = valid-C₁P n ts p
valid-C₁P n (C₂ ∷ ts) p = tt
valid-C₁P n (P m ∷ ts) p with n ≟ m
... | yes _ = valid-C₁P n ts p
... | no _ = tt

valid-C₁ : ∀ ts → hasC₂ ts → isOKC₁ ts
valid-C₁ [] ()
valid-C₁ (R ∷ ts) p = tt
valid-C₁ (C₁ ∷ ts) p = valid-C₁ ts p
valid-C₁ (C₂ ∷ ts) p = tt
valid-C₁ (P m ∷ ts) p = valid-C₁P m ts p

valid-C₂P : ∀ n ts → hasC₁ ts → isOKC₂P n ts
valid-C₂P n [] ()
valid-C₂P n (R ∷ ts) p = tt
valid-C₂P n (C₁ ∷ ts) p = tt
valid-C₂P n (C₂ ∷ ts) p = valid-C₂P n ts p
valid-C₂P n (P m ∷ ts) p with n ≟ m
... | yes _ = valid-C₂P n ts p
... | no _ = tt

valid-C₂ : ∀ ts → hasC₁ ts → isOKC₂ ts
valid-C₂ [] ()
valid-C₂ (R ∷ ts) p = tt
valid-C₂ (C₁ ∷ ts) p = tt
valid-C₂ (C₂ ∷ ts) p = valid-C₂ ts p
valid-C₂ (P m ∷ ts) p = valid-C₂P m ts p

valid-CsP : ∀ n ts → hasC₁ ts → hasC₂ ts → isOKP n ts
valid-CsP n [] () q
valid-CsP n (R ∷ ts) p q = tt
valid-CsP n (C₁ ∷ ts) p q = valid-C₁P n ts q
valid-CsP n (C₂ ∷ ts) p q = valid-C₂P n ts p
valid-CsP n (P m ∷ ts) p q with n ≟ m
... | yes _ = valid-CsP n ts p q
... | no _ = tt

valid-Cs : ∀ ts → hasC₁ ts → hasC₂ ts → isOK ts
valid-Cs [] () q
valid-Cs (R ∷ ts) p q = tt
valid-Cs (C₁ ∷ ts) p q = valid-C₁ ts q
valid-Cs (C₂ ∷ ts) p q = valid-C₂ ts p
valid-Cs (P m ∷ ts) p q = valid-CsP m ts p q

-- A pass at a different position establishes validity.
valid-diffC₁P : ∀ n ts → differsFromP n ts → isOKC₁P n ts
valid-diffC₁P n [] ()
valid-diffC₁P n (R ∷ ts) p = tt
valid-diffC₁P n (C₁ ∷ ts) p = valid-diffC₁P n ts p
valid-diffC₁P n (C₂ ∷ ts) p = tt
valid-diffC₁P n (P m ∷ ts) p with n ≟ m
... | yes _ = valid-diffC₁P n ts p
... | no _ = tt

valid-diffC₂P : ∀ n ts → differsFromP n ts → isOKC₂P n ts
valid-diffC₂P n [] ()
valid-diffC₂P n (R ∷ ts) p = tt
valid-diffC₂P n (C₁ ∷ ts) p = tt
valid-diffC₂P n (C₂ ∷ ts) p = valid-diffC₂P n ts p
valid-diffC₂P n (P m ∷ ts) p with n ≟ m
... | yes _ = valid-diffC₂P n ts p
... | no _ = tt

valid-diffP : ∀ n ts → differsFromP n ts → isOKP n ts
valid-diffP n [] ()
valid-diffP n (R ∷ ts) p = tt
valid-diffP n (C₁ ∷ ts) p = valid-diffC₁P n ts p
valid-diffP n (C₂ ∷ ts) p = valid-diffC₂P n ts p
valid-diffP n (P m ∷ ts) p with n ≟ m
... | yes _ = valid-diffP n ts p
... | no _ = tt

valid-PsC₁ : ∀ ts → differentP ts → isOKC₁ ts
valid-PsC₁ [] ()
valid-PsC₁ (R ∷ ts) p = tt
valid-PsC₁ (C₁ ∷ ts) p = valid-PsC₁ ts p
valid-PsC₁ (C₂ ∷ ts) p = tt
valid-PsC₁ (P n ∷ ts) p = valid-diffC₁P n ts p

valid-PsC₂ : ∀ ts → differentP ts → isOKC₂ ts
valid-PsC₂ [] ()
valid-PsC₂ (R ∷ ts) p = tt
valid-PsC₂ (C₁ ∷ ts) p = tt
valid-PsC₂ (C₂ ∷ ts) p = valid-PsC₂ ts p
valid-PsC₂ (P n ∷ ts) p = valid-diffC₂P n ts p

valid-Ps : ∀ ts → differentP ts → isOK ts
valid-Ps [] ()
valid-Ps (R ∷ ts) p = tt
valid-Ps (C₁ ∷ ts) p = valid-PsC₁ ts p
valid-Ps (C₂ ∷ ts) p = valid-PsC₂ ts p
valid-Ps (P n ∷ ts) p = valid-diffP n ts p

isOKP-toC₁P : ∀ n ts → isOKP n ts → isOKC₁P n ts
isOKP-toC₁P n [] ()
isOKP-toC₁P n (R ∷ ts) ok = tt
isOKP-toC₁P n (C₁ ∷ ts) ok = ok
isOKP-toC₁P n (C₂ ∷ ts) ok = tt
isOKP-toC₁P n (P m ∷ ts) ok with n ≟ m
... | yes refl = isOKP-toC₁P n ts ok
... | no _ = tt

isOK-toC₁ : ∀ ts → isOK ts → isOKC₁ ts
isOK-toC₁ [] ()
isOK-toC₁ (R ∷ ts) ok = tt
isOK-toC₁ (C₁ ∷ ts) ok = ok
isOK-toC₁ (C₂ ∷ ts) ok = tt
isOK-toC₁ (P m ∷ ts) ok = isOKP-toC₁P m ts ok

isOKP-toC₂P : ∀ n ts → isOKP n ts → isOKC₂P n ts
isOKP-toC₂P n [] ()
isOKP-toC₂P n (R ∷ ts) ok = tt
isOKP-toC₂P n (C₁ ∷ ts) ok = tt
isOKP-toC₂P n (C₂ ∷ ts) ok = ok
isOKP-toC₂P n (P m ∷ ts) ok with n ≟ m
... | yes refl = isOKP-toC₂P n ts ok
... | no _ = tt

isOK-toC₂ : ∀ ts → isOK ts → isOKC₂ ts
isOK-toC₂ [] ()
isOK-toC₂ (R ∷ ts) ok = tt
isOK-toC₂ (C₁ ∷ ts) ok = tt
isOK-toC₂ (C₂ ∷ ts) ok = ok
isOK-toC₂ (P m ∷ ts) ok = isOKP-toC₂P m ts ok

-- Remembering an additional choice preserves validity.
isOKC₁-toC₁P : ∀ n ts → isOKC₁ ts → isOKC₁P n ts
isOKC₁-toC₁P n [] ()
isOKC₁-toC₁P n (R ∷ ts) ok = tt
isOKC₁-toC₁P n (C₁ ∷ ts) ok = isOKC₁-toC₁P n ts ok
isOKC₁-toC₁P n (C₂ ∷ ts) ok = tt
isOKC₁-toC₁P n (P m ∷ ts) ok with n ≟ m
... | yes refl = ok
... | no _ = tt

isOKC₂-toC₂P : ∀ n ts → isOKC₂ ts → isOKC₂P n ts
isOKC₂-toC₂P n [] ()
isOKC₂-toC₂P n (R ∷ ts) ok = tt
isOKC₂-toC₂P n (C₁ ∷ ts) ok = tt
isOKC₂-toC₂P n (C₂ ∷ ts) ok = isOKC₂-toC₂P n ts ok
isOKC₂-toC₂P n (P m ∷ ts) ok with n ≟ m
... | yes refl = ok
... | no _ = tt

isOK-toP : ∀ n ts → isOK ts → isOKP n ts
isOK-toP n [] ()
isOK-toP n (R ∷ ts) ok = tt
isOK-toP n (C₁ ∷ ts) ok = isOKC₁-toC₁P n ts ok
isOK-toP n (C₂ ∷ ts) ok = isOKC₂-toC₂P n ts ok
isOK-toP n (P m ∷ ts) ok with n ≟ m
... | yes refl = ok
... | no _ = tt

valid-cons : ∀ t ts → isOK ts → isOK (t ∷ ts)
valid-cons R ts ok = tt
valid-cons C₁ ts ok = isOK-toC₁ ts ok
valid-cons C₂ ts ok = isOK-toC₂ ts ok
valid-cons (P n) ts ok = isOK-toP n ts ok

hasC₁-++1 : ∀ xs ys → hasC₁ xs → hasC₁ (xs ++ ys)
hasC₁-++1 [] ys ()
hasC₁-++1 (R ∷ xs) ys p = hasC₁-++1 xs ys p
hasC₁-++1 (C₁ ∷ xs) ys p = tt
hasC₁-++1 (C₂ ∷ xs) ys p = hasC₁-++1 xs ys p
hasC₁-++1 (P n ∷ xs) ys p = hasC₁-++1 xs ys p

hasC₁-++2 : ∀ xs ys → hasC₁ ys → hasC₁ (xs ++ ys)
hasC₁-++2 [] ys p = p
hasC₁-++2 (R ∷ xs) ys p = hasC₁-++2 xs ys p
hasC₁-++2 (C₁ ∷ xs) ys p = tt
hasC₁-++2 (C₂ ∷ xs) ys p = hasC₁-++2 xs ys p
hasC₁-++2 (P n ∷ xs) ys p = hasC₁-++2 xs ys p

hasC₂-++1 : ∀ xs ys → hasC₂ xs → hasC₂ (xs ++ ys)
hasC₂-++1 [] ys ()
hasC₂-++1 (R ∷ xs) ys p = hasC₂-++1 xs ys p
hasC₂-++1 (C₁ ∷ xs) ys p = hasC₂-++1 xs ys p
hasC₂-++1 (C₂ ∷ xs) ys p = tt
hasC₂-++1 (P n ∷ xs) ys p = hasC₂-++1 xs ys p

hasC₂-++2 : ∀ xs ys → hasC₂ ys → hasC₂ (xs ++ ys)
hasC₂-++2 [] ys p = p
hasC₂-++2 (R ∷ xs) ys p = hasC₂-++2 xs ys p
hasC₂-++2 (C₁ ∷ xs) ys p = hasC₂-++2 xs ys p
hasC₂-++2 (C₂ ∷ xs) ys p = tt
hasC₂-++2 (P n ∷ xs) ys p = hasC₂-++2 xs ys p

differsFromP-++1 : ∀ n xs ys → differsFromP n xs → differsFromP n (xs ++ ys)
differsFromP-++1 n [] ys ()
differsFromP-++1 n (R ∷ xs) ys p = differsFromP-++1 n xs ys p
differsFromP-++1 n (C₁ ∷ xs) ys p = differsFromP-++1 n xs ys p
differsFromP-++1 n (C₂ ∷ xs) ys p = differsFromP-++1 n xs ys p
differsFromP-++1 n (P m ∷ xs) ys p with n ≟ m
... | yes _ = differsFromP-++1 n xs ys p
... | no _ = tt

differsFromP-++2 : ∀ n xs ys → differsFromP n ys → differsFromP n (xs ++ ys)
differsFromP-++2 n [] ys p = p
differsFromP-++2 n (R ∷ xs) ys p = differsFromP-++2 n xs ys p
differsFromP-++2 n (C₁ ∷ xs) ys p = differsFromP-++2 n xs ys p
differsFromP-++2 n (C₂ ∷ xs) ys p = differsFromP-++2 n xs ys p
differsFromP-++2 n (P m ∷ xs) ys p with n ≟ m
... | yes _ = differsFromP-++2 n xs ys p
... | no _ = tt

-- A valid suffix stays valid after any prefix.
isOK++2 : ∀ ts {us} → isOK us → isOK (ts ++ us)
isOK++2 [] ok = ok
isOK++2 (t ∷ ts) ok = valid-cons t _ (isOK++2 ts ok)


-- Lists consisting uniformly of one projection cannot be valid.
onlyC₁ : List Tag → Set
onlyC₁ [] = ⊤
onlyC₁ (R ∷ ts) = ⊥
onlyC₁ (P n ∷ ts) = ⊥
onlyC₁ (C₁ ∷ ts) = onlyC₁ ts
onlyC₁ (C₂ ∷ ts) = ⊥

onlyC₂ : List Tag → Set
onlyC₂ [] = ⊤
onlyC₂ (R ∷ ts) = ⊥
onlyC₂ (P n ∷ ts) = ⊥
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

-- A uniform pass position cannot justify a right introduction.
onlyP : ℕ → List Tag → Set
onlyP n [] = ⊤
onlyP n (R ∷ ts) = ⊥
onlyP n (C₁ ∷ ts) = ⊥
onlyP n (C₂ ∷ ts) = ⊥
onlyP n (P m ∷ ts) with n ≟ m
... | yes _ = onlyP n ts
... | no _ = ⊥

onlyP++ : ∀ n ts {us} → onlyP n ts → onlyP n us → onlyP n (ts ++ us)
onlyP++ n [] p q = q
onlyP++ n (P m ∷ ts) p q with n ≟ m
... | yes _ = onlyP++ n ts p q
... | no _ = ⊥-elim p

notOK-onlyP' : ∀ n ts → onlyP n ts → isOKP n ts → ⊥
notOK-onlyP' n [] p ()
notOK-onlyP' n (P m ∷ ts) p ok with n ≟ m
... | yes _ = notOK-onlyP' n ts p ok
... | no _ = p

notOK-onlyP : ∀ n ts → onlyP n ts → isOK ts → ⊥
notOK-onlyP n [] p ()
notOK-onlyP n (P m ∷ ts) p ok with n ≟ m
... | yes refl = notOK-onlyP' n ts p ok
... | no _ = p

-- Relabeling pass positions by an injection preserves validity.
rename-tag : (ℕ → ℕ) → Tag → Tag
rename-tag ρ R = R
rename-tag ρ C₁ = C₁
rename-tag ρ C₂ = C₂
rename-tag ρ (P n) = P (ρ n)

isOKC₁P-rename : (ρ : ℕ → ℕ) → (∀ {m n} → ρ m ≡ ρ n → m ≡ n)
  → ∀ n ts → isOKC₁P n ts → isOKC₁P (ρ n) (map (rename-tag ρ) ts)
isOKC₁P-rename ρ inj n [] ()
isOKC₁P-rename ρ inj n (R ∷ ts) ok = tt
isOKC₁P-rename ρ inj n (C₁ ∷ ts) ok = isOKC₁P-rename ρ inj n ts ok
isOKC₁P-rename ρ inj n (C₂ ∷ ts) ok = tt
isOKC₁P-rename ρ inj n (P m ∷ ts) ok with n ≟ m | ρ n ≟ ρ m
... | yes refl | yes _ = isOKC₁P-rename ρ inj n ts ok
... | yes refl | no neq = ⊥-elim (neq refl)
... | no neq | yes eq = ⊥-elim (neq (inj eq))
... | no _ | no _ = tt

isOKC₂P-rename : (ρ : ℕ → ℕ) → (∀ {m n} → ρ m ≡ ρ n → m ≡ n)
  → ∀ n ts → isOKC₂P n ts → isOKC₂P (ρ n) (map (rename-tag ρ) ts)
isOKC₂P-rename ρ inj n [] ()
isOKC₂P-rename ρ inj n (R ∷ ts) ok = tt
isOKC₂P-rename ρ inj n (C₁ ∷ ts) ok = tt
isOKC₂P-rename ρ inj n (C₂ ∷ ts) ok = isOKC₂P-rename ρ inj n ts ok
isOKC₂P-rename ρ inj n (P m ∷ ts) ok with n ≟ m | ρ n ≟ ρ m
... | yes refl | yes _ = isOKC₂P-rename ρ inj n ts ok
... | yes refl | no neq = ⊥-elim (neq refl)
... | no neq | yes eq = ⊥-elim (neq (inj eq))
... | no _ | no _ = tt

isOKC₁-rename : (ρ : ℕ → ℕ) → (∀ {m n} → ρ m ≡ ρ n → m ≡ n)
  → ∀ ts → isOKC₁ ts → isOKC₁ (map (rename-tag ρ) ts)
isOKC₁-rename ρ inj [] ()
isOKC₁-rename ρ inj (R ∷ ts) ok = tt
isOKC₁-rename ρ inj (C₁ ∷ ts) ok = isOKC₁-rename ρ inj ts ok
isOKC₁-rename ρ inj (C₂ ∷ ts) ok = tt
isOKC₁-rename ρ inj (P m ∷ ts) ok = isOKC₁P-rename ρ inj m ts ok

isOKC₂-rename : (ρ : ℕ → ℕ) → (∀ {m n} → ρ m ≡ ρ n → m ≡ n)
  → ∀ ts → isOKC₂ ts → isOKC₂ (map (rename-tag ρ) ts)
isOKC₂-rename ρ inj [] ()
isOKC₂-rename ρ inj (R ∷ ts) ok = tt
isOKC₂-rename ρ inj (C₁ ∷ ts) ok = tt
isOKC₂-rename ρ inj (C₂ ∷ ts) ok = isOKC₂-rename ρ inj ts ok
isOKC₂-rename ρ inj (P m ∷ ts) ok = isOKC₂P-rename ρ inj m ts ok

isOKP-rename : (ρ : ℕ → ℕ) → (∀ {m n} → ρ m ≡ ρ n → m ≡ n)
  → ∀ n ts → isOKP n ts → isOKP (ρ n) (map (rename-tag ρ) ts)
isOKP-rename ρ inj n [] ()
isOKP-rename ρ inj n (R ∷ ts) ok = tt
isOKP-rename ρ inj n (C₁ ∷ ts) ok = isOKC₁P-rename ρ inj n ts ok
isOKP-rename ρ inj n (C₂ ∷ ts) ok = isOKC₂P-rename ρ inj n ts ok
isOKP-rename ρ inj n (P m ∷ ts) ok with n ≟ m | ρ n ≟ ρ m
... | yes refl | yes _ = isOKP-rename ρ inj n ts ok
... | yes refl | no neq = ⊥-elim (neq refl)
... | no neq | yes eq = ⊥-elim (neq (inj eq))
... | no _ | no _ = tt

isOK-rename : (ρ : ℕ → ℕ) → (∀ {m n} → ρ m ≡ ρ n → m ≡ n)
  → ∀ ts → isOK ts → isOK (map (rename-tag ρ) ts)
isOK-rename ρ inj [] ()
isOK-rename ρ inj (R ∷ ts) ok = tt
isOK-rename ρ inj (C₁ ∷ ts) ok = isOKC₁-rename ρ inj ts ok
isOK-rename ρ inj (C₂ ∷ ts) ok = isOKC₂-rename ρ inj ts ok
isOK-rename ρ inj (P m ∷ ts) ok = isOKP-rename ρ inj m ts ok

