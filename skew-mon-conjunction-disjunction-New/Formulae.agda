{-# OPTIONS --safe #-}

module Formulae (At : Set) where

open import Data.Maybe
open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_∧_; _∨_)
open import Relation.Nullary
open import Utilities



-- Formulae over the arbitrary set At of atoms.
data Fma : Set where 
  ` : At → Fma
  I : Fma
  -- top : Fma
  -- bot : Fma
  _⊗_ : Fma → Fma → Fma
  _∧_ : Fma → Fma → Fma
  _∨_ : Fma → Fma → Fma
infix 22 _⊗_ _∧_ _∨_

-- The stoup holds at most one distinguished formula; - denotes an empty stoup.
Stp : Set
Stp = Maybe Fma

pattern - = nothing

-- Contexts are ordered lists of formulae.
Cxt : Set
Cxt = List Fma

-- Iterated ⊗
_⊗⋆_ : Fma → Cxt → Fma
A ⊗⋆ [] = A
A ⊗⋆ (B ∷ Γ) = (A ⊗ B) ⊗⋆ Γ

infix 21 _⊗⋆_

snoc⊗⋆ : (Γ : Cxt) (A B : Fma)
  → (A ⊗⋆ (Γ ∷ʳ B)) ≡ (A ⊗⋆ Γ) ⊗ B
snoc⊗⋆ [] = λ A B → refl
snoc⊗⋆ (x ∷ Γ) = λ A → snoc⊗⋆ Γ (A ⊗ x)

-- Predicates used to determine which focused phase applies.

-- the formula is not atomic
isn'tAt : Fma → Set
isn'tAt (` x) = ⊥
isn'tAt _ = ⊤

-- the outermost connective is not ⊗
isn't⊗ : Fma → Set
isn't⊗ (A ⊗ B) = ⊥
isn't⊗ _ = ⊤

-- Negative formulae are atoms and conjunctions.
-- Atoms are also positive, so they can occur in the focused axiom.
isNeg : Fma → Set
isNeg (` x) = ⊤
isNeg I = ⊥
isNeg (x ⊗ x₁) = ⊥
isNeg (x ∧ x₁) = ⊤
isNeg (x ∨ x₁) = ⊥

isAt : Fma → Set
isAt (` x) = ⊤
isAt _ = ⊥

-- Positive formulae are atoms, I, tensors, and disjunctions.
isPos : Fma → Set
isPos (` x) = ⊤
isPos I = ⊤
isPos (x ⊗ x₁) = ⊤
isPos (x ∧ x₁) = ⊥
isPos (x ∨ x₁) = ⊤

isPosBool : Fma → Bool
isPosBool (` x) = true
isPosBool I = true
isPosBool (A ⊗ A₁) = true
isPosBool (A ∧ A₁) = false
isPosBool (A ∨ A₁) = true

-- Strictly positive formulae exclude atoms as well as conjunctions.
isPPos : Fma → Set
isPPos (A ∧ B) = ⊥
isPPos (` X) = ⊥
isPPos _ = ⊤

-- Predicate on stoups checking whether the stoup is irreducible,
-- i.e. it is either empty or a negative formula
isIrr : Stp → Set
isIrr - = ⊤
isIrr (just A) = isNeg (A)

isPosS : Stp → Set
isPosS (just x) = isPos x
isPosS - = ⊤

isIrrAt : Stp → Set
isIrrAt (just A) = isAt A
isIrrAt ─ = ⊤

-- The type of irreducible stoups
Irr : Set
Irr = Σ Stp λ S → isIrr S

PosS : Set
PosS = Σ Stp λ S → isPosS S

IrrAt : Set
IrrAt = Σ Stp λ S → isIrrAt S

irrisAt : ∀ S → isIrrAt S → isIrr S
irrisAt (just (` x)) y = y
irrisAt - y = y

irrAt : IrrAt → Irr
irrAt (S , p) = S , irrisAt S p

-- The type of positive formulae
Pos : Set
Pos = Σ Fma λ A → isPos A

PPos : Set
PPos = Σ Fma λ A → isPPos A

-- The type of negative formulae
Neg : Set
Neg = Σ Fma λ A → isNeg A

-- Projections and embeddings
irr : Irr → Stp
irr (S , s) = S

posS : PosS → Stp
posS (S , s) = S

ppos2pos : ∀ A → isPPos A → isPos A
ppos2pos I a = tt
ppos2pos (A ⊗ A₁) a = tt
ppos2pos (A ∨ A₁) a = tt

pos : Pos → Fma
pos (A , a) = A

ppos : PPos → Fma
ppos (A , a) = A

ppos2 : PPos → Pos
ppos2 (A , a) = A , ppos2pos A a

neg : Neg → Fma
neg (A , a) = A

neg2irr : Neg → Irr
neg2irr (A , a) = just A , a 
 
irr-eq : (S : Stp) (p : isIrr S) → irr (S , p) ≡ S
irr-eq (just (` x)) tt = refl
irr-eq (just (x ∧ x₁)) tt = refl
irr-eq - tt = refl

-- Irreducibility witnesses are unique, so they do not distinguish derivations.
isIrr-unique : (S : Stp) (p q : isIrr S) → p ≡ q
isIrr-unique (just (` x)) p q = refl
isIrr-unique (just (x ∧ x₁)) p q = refl
isIrr-unique - p q = refl

pos-eq : (A : Fma) (p : isPos A) → pos (A , p) ≡ A
pos-eq (` x) p = refl
pos-eq I p = refl
pos-eq (A ⊗ A₁) p = refl
pos-eq (A ∨ A₁) p = refl

-- Positivity witnesses are likewise unique.
isPos-unique : (A : Fma) (p q : isPos A) → p ≡ q
isPos-unique (` x) p q = refl
isPos-unique I p q = refl
isPos-unique (A ⊗ A₁) p q = refl
isPos-unique (A ∨ A₁) p q = refl

-- Split conjunctions into a binary tree, stopping at positive formulae.
-- This records exactly the premises exposed by the right-invertible phase.
toTree : Fma → Tree Pos
toTree (` X) = leaf (` X , _)
toTree I = leaf (I , _)
toTree (A ⊗ B) = leaf (A ⊗ B , _)
toTree (A ∧ B) = node (toTree A) (toTree B)
toTree (A ∨ B) = leaf (A ∨ B , _)
