{-# OPTIONS --safe #-}

module Fma (At : Set) where

open import Agda.Builtin.Maybe
open import Data.List.Base
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality.Core


data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma
  _⊸_ : Fma → Fma → Fma
  _∧_ : Fma → Fma → Fma
  _∨_ : Fma → Fma → Fma

infix 22 _⊗_ _⊸_ _∧_ _∨_

Stp : Set
Stp = Maybe Fma

pattern - = nothing

Cxt : Set
Cxt = List Fma

isNeg : Fma → Set
isNeg (` X) = ⊤
isNeg (A ⊸ B) = ⊤
isNeg (A ∧ B) = ⊤
isNeg _ = ⊥

isPos : Fma → Set
isPos (A ⊸ B) = ⊥
isPos (A ∧ B) = ⊥
isPos _ = ⊤

isIrr : Stp → Set
isIrr - = ⊤
isIrr (just A) = isNeg A

Irr : Set
Irr = Σ Stp isIrr

Pos : Set
Pos = Σ Fma isPos

irr : Irr → Stp
irr (S , p) = S

pos : Pos → Fma
pos (A , p) = A

isIrr-unique : (S : Stp) (p q : isIrr S) → p ≡ q
isIrr-unique - p q = refl
isIrr-unique (just (` X)) p q = refl
isIrr-unique (just (A ⊸ B)) p q = refl
isIrr-unique (just (A ∧ B)) p q = refl

open import Utilities

impconj : Cxt → Fma → Tree (Cxt × Pos)
impconj Ω (A ∧ B) = node (impconj Ω A) (impconj Ω B)
impconj Ω (A ⊸ B) = impconj (Ω ++ A ∷ []) B
impconj Ω (` X)   = leaf (Ω , (` X , tt))
impconj Ω I       = leaf (Ω , (I , tt))
impconj Ω (A ⊗ B) = leaf (Ω , (A ⊗ B , tt))
impconj Ω (A ∨ B) = leaf (Ω , (A ∨ B , tt))
