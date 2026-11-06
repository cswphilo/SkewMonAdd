{-# OPTIONS --safe #-}

module FocusSeqCalc (At : Set) where

open import Data.List.Base
open import Agda.Builtin.Maybe
open import Data.Product.Base
open import Data.Sum.Base
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Bool.Base renaming (_∧_ to _∧ᵇ_; _∨_ to _∨ᵇ_)
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality.Core

open import Utilities
open import Fma At

data _∣_⊢ri_ : Stp → Cxt → Fma → Set
data _∣_⊢li_ : Stp → Cxt → Pos → Set
data _∣_⊢f_ : Irr → Cxt → Pos → Set
data Tag : Set

data Tag where
  R P C₁ C₂ • : Tag
  ⊸l : {A : Fma} (Γ : Cxt) → - ∣ Γ ⊢ri A → Tag


tag-f : ∀ {S C Λ} (Γ Ω : Cxt) → S ∣ Λ ⊢f C → (eq : Λ ≡ Γ ++ Ω) → Tag

-- Compare rule constructors and context splits. At a common sequent this decides equality.
eq-ri : ∀ {S Γ A} → S ∣ Γ ⊢ri A → ∀ {T Δ B} → T ∣ Δ ⊢ri B → Bool
eq-li : ∀ {S Γ C} → S ∣ Γ ⊢li C → ∀ {T Δ D} → T ∣ Δ ⊢li D → Bool
eq-f  : ∀ {S Γ C} → S ∣ Γ ⊢f C → ∀ {T Δ D} → T ∣ Δ ⊢f D → Bool

tags-ri-gen : (S : Irr) (Γ Ω : Cxt) {Λ : Cxt} {A : Fma} → irr S ∣ Λ ⊢ri A → Λ ≡ Γ ++ Ω → List Tag

tags-ri : (S : Irr) {Γ : Cxt} {A : Fma} → irr S ∣ Γ ⊢ri A → List Tag

isOK : List Tag → Set
isOKC₁ isOKC₂ : List Tag → Set
isOK⊸l : ∀ {A} (Γ : Cxt) → - ∣ Γ ⊢ri A → List Tag → Set

isOK⊸l-compare : ∀ {A B Λ Δ} → - ∣ Λ ⊢ri A → - ∣ Δ ⊢ri B → List Tag → Set

data _∣_⊢ri_ where
  ∧r : ∀ {S Γ A B} → S ∣ Γ ⊢ri A → S ∣ Γ ⊢ri B → S ∣ Γ ⊢ri A ∧ B
  ⊸r : ∀ {S Γ A B} → S ∣ Γ ++ A ∷ [] ⊢ri B → S ∣ Γ ⊢ri A ⊸ B
  li2ri : ∀ {S Γ C} → S ∣ Γ ⊢li C → S ∣ Γ ⊢ri pos C

data _∣_⊢li_ where
  Il : ∀ {Γ C} → - ∣ Γ ⊢li C → just I ∣ Γ ⊢li C
  ⊗l : ∀ {Γ A B C} → just A ∣ B ∷ Γ ⊢li C → just (A ⊗ B) ∣ Γ ⊢li C
  ∨l : ∀ {Γ A B C} → just A ∣ Γ ⊢li C → just B ∣ Γ ⊢li C → just (A ∨ B) ∣ Γ ⊢li C
  f2li : ∀ {S Γ C} → S ∣ Γ ⊢f C → irr S ∣ Γ ⊢li C

data _∣_⊢f_ where
  ax : ∀ {X} → (just (` X) , tt) ∣ [] ⊢f (` X , tt)
  Ir : (- , tt) ∣ [] ⊢f (I , tt)
  pass : ∀ {Γ A C} → just A ∣ Γ ⊢li C → (- , tt) ∣ A ∷ Γ ⊢f C
  ∧l₁ : ∀ {Γ A B C} → just A ∣ Γ ⊢li C → (just (A ∧ B) , tt) ∣ Γ ⊢f C
  ∧l₂ : ∀ {Γ A B C} → just B ∣ Γ ⊢li C → (just (A ∧ B) , tt) ∣ Γ ⊢f C
  ⊸l : ∀ {Γ Δ Γ' A B C} → (eq : Γ' ≡ Γ ++ Δ)
    → - ∣ Γ ⊢ri A → just B ∣ Δ ⊢li C → (just (A ⊸ B) , tt) ∣ Γ' ⊢f C
  ⊗r : ∀ {S Γ Δ Γ' A B} → (eq : Γ' ≡ Γ ++ Δ)
    → (f : irr S ∣ Γ ⊢ri A) → - ∣ Δ ⊢ri B
    → .(ok : isOK (tags-ri S f)) → S ∣ Γ' ⊢f (A ⊗ B , tt)
  ∨r₁ : ∀ {S Γ A B} → (f : irr S ∣ Γ ⊢ri A)
    → .(ok : isOK (tags-ri S f)) → S ∣ Γ ⊢f (A ∨ B , tt)
  ∨r₂ : ∀ {S Γ A B} → (f : irr S ∣ Γ ⊢ri B)
    → .(ok : isOK (tags-ri S f)) → S ∣ Γ ⊢f (A ∨ B , tt)

tag-f Γ Ω ax eq = R
tag-f Γ Ω Ir eq = R
tag-f [] Ω (pass f) eq = •
tag-f (x ∷ Γ) Ω (pass f) eq = P
tag-f Γ Ω (∧l₁ f) eq = C₁
tag-f Γ Ω (∧l₂ f) eq = C₂
tag-f Γ [] (⊸l {Γ₁} {Δ} eq₁ f g) eq = ⊸l Γ₁ f
tag-f Γ (A ∷ Ω) (⊸l {Γ₁} {Δ} eq₁ f g) refl with cases++ Γ Γ₁ Ω Δ (sym eq₁)
... | inj₁ _ = •
... | inj₂ _ = ⊸l Γ₁ f
tag-f Γ Ω (⊗r eq₁ f g ok) eq = R
tag-f Γ Ω (∨r₁ f ok) eq = R
tag-f Γ Ω (∨r₂ f ok) eq = R

tags-ri-gen S Γ Ω (∧r f g) eq = tags-ri-gen S Γ Ω f eq ++ tags-ri-gen S Γ Ω g eq
tags-ri-gen S Γ Ω (⊸r {A = A} f) eq = tags-ri-gen S Γ (Ω ++ [ A ]) f (trans (cong (_++ [ A ]) eq) (++ass Γ))
tags-ri-gen S Γ Ω (li2ri (f2li f)) eq = [ tag-f Γ Ω f eq ]

tags-ri S {Γ} f = tags-ri-gen S Γ [] f (sym (++ru Γ))

isOK [] = ⊥
isOK (• ∷ ts) = ⊤
isOK (R ∷ ts) = ⊤
isOK (P ∷ ts) = isOK ts
isOK (C₁ ∷ ts) = isOKC₁ ts
isOK (C₂ ∷ ts) = isOKC₂ ts
isOK (⊸l Γ f ∷ ts) = isOK⊸l Γ f ts

isOKC₁ (• ∷ ts) = ⊤
isOKC₁ (R ∷ ts) = ⊤
isOKC₁ (C₂ ∷ ts) = ⊤
isOKC₁ (C₁ ∷ ts) = isOKC₁ ts
isOKC₁ _ = ⊥

isOKC₂ (• ∷ ts) = ⊤
isOKC₂ (R ∷ ts) = ⊤
isOKC₂ (C₁ ∷ ts) = ⊤
isOKC₂ (C₂ ∷ ts) = isOKC₂ ts
isOKC₂ _ = ⊥

isOK⊸l Γ f (• ∷ ts) = ⊤
isOK⊸l Γ f (R ∷ ts) = ⊤
isOK⊸l Γ f (⊸l Δ g ∷ ts) = isOK⊸l-compare f g ts
isOK⊸l Γ f _ = ⊥

-- In a list from tags-ri, Λ and Δ are prefixes of the same unmarked context.
-- Two prefixes of length n contain the first n formulae of that context in order.
isOK⊸l-compare {Λ = Λ} {Δ} f g ts with length≟ Λ Δ
... | no _ = ⊤
... | yes _ with eq-ri f g
...   | false = ⊤
...   | true  = isOK⊸l Λ f ts

eq-ri (∧r f g) (∧r f' g') = eq-ri f f' ∧ᵇ eq-ri g g'
eq-ri (⊸r f) (⊸r g) = eq-ri f g
eq-ri (li2ri f) (li2ri g) = eq-li f g
eq-ri _ _ = false

eq-li (Il f) (Il g) = eq-li f g
eq-li (⊗l f) (⊗l g) = eq-li f g
eq-li (∨l f g) (∨l f' g') = eq-li f f' ∧ᵇ eq-li g g'
eq-li (f2li f) (f2li g) = eq-f f g
eq-li _ _ = false

eq-f ax ax = true
eq-f Ir Ir = true
eq-f (pass f) (pass g) = eq-li f g
eq-f (∧l₁ f) (∧l₁ g) = eq-li f g
eq-f (∧l₂ f) (∧l₂ g) = eq-li f g
eq-f (⊸l {Γ} _ f g) (⊸l {Δ} _ f' g') with length≟ Γ Δ
... | no _ = false
... | yes _ = eq-ri f f' ∧ᵇ eq-li g g'
eq-f (⊗r {Γ = Γ} _ f g _) (⊗r {Γ = Δ} _ f' g' _) with length≟ Γ Δ
... | no _ = false
... | yes _ = eq-ri f f' ∧ᵇ eq-ri g g'
eq-f (∨r₁ f _) (∨r₁ g _) = eq-ri f g
eq-f (∨r₂ f _) (∨r₂ g _) = eq-ri f g
eq-f _ _ = false
