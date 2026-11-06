{-# OPTIONS --safe #-}

module Utilities where

open import Data.Empty
open import Data.Sum.Base
open import Data.List.Base hiding (head)
import Data.Nat.Base as ℕ
open import Data.List.Relation.Unary.All as LA using ()
open import Data.Product.Base
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality.Core




-- uniqueness of identity proofs

uip : {A : Set} → {a a' : A} → {p p' : a ≡ a'} → p ≡ p' 
uip {_} {.a} {a} {refl} {refl} = refl

-- Some lemmata about lists for reasoning about contexts

++ru : {X : Set} → (xs : List X) → xs ++ [] ≡ xs
++ru [] = refl
++ru (x ∷ xs) = cong (_∷_ x) (++ru xs) 

++ass : {X : Set} → (xs : List X) → {ys zs : List X} → 
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++ass [] = refl
++ass (x ∷ xs) = cong (_∷_ x) (++ass xs)



inj∷ : {X : Set} → {x y : X} → {xs ys : List X} → 
           x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
inj∷ refl = refl , refl

[]disj∷ : {X : Set} → (xs : List X) → {ys : List X} → {x : X} →  
             [] ≡ xs ++ x ∷ ys → ⊥
[]disj∷ [] ()
[]disj∷ (x ∷ xs) ()

cases∷ : {X : Set} → (xs : List X) → {ys ys' : List X} → {x x' : X} → 
   x' ∷ ys' ≡ xs ++ x ∷ ys → 
        (x ≡ x' × xs ≡ [] × ys ≡ ys')  
        ⊎ Σ (List X) 
               (λ xs₀  → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ x' ∷ xs₀) 
cases∷ [] refl = inj₁ (refl , refl , refl)
cases∷ (x₀ ∷ xs) {ys} {.(xs ++ x ∷ ys)} {x} {.x₀} refl = inj₂ (xs , refl , refl)

cases++ : {X : Set} → (xs xs' ys ys' : List X) → {x : X} → 
   xs' ++ ys' ≡ xs ++ x ∷ ys → 
       Σ (List X) (λ xs₀ → xs' ≡ xs ++ x ∷ xs₀ × ys ≡ xs₀ ++ ys')  
     ⊎ Σ (List X) (λ xs₀ → ys' ≡ xs₀ ++ x ∷ ys × xs ≡ xs' ++ xs₀) 
cases++ xs [] _ _ refl = inj₂ (xs , refl , refl)
cases++ [] (x' ∷ xs') _ _ refl = inj₁ (xs' , refl , refl)
cases++ (x₀ ∷ xs) (x' ∷ xs') ys ys' {x} p with inj∷ p
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q with cases++ xs xs' ys ys' q 
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₁ (xs₀ , r , r') = inj₁ (xs₀ , cong₂ _∷_ refl r , r')
cases++ (.x' ∷ xs) (x' ∷ xs') ys ys' p | refl , q | inj₂ (xs₀ , r , r') = inj₂ (xs₀ , r , cong₂ _∷_ refl r')

-- Compare the two prefix lengths by walking the lists together.
length≟ : {X : Set} (xs ys : List X) → Dec (length xs ≡ length ys)
length≟ [] [] = yes refl
length≟ [] (_ ∷ _) = no λ ()
length≟ (_ ∷ _) [] = no λ ()
length≟ (_ ∷ xs) (_ ∷ ys) with length≟ xs ys
... | yes eq = yes (cong ℕ.suc eq)
... | no neq = no (λ eq → neq (cong ℕ.pred eq))

length≟-refl : {X : Set} (xs : List X) → length≟ xs xs ≡ yes refl
length≟-refl [] = refl
length≟-refl (_ ∷ xs) rewrite length≟-refl xs = refl

-- Equal split positions in the same context give equal prefixes and suffixes.
split-at-length : {X : Set} (Γ Γ' : List X) {Δ Δ' : List X} →
  Γ ++ Δ ≡ Γ' ++ Δ' → length Γ ≡ length Γ' → Γ ≡ Γ' × Δ ≡ Δ'
split-at-length [] [] eq _ = refl , eq
split-at-length [] (_ ∷ _) _ ()
split-at-length (_ ∷ _) [] _ ()
split-at-length (A ∷ Γ) (B ∷ Γ') {Δ} {Δ'} eq len with inj∷ eq
... | refl , p with split-at-length Γ Γ' {Δ} {Δ'} p (cong ℕ.pred len)
...   | same , rest = cong (A ∷_) same , rest

-- Compare two splittings of the same context.
split≟ : {X : Set} (Γ Δ Γ' Δ' : List X)
  → Γ ++ Δ ≡ Γ' ++ Δ' → Dec (Γ ≡ Γ' × Δ ≡ Δ')
split≟ Γ Δ Γ' Δ' eq with length≟ Γ Γ'
... | no n = no (λ { (refl , _) → n refl })
... | yes len = yes (split-at-length Γ Γ' {Δ} {Δ'} eq len)

All++ : {A : Set} {xs ys : List A} {P : A → Set} → LA.All P xs → LA.All P ys → LA.All P (xs ++ ys)
All++ LA.[] ys = ys
All++ (p LA.∷ xs) ys = p LA.∷ All++ xs ys

++canc : {A : Set} (xs : List A) {ys zs : List A} → xs ++ ys ≡ xs ++ zs → ys ≡ zs
++canc [] eq = eq
++canc (x ∷ xs) eq = ++canc xs (proj₂ (inj∷ eq))

cases++-inj₁ : {X : Set} (Γ Δ Ξ : List X) (D : X)
  → (eq : (Γ ++ D ∷ Δ) ++ Ξ ≡ Γ ++ D ∷ (Δ ++ Ξ))
  → cases++ Γ (Γ ++ D ∷ Δ) (Δ ++ Ξ) Ξ eq ≡ inj₁ (Δ , refl , refl)
cases++-inj₁ [] Δ Ξ D refl = refl
cases++-inj₁ (A ∷ Γ) Δ Ξ D eq with inj∷ eq
... | refl , q rewrite cases++-inj₁ Γ Δ Ξ D q = refl

cases++-inj₂ : {X : Set} (xs xs' ys : List X) (x : X)
  → (eq : xs' ++ (xs ++ x ∷ ys) ≡ (xs' ++ xs) ++ x ∷ ys)
  → cases++ (xs' ++ xs) xs' ys (xs ++ x ∷ ys) eq ≡ inj₂ (xs , refl , refl)
cases++-inj₂ xs [] ys x refl = refl
cases++-inj₂ xs (A ∷ xs') ys x eq with inj∷ eq
... | refl , q rewrite cases++-inj₂ xs xs' ys x q = refl

subst₂-refl₁ : {A B : Set} {P : A → B → Set} {a : A} {b b' : B}
  → (p : b ≡ b') (x : P a b) → subst₂ P refl p x ≡ subst (P a) p x
subst₂-refl₁ refl x = refl

empty++1 : {A : Set} (xs : List A) {ys : List A} → xs ++ ys ≡ [] → xs ≡ []
empty++1 [] eq = refl
empty++1 (x ∷ xs) ()

split≟-refl : ∀ {X : Set} (Γ Δ : List X) → split≟ Γ Δ Γ Δ refl ≡ yes (refl , refl)
split≟-refl Γ Δ with split≟ Γ Δ Γ Δ refl
... | no n = ⊥-elim (n (refl , refl))
... | yes (p , q) rewrite uip {p = p} {refl} | uip {p = q} {refl} = refl

-- Nonempty binary trees preserve the branching of iterated conjunction-right.
data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

-- A family of witnesses with the same shape as the underlying tree.
data All {A : Set} (P : A → Set) : Tree A → Set where
  leaf  : {x : A} → P x → All P (leaf x)
  node : ∀ {t u} (pt : All P t) (pu : All P u) → All P (node t u)

mapAll : {A : Set} {P Q : A → Set}
  → (∀ {x} → P x → Q x)
  → ∀ {xs} → All P xs → All Q xs
mapAll fs (leaf p) = leaf (fs p)
mapAll fs (node pxs pys) = node (mapAll fs pxs) (mapAll fs pys)

map2All : {A : Set} {P Q R : A → Set}
  → (∀ {x} → P x → Q x → R x)
  → ∀ {xs} → All P xs → All Q xs → All R xs
map2All fs (leaf p) (leaf q) = leaf (fs p q)
map2All fs (node pxs pys) (node qxs qys) = node (map2All fs pxs qxs) (map2All fs pys qys)

head : {A : Set} → Tree A → A
head (leaf x) = x
head (node xs ys) = head xs

headAll : {A : Set} {P : A → Set} {xs : Tree A} → All P xs → P (head xs)
headAll (leaf f) = f
headAll (node fs gs) = headAll fs

headAll-map : {A : Set} {P Q : A → Set} (m : ∀ {x} → P x → Q x)
  → ∀ {xs} (fs : All P xs) → headAll (mapAll m fs) ≡ m (headAll fs)
headAll-map m (leaf f) = refl
headAll-map m (node fs gs) = headAll-map m fs

headAll-map2 : {A : Set} {P Q R : A → Set} (m : ∀ {x} → P x → Q x → R x)
  → ∀ {xs} (fs : All P xs) (gs : All Q xs) → headAll (map2All m fs gs) ≡ m (headAll fs) (headAll gs)
headAll-map2 m (leaf f) (leaf g) = refl
headAll-map2 m (node fs gs) (node hs ks) = headAll-map2 m fs hs
