{-# OPTIONS --safe #-}

module Utilities where

open import Data.List
open import Data.Product
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty
import Data.List.Relation.Unary.All as LA
open import Relation.Binary.PropositionalEquality hiding ([_])

-- Nonempty binary trees preserve the branching of iterated conjunction-right.
data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

-- One adjacent exchange: swap the first two occurrences, or retain
-- the common head and exchange two occurrences in the tails.
data Swap {X : Set} : List X → List X → Set where
  sw : ∀ {A B Γ} → Swap (A ∷ B ∷ Γ) (B ∷ A ∷ Γ)
  keep : ∀ {A Γ Δ} → Swap Γ Δ → Swap (A ∷ Γ) (A ∷ Δ)

-- The two paths in an adjacent braid, possibly below common heads.
data Braid {X : Set} : ∀ {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂ : List X}
  → Swap Γ Δ₁ → Swap Δ₁ Δ₂ → Swap Δ₂ Θ
  → Swap Γ Ξ₁ → Swap Ξ₁ Ξ₂ → Swap Ξ₂ Θ → Set where
  braid : ∀ {A B C Γ} → Braid
    (sw {A = A} {B = B} {Γ = C ∷ Γ}) (keep sw) sw (keep sw) sw (keep sw)
  keep-braid : ∀ {A Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂}
    {σ₁ : Swap Γ Δ₁} {σ₂ : Swap Δ₁ Δ₂} {σ₃ : Swap Δ₂ Θ}
    {τ₁ : Swap Γ Ξ₁} {τ₂ : Swap Ξ₁ Ξ₂} {τ₃ : Swap Ξ₂ Θ}
    → Braid σ₁ σ₂ σ₃ τ₁ τ₂ τ₃
    → Braid (keep {A = A} σ₁) (keep σ₂) (keep σ₃) (keep τ₁) (keep τ₂) (keep τ₃)

-- Two disjoint exchanges may be performed in either order.
data Disjoint {X : Set} : ∀ {Γ Δ Ξ Θ : List X}
  → Swap Γ Δ → Swap Δ Θ → Swap Γ Ξ → Swap Ξ Θ → Set where
  disjoint : ∀ {A B Γ Δ} (σ : Swap Γ Δ)
    → Disjoint (sw {A = A} {B = B}) (keep (keep σ)) (keep (keep σ)) sw
  keep-disjoint : ∀ {A Γ Δ Ξ Θ}
    {σ₁ : Swap Γ Δ} {σ₂ : Swap Δ Θ} {τ₁ : Swap Γ Ξ} {τ₂ : Swap Ξ Θ}
    → Disjoint σ₁ σ₂ τ₁ τ₂
    → Disjoint (keep {A = A} σ₁) (keep σ₂) (keep τ₁) (keep τ₂)

swap-sym : ∀ {X : Set} {Γ Δ : List X} → Swap Γ Δ → Swap Δ Γ
swap-sym sw = sw
swap-sym (keep σ) = keep (swap-sym σ)

-- Partition a list into two subsequences, preserving the order of each.
-- The witness records which side receives each occurrence, so repeated
-- formulae do not require decidable equality or lose their occurrence identity.
data Part {A : Set} : List A → List A → List A → Set where
  done : Part [] [] []
  left : ∀ {x xs ys zs} → Part xs ys zs → Part (x ∷ xs) ys (x ∷ zs)
  right : ∀ {x xs ys zs} → Part xs ys zs → Part xs (x ∷ ys) (x ∷ zs)

-- Concatenate two partitions, preserving the allocation of each prefix.
part++ : ∀ {X : Set} {Λ Ω Ξ Λ' Ω' Ξ' : List X}
  → Part Λ Ω Ξ → Part Λ' Ω' Ξ' → Part (Λ ++ Λ') (Ω ++ Ω') (Ξ ++ Ξ')
part++ done r = r
part++ (left t) r = left (part++ t r)
part++ (right t) r = right (part++ t r)

-- Every original contiguous context split is a partition.
part : ∀ {A : Set} (xs ys : List A) → Part xs ys (xs ++ ys)
part [] [] = done
part [] (y ∷ ys) = right (part [] ys)
part (x ∷ xs) ys = left (part xs ys)

-- Selecting one occurrence, with the order of all remaining occurrences fixed.
data Pick {A : Set} (a : A) : List A → List A → Set where
  here : ∀ {xs} → Pick a (a ∷ xs) xs
  there : ∀ {b xs ys} → Pick a xs ys → Pick a (b ∷ xs) (b ∷ ys)

pick-prefix : ∀ {A : Set} (xs : List A) {a ys} → Pick a (xs ++ a ∷ ys) (xs ++ ys)
pick-prefix [] = here
pick-prefix (x ∷ xs) = there (pick-prefix xs)

-- Appending an untouched suffix preserves the selected occurrence.
pick-post : ∀ {A : Set} {X : A} {Γ Ω} → Pick X Γ Ω → (Δ : List A) → Pick X (Γ ++ Δ) (Ω ++ Δ)
pick-post here Δ = here
pick-post (there q) Δ = there (pick-post q Δ)

-- Removing an occurrence assigned to the left tensor premise removes that
-- very occurrence from the conclusion partition as well.
pull-left : ∀ {A : Set} {a : A} {xs ys zs xs'}
  → Part xs ys zs → Pick a xs xs'
  → Σ (List A) λ zs' → Pick a zs zs' × Part xs' ys zs'
pull-left (left p) here = _ , here , p
pull-left (left p) (there q) with pull-left p q
... | zs' , r , p' = _ ∷ zs' , there r , left p'
pull-left (right p) q with pull-left p q
... | zs' , r , p' = _ ∷ zs' , there r , right p'

-- Expose the recursive result beneath a partition constructor without
-- matching on a proof that uses that result.
pull-left-left : ∀ {X : Set} {A B : X} {Γ Δ Θ Γ'} (p : Part Γ Δ Θ) (q : Pick A Γ Γ')
  → pull-left (left {x = B} p) (there q)
    ≡ let t = pull-left p q in B ∷ proj₁ t , there (proj₁ (proj₂ t)) , left (proj₂ (proj₂ t))
pull-left-left p q with pull-left p q
... | _ , _ , _ = refl

pull-left-right : ∀ {X : Set} {A B : X} {Γ Δ Θ Γ'} (p : Part Γ Δ Θ) (q : Pick A Γ Γ')
  → pull-left (right {x = B} p) q
    ≡ let t = pull-left p q in B ∷ proj₁ t , there (proj₁ (proj₂ t)) , right (proj₂ (proj₂ t))
pull-left-right p q with pull-left p q
... | _ , _ , _ = refl

-- Extending a swap by contexts preserves its location.
swap-pre : ∀ {X : Set} (Λ : List X) {Γ Δ} → Swap Γ Δ → Swap (Λ ++ Γ) (Λ ++ Δ)
swap-pre [] σ = σ
swap-pre (_ ∷ Λ) σ = keep (swap-pre Λ σ)

swap-post : ∀ {X : Set} {Γ Δ} → Swap Γ Δ → (Λ : List X) → Swap (Γ ++ Λ) (Δ ++ Λ)
swap-post sw Λ = sw
swap-post (keep σ) Λ = keep (swap-post σ Λ)

-- Prefixes accumulated in reverse order avoid associativity transports
-- while traversing a selection or partition from left to right.
infixr 5 _ᴿ++_

_ᴿ++_ : ∀ {X : Set} → List X → List X → List X
[] ᴿ++ Γ = Γ
(A ∷ Λ) ᴿ++ Γ = Λ ᴿ++ (A ∷ Γ)

pickᴿ++ : ∀ {X : Set} (Λ : List X) {A Γ Δ} → Pick A Γ Δ → Pick A (Λ ᴿ++ Γ) (Λ ᴿ++ Δ)
pickᴿ++ [] p = p
pickᴿ++ (A ∷ Λ) p = pickᴿ++ Λ (there p)

swapᴿ++ : ∀ {X : Set} (Λ : List X) {Γ Δ} → Swap Γ Δ → Swap (Λ ᴿ++ Γ) (Λ ᴿ++ Δ)
swapᴿ++ [] σ = σ
swapᴿ++ (A ∷ Λ) σ = swapᴿ++ Λ (keep σ)

-- Reversing an exchange commutes with extending its fixed prefix.
swap-symᴿ++ : ∀ {X : Set} (Λ : List X) {Γ Δ} (σ : Swap Γ Δ)
  → swap-sym (swapᴿ++ Λ σ) ≡ swapᴿ++ Λ (swap-sym σ)
swap-symᴿ++ [] σ = refl
swap-symᴿ++ (B ∷ Λ) σ = swap-symᴿ++ Λ (keep σ)

partᴿ++ : ∀ {X : Set} {Λ Ω Ξ Γ Δ Θ : List X}
  → Part Λ Ω Ξ → Part Γ Δ Θ → Part (Λ ᴿ++ Γ) (Ω ᴿ++ Δ) (Ξ ᴿ++ Θ)
partᴿ++ done p = p
partᴿ++ (left r) p = partᴿ++ r (left p)
partᴿ++ (right r) p = partᴿ++ r (right p)

-- Selecting in an accumulated prefix, rather than in its suffix.
pick-prefixᴿ++ : ∀ {X : Set} {A : X} {Λ Λ'} → Pick A Λ Λ' → (Γ : List X)
  → Pick A (Λ ᴿ++ Γ) (Λ' ᴿ++ Γ)
pick-prefixᴿ++ (here {xs = Λ}) Γ = pickᴿ++ Λ here
pick-prefixᴿ++ (there {b = B} q) Γ = pick-prefixᴿ++ q (B ∷ Γ)

-- Pulling a suffix selection through the accumulated partition leaves
-- the accumulated prefix unchanged.
pull-leftᴿ++ : ∀ {X : Set} {A : X} {Λ Ω Ξ Γ Δ Θ Γ'}
  (r : Part Λ Ω Ξ) (p : Part Γ Δ Θ) (q : Pick A Γ Γ')
  → pull-left (partᴿ++ r p) (pickᴿ++ Λ q)
    ≡ let t = pull-left p q in
      Ξ ᴿ++ proj₁ t , pickᴿ++ Ξ (proj₁ (proj₂ t)) , partᴿ++ r (proj₂ (proj₂ t))
pull-leftᴿ++ done p q = refl
pull-leftᴿ++ {Ξ = _ ∷ Ξ} (left r) p q = trans (pull-leftᴿ++ r (left p) (there q))
  (cong (λ t → Ξ ᴿ++ proj₁ t , pickᴿ++ Ξ (proj₁ (proj₂ t)) , partᴿ++ r (proj₂ (proj₂ t)))
    (pull-left-left p q))
pull-leftᴿ++ {Ξ = _ ∷ Ξ} (right r) p q = trans (pull-leftᴿ++ r (right p) q)
  (cong (λ t → Ξ ᴿ++ proj₁ t , pickᴿ++ Ξ (proj₁ (proj₂ t)) , partᴿ++ r (proj₂ (proj₂ t)))
    (pull-left-right p q))

-- A selection in the prefix instead removes one occurrence from the
-- prefix partition, leaving the suffix partition unchanged.
pull-left-prefixᴿ++ : ∀ {X : Set} {A : X} {Λ Λ' Ω Ξ Γ Δ Θ}
  (r : Part Λ Ω Ξ) (q : Pick A Λ Λ') (p : Part Γ Δ Θ)
  → pull-left (partᴿ++ r p) (pick-prefixᴿ++ q Γ)
    ≡ let t = pull-left r q in
      proj₁ t ᴿ++ Θ , pick-prefixᴿ++ (proj₁ (proj₂ t)) Θ , partᴿ++ (proj₂ (proj₂ t)) p
pull-left-prefixᴿ++ (left r) here p = pull-leftᴿ++ r (left p) here
pull-left-prefixᴿ++ {Θ = Θ} (left r) (there q) p = trans (pull-left-prefixᴿ++ r q (left p))
  (sym (cong (λ t → proj₁ t ᴿ++ Θ , pick-prefixᴿ++ (proj₁ (proj₂ t)) Θ , partᴿ++ (proj₂ (proj₂ t)) p)
    (pull-left-left r q)))
pull-left-prefixᴿ++ {Θ = Θ} (right r) q p = trans (pull-left-prefixᴿ++ r q (right p))
  (sym (cong (λ t → proj₁ t ᴿ++ Θ , pick-prefixᴿ++ (proj₁ (proj₂ t)) Θ , partᴿ++ (proj₂ (proj₂ t)) p)
    (pull-left-right r q)))

-- Append one formula to a reversed prefix: it becomes the first formula
-- of the completed context. This is the prefix change made by tensor-left.
ᴿ++-snoc : ∀ {X : Set} (Λ : List X) (B : X) (Γ : List X)
  → (Λ ++ [ B ]) ᴿ++ Γ ≡ B ∷ (Λ ᴿ++ Γ)
ᴿ++-snoc [] B Γ = refl
ᴿ++-snoc (A ∷ Λ) B Γ = ᴿ++-snoc Λ B (A ∷ Γ)

part-snoc-left : ∀ {X : Set} {Λ Ω Ξ : List X} → Part Λ Ω Ξ → (B : X)
  → Part (Λ ++ [ B ]) Ω (Ξ ++ [ B ])
part-snoc-left done B = left done
part-snoc-left (left r) B = left (part-snoc-left r B)
part-snoc-left (right r) B = right (part-snoc-left r B)

partᴿ++-snoc-left : ∀ {X : Set} {Λ Ω Ξ Γ Δ Θ : List X}
  (r : Part Λ Ω Ξ) (B : X) (p : Part Γ Δ Θ)
  → subst₂ (λ Γ Θ → Part Γ (Ω ᴿ++ Δ) Θ) (ᴿ++-snoc Λ B Γ) (ᴿ++-snoc Ξ B Θ)
      (partᴿ++ (part-snoc-left r B) p) ≡ left (partᴿ++ r p)
partᴿ++-snoc-left done B p = refl
partᴿ++-snoc-left (left r) B p = partᴿ++-snoc-left r B (left p)
partᴿ++-snoc-left (right r) B p = partᴿ++-snoc-left r B (right p)

swapᴿ++-snoc : ∀ {X : Set} (Λ : List X) (B : X) {Γ Δ} (σ : Swap Γ Δ)
  → subst₂ Swap (ᴿ++-snoc Λ B Γ) (ᴿ++-snoc Λ B Δ) (swapᴿ++ (Λ ++ [ B ]) σ)
    ≡ keep (swapᴿ++ Λ σ)
swapᴿ++-snoc [] B σ = refl
swapᴿ++-snoc (A ∷ Λ) B σ = swapᴿ++-snoc Λ B (keep σ)

-- Exchange occurrences inside an accumulated (reversed) prefix.
swap-prefixᴿ++ : ∀ {X : Set} {Λ Λ' : List X} → Swap Λ Λ' → (Γ : List X)
  → Swap (Λ ᴿ++ Γ) (Λ' ᴿ++ Γ)
swap-prefixᴿ++ (sw {Γ = Λ}) Γ = swapᴿ++ Λ sw
swap-prefixᴿ++ (keep {A = A} ρ) Γ = swap-prefixᴿ++ ρ (A ∷ Γ)

disjointᴿ++ : ∀ {X : Set} (Λ : List X) {Γ Δ Ξ Θ}
  {σ₁ : Swap Γ Δ} {σ₂ : Swap Δ Θ} {τ₁ : Swap Γ Ξ} {τ₂ : Swap Ξ Θ}
  → Disjoint σ₁ σ₂ τ₁ τ₂
  → Disjoint (swapᴿ++ Λ σ₁) (swapᴿ++ Λ σ₂) (swapᴿ++ Λ τ₁) (swapᴿ++ Λ τ₂)
disjointᴿ++ [] d = d
disjointᴿ++ (A ∷ Λ) d = disjointᴿ++ Λ (keep-disjoint d)

-- A swap in the fixed prefix is disjoint from a swap in the suffix.
disjoint-prefixᴿ++ : ∀ {X : Set} {Λ Λ' Γ Δ : List X} (ρ : Swap Λ Λ') (σ : Swap Γ Δ)
  → Disjoint (swap-prefixᴿ++ ρ Γ) (swapᴿ++ Λ' σ)
      (swapᴿ++ Λ σ) (swap-prefixᴿ++ ρ Δ)
disjoint-prefixᴿ++ (sw {Γ = Λ}) σ = disjointᴿ++ Λ (disjoint σ)
disjoint-prefixᴿ++ (keep ρ) σ = disjoint-prefixᴿ++ ρ (keep σ)

-- Lift all six exchanges of a braid beneath a reversed prefix.
braidᴿ++ : ∀ {X : Set} (Λ : List X) {Γ Δ₁ Δ₂ Θ Ξ₁ Ξ₂}
  {σ₁ : Swap Γ Δ₁} {σ₂ : Swap Δ₁ Δ₂} {σ₃ : Swap Δ₂ Θ}
  {τ₁ : Swap Γ Ξ₁} {τ₂ : Swap Ξ₁ Ξ₂} {τ₃ : Swap Ξ₂ Θ}
  → Braid σ₁ σ₂ σ₃ τ₁ τ₂ τ₃
  → Braid (swapᴿ++ Λ σ₁) (swapᴿ++ Λ σ₂) (swapᴿ++ Λ σ₃)
      (swapᴿ++ Λ τ₁) (swapᴿ++ Λ τ₂) (swapᴿ++ Λ τ₃)
braidᴿ++ [] b = b
braidᴿ++ (A ∷ Λ) b = braidᴿ++ Λ (keep-braid b)

-- Reassociating append with a reversed accumulated prefix.
ᴿ++-++ : ∀ {X : Set} (Λ Γ Δ : List X) → (Λ ᴿ++ Γ) ++ Δ ≡ Λ ᴿ++ (Γ ++ Δ)
ᴿ++-++ [] Γ Δ = refl
ᴿ++-++ (A ∷ Λ) Γ Δ = ᴿ++-++ Λ (A ∷ Γ) Δ

-- Further context utilities and tree-indexed families used by focusing.
empty++1 : {A : Set} (xs : List A) {ys : List A} → xs ++ ys ≡ [] → xs ≡ []
empty++1 [] eq = refl

-- A list containing a specified occurrence cannot be empty.
[]disj∷ : ∀ {A : Set} (pre : List A) {a suf} → pre ++ a ∷ suf ≡ [] → ⊥
[]disj∷ [] ()
[]disj∷ (_ ∷ _) ()

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

-- Recover the prefix presentation when interfacing with older proofs.
swap-view : ∀ {X : Set} {Γ Δ : List X} → Swap Γ Δ
  → Σ (List X) λ Λ → Σ X λ A → Σ X λ B → Σ (List X) λ Ξ
    → Γ ≡ Λ ++ A ∷ B ∷ Ξ × Δ ≡ Λ ++ B ∷ A ∷ Ξ
swap-view sw = [] , _ , _ , _ , refl , refl
swap-view (keep {A = A} σ) with swap-view σ
... | Λ , B , C , Ξ , refl , refl = A ∷ Λ , B , C , Ξ , refl , refl

swap-view-prefix : ∀ {X : Set} (Γ : List X) {A B Δ}
  → swap-view (swap-pre Γ (sw {A = A} {B = B} {Γ = Δ})) ≡ (Γ , A , B , Δ , refl , refl)
swap-view-prefix [] = refl
swap-view-prefix (x ∷ Γ) {A} {B} {Δ} rewrite swap-view-prefix Γ {A} {B} {Δ} = refl

-- The tag of pass records the selected occurrence, counted from zero.
pick-index : ∀ {X : Set} {a : X} {Γ Δ} → Pick a Γ Δ → ℕ
pick-index here = zero
pick-index (there p) = suc (pick-index p)

-- Equal indices in one context identify the selected formula, the
-- remaining context, and the selection witness, even with repetitions.
same-pick : ∀ {X : Set} {a b : X} {Γ Δ Ξ}
  (p : Pick a Γ Δ) (q : Pick b Γ Ξ) → pick-index p ≡ pick-index q
  → _≡_ {A = Σ X λ x → Σ (List X) λ ys → Pick x Γ ys} (a , Δ , p) (b , Ξ , q)
same-pick here here eq = refl
same-pick here (there q) ()
same-pick (there p) here ()
same-pick (there p) (there q) eq with same-pick p q (suc-injective eq)
... | refl = refl

-- Two selections either choose the same occurrence or commute. This
-- lets insertion retain every existing pass choice, including repetitions.
ex-pickR : ∀ {X : Set} {A B : X} {Γ Γ' Δ' : List X} → Pick A Γ' Γ → Pick B Γ' Δ'
  → (A ≡ B × Γ ≡ Δ') ⊎ (Σ (List X) λ Δ → Pick B Γ Δ × Pick A Δ' Δ)
ex-pickR here here = inj₁ (refl , refl)
ex-pickR here (there q) = inj₂ (_ , q , here)
ex-pickR (there p) here = inj₂ (_ , here , p)
ex-pickR (there p) (there q) with ex-pickR p q
... | inj₁ (refl , refl) = inj₁ (refl , refl)
... | inj₂ (Δ , q' , p') = inj₂ (_ ∷ Δ , there q' , there p')

-- Concatenation and splitting of list-indexed families of witnesses.
all++ : ∀ {A : Set} {P : A → Set} {xs ys} → LA.All P xs → LA.All P ys → LA.All P (xs ++ ys)
all++ LA.[] qs = qs
all++ (p LA.∷ ps) qs = p LA.∷ all++ ps qs

splitAll : ∀ {A : Set} {P : A → Set} (xs : List A) {ys} (ps : LA.All P (xs ++ ys))
  → Σ (LA.All P xs) λ qs → Σ (LA.All P ys) λ rs → ps ≡ all++ qs rs
splitAll [] ps = LA.[] , ps , refl
splitAll (x ∷ xs) (p LA.∷ ps) with splitAll xs ps
... | qs , rs , refl = (p LA.∷ qs) , rs , refl

-- Exchange permutes the two positions following a prefix.
swap-index : ℕ → ℕ → ℕ
swap-index zero zero = suc zero
swap-index zero (suc zero) = zero
swap-index zero (suc (suc n)) = suc (suc n)
swap-index (suc k) zero = zero
swap-index (suc k) (suc n) = suc (swap-index k n)

swap-index-iso : ∀ k n → swap-index k (swap-index k n) ≡ n
swap-index-iso zero zero = refl
swap-index-iso zero (suc zero) = refl
swap-index-iso zero (suc (suc n)) = refl
swap-index-iso (suc k) zero = refl
swap-index-iso (suc k) (suc n) = cong suc (swap-index-iso k n)

swap-index-injective : ∀ k {m n} → swap-index k m ≡ swap-index k n → m ≡ n
swap-index-injective k {m} {n} eq = trans (sym (swap-index-iso k m))
  (trans (cong (swap-index k) eq) (swap-index-iso k n))

-- Context transports with the same endpoints agree.
eq-unique : ∀ {X : Set} {x y : X} (p q : x ≡ y) → p ≡ q
eq-unique refl refl = refl

subst-coherent : ∀ {X : Set} (P : X → Set) {x y z}
  (p : x ≡ y) (q : y ≡ z) (r : x ≡ z) (u : P x)
  → subst P q (subst P p u) ≡ subst P r u
subst-coherent P refl refl refl u = refl
