{-# OPTIONS --safe #-}

module FocusSeqCalcProperties (At : Set) where

open import Data.Bool.Base renaming (_∧_ to _∧ᵇ_; _∨_ to _∨ᵇ_)
open import Data.Empty
open import Data.List.Base
open import Agda.Builtin.Maybe
open import Data.Product.Base
open import Agda.Builtin.Unit
open import Relation.Nullary.Decidable.Core
open import Relation.Binary.PropositionalEquality.Core

open import Utilities
open import Fma At
open import FocusSeqCalc At

-- Right-rule congruence used by FocusEmb and by eq-f-sound.

⊗req : ∀ {S Γ Δ Γ' A B} {eq eq' : Γ' ≡ Γ ++ Δ}
  → {f f' : irr S ∣ Γ ⊢ri A} {g g' : - ∣ Δ ⊢ri B}
  → f ≡ f' → g ≡ g'
  → .{ok : isOK (tags-ri S f)}
  → .{ok' : isOK (tags-ri S f')}
  → ⊗r eq f g ok ≡ ⊗r eq' f' g' ok'
⊗req {eq = eq} {eq'} refl refl rewrite uip {p = eq} {eq'} = refl

∨r₁eq : ∀ {S Γ A B} {f f' : irr S ∣ Γ ⊢ri A} → f ≡ f'
  → .{ok : isOK (tags-ri S f)}
  → .{ok' : isOK (tags-ri S f')}
  → ∨r₁ {B = B} f ok ≡ ∨r₁ f' ok'
∨r₁eq refl = refl

∨r₂eq : ∀ {S Γ A B} {f f' : irr S ∣ Γ ⊢ri B} → f ≡ f'
  → .{ok : isOK (tags-ri S f)}
  → .{ok' : isOK (tags-ri S f')}
  → ∨r₂ {A = A} f ok ≡ ∨r₂ f' ok'
∨r₂eq refl = refl

-- Soundness of the comparison used by check-focus in Focus.

∧ᵇ-true : {a b : Bool} → a ∧ᵇ b ≡ true → a ≡ true × b ≡ true
∧ᵇ-true {true} eq = refl , eq
∧ᵇ-true {false} ()

false≢true : false ≡ true → ⊥
false≢true ()

eq-ri-sound : ∀ {S Γ A} (f g : S ∣ Γ ⊢ri A) → eq-ri f g ≡ true → f ≡ g
eq-li-sound : ∀ {S Γ A} (f g : S ∣ Γ ⊢li A) → eq-li f g ≡ true → f ≡ g
eq-f-sound : ∀ {S Γ A} (f g : S ∣ Γ ⊢f A) → eq-f f g ≡ true → f ≡ g

eq-ri-sound (∧r f g) (∧r f' g') eq with ∧ᵇ-true eq
... | p , q = cong₂ ∧r (eq-ri-sound f f' p) (eq-ri-sound g g' q)
eq-ri-sound (⊸r f) (⊸r g) eq = cong ⊸r (eq-ri-sound f g eq)
eq-ri-sound (li2ri {C = ` X , tt} f) (li2ri g) eq = cong li2ri (eq-li-sound f g eq)
eq-ri-sound (li2ri {C = I , tt} f) (li2ri g) eq = cong li2ri (eq-li-sound f g eq)
eq-ri-sound (li2ri {C = A ⊗ B , tt} f) (li2ri g) eq = cong li2ri (eq-li-sound f g eq)
eq-ri-sound (li2ri {C = A ∨ B , tt} f) (li2ri g) eq = cong li2ri (eq-li-sound f g eq)

eq-li-sound (Il f) (Il g) eq = cong Il (eq-li-sound f g eq)
eq-li-sound (⊗l f) (⊗l g) eq = cong ⊗l (eq-li-sound f g eq)
eq-li-sound (∨l f g) (∨l f' g') eq with ∧ᵇ-true eq
... | p , q = cong₂ ∨l (eq-li-sound f f' p) (eq-li-sound g g' q)
eq-li-sound (f2li {S = - , tt} f) (f2li g) eq = cong f2li (eq-f-sound f g eq)
eq-li-sound (f2li {S = just (` X) , tt} f) (f2li g) eq = cong f2li (eq-f-sound f g eq)
eq-li-sound (f2li {S = just (A ⊸ B) , tt} f) (f2li g) eq = cong f2li (eq-f-sound f g eq)
eq-li-sound (f2li {S = just (A ∧ B) , tt} f) (f2li g) eq = cong f2li (eq-f-sound f g eq)

eq-f-sound ax ax eq = refl
eq-f-sound Ir Ir eq = refl
eq-f-sound (pass f) (pass g) eq = cong pass (eq-li-sound f g eq)
eq-f-sound (∧l₁ f) (∧l₁ g) eq = cong ∧l₁ (eq-li-sound f g eq)
eq-f-sound (∧l₂ f) (∧l₂ g) eq = cong ∧l₂ (eq-li-sound f g eq)
eq-f-sound (⊸l {Γ} {Δ} eq f g) (⊸l {Γ'} {Δ'} eq' f' g') e with length≟ Γ Γ'
... | no _ = ⊥-elim (false≢true e)
... | yes len with split-at-length Γ Γ' {Δ} {Δ'} (trans (sym eq) eq') len
...   | refl , refl with ∧ᵇ-true e
...     | p , q rewrite eq-ri-sound f f' p | eq-li-sound g g' q | uip {p = eq} {eq'} = refl
eq-f-sound (⊗r {S} {Γ} {Δ} eq f g ok) (⊗r {Γ = Γ'} {Δ'} eq' f' g' ok') e with length≟ Γ Γ'
... | no _ = ⊥-elim (false≢true e)
... | yes len with split-at-length Γ Γ' {Δ} {Δ'} (trans (sym eq) eq') len
...   | refl , refl with ∧ᵇ-true e
...     | p , q = ⊗req (eq-ri-sound f f' p) (eq-ri-sound g g' q)
eq-f-sound (∨r₁ f ok) (∨r₁ g ok') e = ∨r₁eq (eq-ri-sound f g e)
eq-f-sound (∨r₂ f ok) (∨r₂ g ok') e = ∨r₂eq (eq-ri-sound f g e)
eq-f-sound (pass f) (⊗r eq′ f′ g′ ok′) ()
eq-f-sound (⊗r eq f g ok) (pass f′) ()
eq-f-sound (pass f) (∨r₁ f′ ok′) ()
eq-f-sound (∨r₁ f ok) (pass f′) ()
eq-f-sound (pass f) (∨r₂ f′ ok′) ()
eq-f-sound (∨r₂ f ok) (pass f′) ()
eq-f-sound (∧l₁ f) (∧l₂ f′) ()
eq-f-sound (∧l₂ f) (∧l₁ f′) ()
eq-f-sound (∧l₁ f) (⊗r eq′ f′ g′ ok′) ()
eq-f-sound (⊗r eq f g ok) (∧l₁ f′) ()
eq-f-sound (∧l₁ f) (∨r₁ f′ ok′) ()
eq-f-sound (∨r₁ f ok) (∧l₁ f′) ()
eq-f-sound (∧l₁ f) (∨r₂ f′ ok′) ()
eq-f-sound (∨r₂ f ok) (∧l₁ f′) ()
eq-f-sound (∧l₂ f) (⊗r eq′ f′ g′ ok′) ()
eq-f-sound (⊗r eq f g ok) (∧l₂ f′) ()
eq-f-sound (∧l₂ f) (∨r₁ f′ ok′) ()
eq-f-sound (∨r₁ f ok) (∧l₂ f′) ()
eq-f-sound (∧l₂ f) (∨r₂ f′ ok′) ()
eq-f-sound (∨r₂ f ok) (∧l₂ f′) ()
eq-f-sound (⊸l eq f g) (⊗r eq′ f′ g′ ok′) ()
eq-f-sound (⊗r eq f g ok) (⊸l eq′ f′ g′) ()
eq-f-sound (⊸l eq f g) (∨r₁ f′ ok′) ()
eq-f-sound (∨r₁ f ok) (⊸l eq′ f′ g′) ()
eq-f-sound (⊸l eq f g) (∨r₂ f′ ok′) ()
eq-f-sound (∨r₂ f ok) (⊸l eq′ f′ g′) ()
eq-f-sound (∨r₁ f ok) (∨r₂ f′ ok′) ()
eq-f-sound (∨r₂ f ok) (∨r₁ f′ ok′) ()

-- Reflexivity used by Focus, FocusProperties and the decision procedure below.

eq-ri-refl : ∀ {S Γ A} (f : S ∣ Γ ⊢ri A) → eq-ri f f ≡ true
eq-li-refl : ∀ {S Γ A} (f : S ∣ Γ ⊢li A) → eq-li f f ≡ true
eq-f-refl : ∀ {S Γ A} (f : S ∣ Γ ⊢f A) → eq-f f f ≡ true

eq-ri-refl (∧r f g) rewrite eq-ri-refl f | eq-ri-refl g = refl
eq-ri-refl (⊸r f) = eq-ri-refl f
eq-ri-refl (li2ri f) = eq-li-refl f

eq-li-refl (Il f) = eq-li-refl f
eq-li-refl (⊗l f) = eq-li-refl f
eq-li-refl (∨l f g) rewrite eq-li-refl f | eq-li-refl g = refl
eq-li-refl (f2li f) = eq-f-refl f

eq-f-refl ax = refl
eq-f-refl Ir = refl
eq-f-refl (pass f) = eq-li-refl f
eq-f-refl (∧l₁ f) = eq-li-refl f
eq-f-refl (∧l₂ f) = eq-li-refl f
eq-f-refl (⊸l {Γ} eq f g)
  rewrite length≟-refl Γ | eq-ri-refl f | eq-li-refl g = refl
eq-f-refl (⊗r {Γ = Γ} eq f g ok)
  rewrite length≟-refl Γ | eq-ri-refl f | eq-ri-refl g = refl
eq-f-refl (∨r₁ f ok) = eq-ri-refl f
eq-f-refl (∨r₂ f ok) = eq-ri-refl f

-- Decidable equality used by check-focus in Focus and its proof in FocusEq.

_≟ri_ : ∀ {S Γ A} (f g : S ∣ Γ ⊢ri A) → Dec (f ≡ g)
f ≟ri g with eq-ri f g in eq
... | true = yes (eq-ri-sound f g eq)
... | false = no (λ { refl → false≢true (trans (sym eq) (eq-ri-refl f)) })

-- Context substitution on LI derivations.

subst-li : ∀ {S Γ Δ A} → Γ ≡ Δ → S ∣ Γ ⊢li A → S ∣ Δ ⊢li A
subst-li refl f = f



subst-ri : ∀ {S Γ Δ A} → Γ ≡ Δ → S ∣ Γ ⊢ri A → S ∣ Δ ⊢ri A
subst-ri refl f = f

subst-f : ∀ {S Γ Δ C} → Γ ≡ Δ → S ∣ Γ ⊢f C → S ∣ Δ ⊢f C
subst-f refl f = f

subst-ri-∧r : ∀ {S Γ Δ A B} (p : Γ ≡ Δ) (f : S ∣ Γ ⊢ri A) (g : S ∣ Γ ⊢ri B)
  → subst-ri p (∧r f g) ≡ ∧r (subst-ri p f) (subst-ri p g)
subst-ri-∧r refl f g = refl

subst-ri-⊸r : ∀ {S Γ Δ A B} (p : Γ ≡ Δ) (f : S ∣ Γ ++ [ A ] ⊢ri B)
  → subst-ri p (⊸r f) ≡ ⊸r (subst-ri (cong (_++ [ A ]) p) f)
subst-ri-⊸r refl f = refl

subst-ri-li2ri : ∀ {S Γ Δ C} (p : Γ ≡ Δ) (f : S ∣ Γ ⊢li C)
  → subst-ri p (li2ri f) ≡ li2ri (subst-li p f)
subst-ri-li2ri refl f = refl

subst-ri-trans : ∀ {S Γ Δ Λ A} (p : Γ ≡ Δ) (q : Δ ≡ Λ) (f : S ∣ Γ ⊢ri A)
  → subst-ri q (subst-ri p f) ≡ subst-ri (trans p q) f
subst-ri-trans refl refl f = refl

subst-ri-compose : ∀ {S Γ Δ Λ A} (p : Γ ≡ Δ) (q : Δ ≡ Λ) (r : Γ ≡ Λ) (f : S ∣ Γ ⊢ri A)
  → subst-ri q (subst-ri p f) ≡ subst-ri r f
subst-ri-compose refl refl refl f = refl

subst-ri-f2li-⊸l : ∀ {Γ Δ Λ A B C} (p : Λ ≡ Γ ++ Δ) (h : - ∣ Γ ⊢ri A) (f : just B ∣ Δ ⊢li C)
  → subst-ri (sym p) (li2ri (f2li (⊸l refl h f))) ≡ li2ri (f2li (⊸l p h f))
subst-ri-f2li-⊸l refl h f = refl

ri*-inv : ∀ {S Γ Λ A} (Ω : Cxt) → S ∣ Λ ⊢ri A → Λ ≡ Γ ++ Ω → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj Ω A)
ri*-inv Ω (∧r f g) eq = node (ri*-inv Ω f eq) (ri*-inv Ω g eq)
ri*-inv {Γ = Γ} Ω (⊸r {A = A} f) eq = ri*-inv (Ω ++ [ A ]) f (trans (cong (_++ [ A ]) eq) (++ass Γ))
ri*-inv Ω (li2ri {C = ` X , tt} f) eq = leaf (subst-li eq f)
ri*-inv Ω (li2ri {C = I , tt} f) eq = leaf (subst-li eq f)
ri*-inv Ω (li2ri {C = A ⊗ B , tt} f) eq = leaf (subst-li eq f)
ri*-inv Ω (li2ri {C = A ∨ B , tt} f) eq = leaf (subst-li eq f)

ri*-inv-subst : ∀ {S Γ Λ Ξ A} (Ω : Cxt) (p : Λ ≡ Ξ) (f : S ∣ Λ ⊢ri A) (q : Ξ ≡ Γ ++ Ω)
  → ri*-inv Ω (subst-ri p f) q ≡ ri*-inv Ω f (trans p q)
ri*-inv-subst Ω refl f q = refl

ri-inv : ∀ {S Γ A} → S ∣ Γ ⊢ri A → All (λ x → S ∣ Γ ++ proj₁ x ⊢li proj₂ x) (impconj [] A)
ri-inv {Γ = Γ} f = ri*-inv [] f (sym (++ru Γ))

tags-fs : (S : Irr) (Γ : Cxt) {Φ : Tree (Cxt × Pos)} → All (λ x → (irr S) ∣ Γ ++ proj₁ x ⊢li proj₂ x) Φ → List Tag
tags-fs S Γ {leaf (Ω , _)} (leaf (f2li f)) = [ tag-f Γ Ω f refl ]
tags-fs S Γ (node fs gs) = tags-fs S Γ fs ++ tags-fs S Γ gs

tag-subst : ∀ {S Γ Ω Λ C i} (p : Λ ≡ Γ ++ Ω) (f : (irr S , i) ∣ Λ ⊢f C)
  → tags-fs S Γ {leaf (Ω , C)} (leaf (subst-li p (f2li f))) ≡ [ tag-f Γ Ω f p ]
tag-subst refl f = refl

tags-ri-inv : ∀ S {Γ Λ} Ω {A} (f : irr S ∣ Λ ⊢ri A) (eq : Λ ≡ Γ ++ Ω)
  → tags-fs S Γ (ri*-inv Ω f eq) ≡ tags-ri-gen S Γ Ω f eq
tags-ri-inv S Ω (∧r f g) eq = cong₂ _++_ (tags-ri-inv S Ω f eq) (tags-ri-inv S Ω g eq)
tags-ri-inv S {Γ} Ω (⊸r {A = A} f) eq = tags-ri-inv S (Ω ++ [ A ]) f (trans (cong (_++ [ A ]) eq) (++ass Γ))
tags-ri-inv S Ω (li2ri {C = ` X , tt} (f2li f)) eq = tag-subst {S = S} eq f
tags-ri-inv S Ω (li2ri {C = I , tt} (f2li f)) eq = tag-subst {S = S} eq f
tags-ri-inv S Ω (li2ri {C = A ⊗ B , tt} (f2li f)) eq = tag-subst {S = S} eq f
tags-ri-inv S Ω (li2ri {C = A ∨ B , tt} (f2li f)) eq = tag-subst {S = S} eq f

tags-ri-inv₀ : ∀ S {Γ A} (f : irr S ∣ Γ ⊢ri A) → tags-fs S Γ (ri-inv f) ≡ tags-ri S f
tags-ri-inv₀ S {Γ} f = tags-ri-inv S [] f (sym (++ru Γ))
