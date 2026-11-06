{-# OPTIONS --safe #-}

module DecEq (At : Set) where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Sum renaming ([_,_]′ to rec⊎)
open import Data.Empty
open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])

open import Utilities
open import Formulae At
import SeqCalc.ImplEq At as I
import SeqCalc.ExplEq At as E
open import SeqCalc.Equiv.Maps At using (_∣_⊢I_; _∣_⊢E_; toI; toE)
open import SeqCalc.Equiv.WellDef At using (toI-≗; toE-≗)
open import SeqCalc.Equiv.ExplImpl At using (toE-toI)
open import Focus.Tags
open import Focus.FocusedCalc At
open import Focus.Maps At
open import Focus.WellDef At
open import Focus.EmbFocus At

-- Compare occurrence choices in a fixed context. Equal positions identify
-- the selected formula, remaining context, and Pick witness together.
pick≟ : ∀ {A B Γ Δ Ξ} (p : Pick A Γ Δ) (q : Pick B Γ Ξ)
  → _≡_ {A = Σ Fma λ A → Σ Cxt λ Δ → Pick A Γ Δ} (A , Δ , p) (B , Ξ , q)
    ⊎ (_≡_ {A = Σ Fma λ A → Σ Cxt λ Δ → Pick A Γ Δ} (A , Δ , p) (B , Ξ , q) → ⊥)
pick≟ p q with pick-index p ≟ pick-index q
... | yes eq = inj₁ (same-pick p q eq)
... | no neq = inj₂ (λ { refl → neq refl })

-- Compare allocations of each occurrence, identifying both premise
-- contexts and the partition witness. No equality test on atoms is used.
part≟ : ∀ {Γ Δ Γ′ Δ′ Ξ} (p : Part Γ Δ Ξ) (q : Part Γ′ Δ′ Ξ)
  → _≡_ {A = Σ Cxt λ Γ → Σ Cxt λ Δ → Part Γ Δ Ξ} (Γ , Δ , p) (Γ′ , Δ′ , q)
    ⊎ (_≡_ {A = Σ Cxt λ Γ → Σ Cxt λ Δ → Part Γ Δ Ξ} (Γ , Δ , p) (Γ′ , Δ′ , q) → ⊥)
part≟ done done = inj₁ refl
part≟ (left p) (left q) =
  rec⊎ (λ { refl → inj₁ refl })
    (λ neq → inj₂ (λ { refl → neq refl })) (part≟ p q)
part≟ (right p) (right q) =
  rec⊎ (λ { refl → inj₁ refl })
    (λ neq → inj₂ (λ { refl → neq refl })) (part≟ p q)
part≟ (left p) (right q) = inj₂ (λ ())
part≟ (right p) (left q) = inj₂ (λ ())

-- Decide equality of derivations of the same sequent in each focused phase.
-- Indices already fix the formulae, so no equality test on At is needed.
Dec≡ri : ∀ {S Γ C} (f g : S ∣ Γ ⊢ri C) → (f ≡ g) ⊎ (f ≡ g → ⊥)
Dec≡li : ∀ {S Γ C} (f g : S ∣ Γ ⊢li C) → (f ≡ g) ⊎ (f ≡ g → ⊥)
Dec≡f : ∀ {S Γ C} (f g : S ∣ Γ ⊢f C) → (f ≡ g) ⊎ (f ≡ g → ⊥)

Dec≡ri (∧r f f') (∧r g g') =
  rec⊎ (λ { refl → rec⊎ (λ { refl → inj₁ refl })
                        (λ neq → inj₂ (λ { refl → neq refl }))
                        (Dec≡ri f' g') })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f g)
Dec≡ri (li2ri {C = A , i} f) (li2ri {C = .A , j} g) with isPos-unique A i j
... | refl =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)

Dec≡li (⊗l f) (⊗l g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡li (Il f) (Il g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡li (∨l f f') (∨l g g') =
  rec⊎ (λ { refl → rec⊎ (λ { refl → inj₁ refl })
                        (λ neq → inj₂ (λ { refl → neq refl }))
                        (Dec≡li f' g') })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡li (f2li {S = S , i} f) (f2li {S = .S , j} g) with isIrr-unique S i j
... | refl =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡f f g)

Dec≡f ax ax = inj₁ refl
Dec≡f Ir Ir = inj₁ refl
Dec≡f (pass p f) (pass q g) with pick≟ p q
... | inj₂ neq = inj₂ (λ { refl → neq refl })
... | inj₁ refl =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡f (∧l₁ f) (∧l₁ g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡f (∧l₂ f) (∧l₂ g) =
  rec⊎ (λ { refl → inj₁ refl })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡li f g)
Dec≡f (∨r₁ f ok) (∨r₁ g ok') =
  rec⊎ (λ eq → inj₁ (∨r₁eq eq))
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f g)
Dec≡f (∨r₂ f ok) (∨r₂ g ok') =
  rec⊎ (λ eq → inj₁ (∨r₂eq eq))
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f g)
-- Identify the partition and its two premise contexts before comparing
-- the premises; isOK witnesses are propositions.
Dec≡f (⊗r p f g ok) (⊗r q f′ g′ ok′) with part≟ p q
... | inj₂ neq = inj₂ (λ { refl → neq refl })
... | inj₁ refl =
  rec⊎ (λ { refl → rec⊎ (λ eqg → inj₁ (⊗req p refl eqg))
                        (λ neq → inj₂ (λ { refl → neq refl }))
                        (Dec≡ri g g′) })
       (λ neq → inj₂ (λ { refl → neq refl }))
       (Dec≡ri f f′)
Dec≡f (pass p f) (⊗r eq′ f′ g′ ok′) = inj₂ (λ ())
Dec≡f (pass p f) (∨r₁ f′ ok′) = inj₂ (λ ())
Dec≡f (pass p f) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (⊗r eq′ f′ g′ ok′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (∨r₁ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₁ f) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (⊗r eq′ f′ g′ ok′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (∨r₁ f′ ok′) = inj₂ (λ ())
Dec≡f (∧l₂ f) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (⊗r eq f g ok) (pass q f′) = inj₂ (λ ())
Dec≡f (⊗r eq f g ok) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (⊗r eq f g ok) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (pass q f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∨r₁ f ok) (∨r₂ f′ ok′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (pass q f′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (∧l₁ f′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (∧l₂ f′) = inj₂ (λ ())
Dec≡f (∨r₂ f ok) (∨r₁ f′ ok′) = inj₂ (λ ())

-- Equal normal forms imply implicit equivalence through their embedding.
injective-focus : ∀ {S Γ C} {f g : S ∣ Γ ⊢I C}
  → focus f ≡ focus g → f I.≗ g
injective-focus eq =
  (I.~ embfocus _) I.∙ I.≡to≗ (cong emb-ri eq) I.∙ embfocus _

-- Decide the implicit equational theory by comparing focused normal forms.
Dec≗I : ∀ {S Γ C} (f g : S ∣ Γ ⊢I C) → (f I.≗ g) ⊎ (f I.≗ g → ⊥)
Dec≗I f g =
  rec⊎ (λ eq → inj₁ (injective-focus eq))
    (λ neq → inj₂ (λ eq → neq (eqfocus eq)))
    (Dec≡ri (focus f) (focus g))

-- Transfer the procedure to explicit exchange through the equivalence.
-- Preservation gives the negative direction; the inverse law gives the
-- positive direction after translating the implicit equality back.
Dec≗E : ∀ {S Γ C} (f g : S ∣ Γ ⊢E C) → (f E.≗ g) ⊎ (f E.≗ g → ⊥)
Dec≗E f g =
  rec⊎ (λ eq → inj₁ ((E.~ toE-toI f) E.∙ toE-≗ eq E.∙ toE-toI g))
    (λ neq → inj₂ (λ eq → neq (toI-≗ eq)))
    (Dec≗I (toI f) (toI g))


module Example where
  f : - ∣ I ∷ I ∷ [] ⊢E I
  f = E.pass refl (E.Il (E.pass refl (E.Il E.Ir)))

  g : - ∣ I ∷ I ∷ [] ⊢E I
  g = E.ex sw f
  
  f≗̸g : Dec≗E f g ≡ inj₂ _
  f≗̸g = refl
