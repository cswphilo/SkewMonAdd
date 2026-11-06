{-# OPTIONS --safe #-}

module Main where

{-
Skew monoidal sequent calculus with additive conjunction and disjunction.
The focused calculus uses isOK side conditions on computed tags.
All modules are checked with --safe; atoms are module parameters.
-}

-- Binary trees of premises, their operations, and context equalities.
import Utilities

-- Formulae, stoups, contexts, and polarity predicates.
import Formulae

-- Sequent calculus and the equivalence relation ≗ on derivations.
import SeqCalc

-- Tags recording noninvertible rules, and the validity predicate isOK.
import Tags

-- The right-invertible, left-invertible, and focused phases.
import FocusedSeqCalc

-- Normalize a sequent-calculus derivation to a focused derivation.
import Focus

-- Embed focused derivations into the sequent calculus.
import Emb

{-
Equivalent derivations have identical focused normal forms:
eqfocus : f ≗ g → focus f ≡ focus g.
-}
import FocusWellDef

{-
Every derivation is ≗-related to the embedding of its normal form:
embfocus : (f : S ∣ Γ ⊢ C) → emb-ri (focus f) ≗ f.
-}
import EmbFocus

{-
Focused derivations are already in normal form:
focusemb-ri : (f : S ∣ Γ ⊢ri C) → focus (emb-ri f) ≡ f.
-}
import FocusEmb

{-
Equivalence of derivations is decidable by comparing their normal forms.
Dec≗ requires no decidable equality on atoms.
-}
import DecEq
