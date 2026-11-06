{-# OPTIONS --safe #-}

module Main where

{-
Skew exchange is represented by arbitrary pass selections and
order-preserving tensor partitions in SeqCalc.Impl. SeqCalc.Expl is the
equivalent presentation with explicit adjacent exchange.
Normalization maps implicit derivations to the focused calculus, whose
three phases ri, li, and f use computed tags and isOK side conditions.
-}

-- Trees, context equalities, and occurrence-sensitive partitions.
import Utilities

-- Formulae, polarities, stoups, and contexts.
import Formulae

-- Original sequent calculus with Swap-indexed exchange.
import SeqCalc.Expl

-- Explicit generating equations for the original calculus.
import SeqCalc.ExplEq

-- Unfocused Pick/Part presentation, with admissible exchange.
import SeqCalc.Impl

-- Logical equations and derived exchange congruence.
import SeqCalc.ImplEq

-- Translations between explicit and implicit exchange.
import SeqCalc.Equiv.Maps

-- Translations preserve the generating equations in both directions.
import SeqCalc.Equiv.WellDef

-- Translating explicit derivations to implicit ones and back is identity
-- modulo the explicit equations.
import SeqCalc.Equiv.ExplImpl

-- Translating implicit derivations to explicit ones and back is identity
-- modulo the implicit equations.
import SeqCalc.Equiv.ImplExpl

-- Pass tags P n and validity, including distinct pass positions.
import Focus.Tags

-- The focused calculus with implicit skew exchange.
import Focus.FocusedCalc

-- Normalize implicit derivations and embed focused derivations.
import Focus.Maps

-- Normalization identifies both sides of every implicit equation.
import Focus.WellDef

-- Embedding a normal form recovers the implicit derivation modulo equations.
import Focus.EmbFocus

-- Normalizing an embedded focused derivation recovers it in each phase.
import Focus.FocusEmb

-- Decide equivalence in the implicit calculus by comparing normal forms,
-- and in the explicit calculus through the equivalence maps.
import DecEq
