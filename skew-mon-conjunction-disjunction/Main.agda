{-# OPTIONS --rewriting #-}

module Main where

-- Some basic facts about lists
import Utilities

-- Formulae
import Formulae

-- Sequent Calculus
import SeqCalc

-- Focused calculus
import Focusing


-- Correctness of the tagged focused sequent calculus, which corresponds to the Theorem 4.5 in the paper.
{-
Equivalent derivations in sequent calculus 
are identical in focused calculus.
-}
import Eqfocus

{-
Every derivation in sequent calculus is 
≗-to the its normal form,
i.e. emb-ri (focus f) ≗ f.
-}
import Embfocus

{-
Focused derivations are in normal form,
i.e. focus (emb-ri f) ≡ f.
-}
import Focusemb
