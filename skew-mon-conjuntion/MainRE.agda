{-# OPTIONS --rewriting #-}
module MainRE where

-- Some basic facts aobut lists
import Utilities

-- Formulae
import Formulae

-- Sequent calculus 
import SeqCalc

-- Interleaving type isInter and permutation of lists ↭'
import IsInter

-- Focused calculus
import FocusingRE

-- Equivalent proofs in sequent calculus are identical in focused calculus
-- f ≗ g → focus f ≡ focus g
import EqfocusRE

-- Every sequent calculus proof is equivalent with its normal form
-- emb-c (focus f) ≗ f
import EmbfocusRE

-- Normal form of a focused proof is identical to itself
-- focus (emb-c f) ≡ f
import FocusEmbRE