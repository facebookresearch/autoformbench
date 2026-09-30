import ChallengeDeps
import Submission

open Autoform_Algebraic_Topology_I_alg_top_theorem102
open CategoryTheory Limits AlgebraicTopology

theorem theorem102 (X : TopCat) (A : Set ↑X) (U : Set ↑A)
    (h : IsExcisive A U) :
    ∀ n : ℕ, IsIso (RelativeHomologyMap (excisionPairMap X A U) n) := by
  exact Submission.theorem102 X A U h
