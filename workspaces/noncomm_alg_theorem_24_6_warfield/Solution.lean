import ChallengeDeps
import Submission

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_24_6_warfield

universe u

theorem theorem_24_6_warfield (k : Type u) [Field k]
    (δ : ℝ)
    (hδ : 2 ≤ δ) :
    Nonempty (TwoGeneratedAlgebraWithGKDimension k δ) := by
  exact Submission.theorem_24_6_warfield k δ hδ
