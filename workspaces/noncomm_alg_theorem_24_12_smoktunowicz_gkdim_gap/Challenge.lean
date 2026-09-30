import ChallengeDeps

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_24_12_smoktunowicz_gkdim_gap

universe u v

theorem theorem_24_12_smoktunowicz_gkdim_gap (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A]
    (G : NGradedAlgebra k A)
    (h_domain : IsNoncommutativeDomain A)
    {δ : ℝ}
    (h_gk : HasGelfandKirillovDimension k A δ) :
    ¬ (2 < δ ∧ δ < 3) := by
  sorry
