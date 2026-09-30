import Mathlib

theorem class_meeting_9_corollary_3_0_2 {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : InnerProductSpace.HarmonicOnNhd u Set.univ)
    (h_one_sided_bound :
      BddBelow (Set.range u) ∨ BddAbove (Set.range u)) :
    ∃ c : ℝ, ∀ x, u x = c := by
  sorry
