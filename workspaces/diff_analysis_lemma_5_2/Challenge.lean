import Mathlib

theorem lemma_5_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty) :
    ∃! v ∈ C, ∀ w ∈ C, ‖v‖ ≤ ‖w‖ := by
  sorry
