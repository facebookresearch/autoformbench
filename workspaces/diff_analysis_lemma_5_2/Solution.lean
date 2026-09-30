import Mathlib
import Submission

theorem lemma_5_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty) :
    ∃! v ∈ C, ∀ w ∈ C, ‖v‖ ≤ ‖w‖ := by
  exact Submission.lemma_5_2 hC_closed hC_convex hC_nonempty
