import Mathlib
import Submission.Helpers

universe u


theorem proposition_1_3 {𝕜 : Type u} [RCLike 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
    (u : V →ₗ[ℝ] ℝ) :
    (Continuous u ↔ ContinuousAt u 0) ∧
    (Continuous u ↔ ∃ C : ℝ, ∀ v : V, ‖v‖ ≤ 1 → ‖u v‖ ≤ C) ∧
    (Continuous u ↔ ∃ C : ℝ, ∀ v : V, ‖u v‖ ≤ C * ‖v‖) := by
  sorry

