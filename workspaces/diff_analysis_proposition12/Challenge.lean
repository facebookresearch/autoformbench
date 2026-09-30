import Mathlib

open scoped Topology

universe u v

theorem proposition12 {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (e : E ≃ₗ[𝕜] F) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : E, C⁻¹ * ‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ C * ‖x‖ := by
  sorry
