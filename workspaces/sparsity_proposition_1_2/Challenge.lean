import ChallengeDeps

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_2

theorem proposition_1_2 {p : ℕ}
    (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (χ : ℝ)
    (w : EuclideanSpace ℝ (Fin p))
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_differentiable : Differentiable ℝ f)
    (hΩ_norm : ∀ x, Ω x = 0 ↔ x = 0)
    (hχ : 0 < χ) :
    (IsMinOn (fun x => f x + χ * Ω x) Set.univ w ↔
      (-(1 / χ)) • gradient f w ∈
        subdifferential (fun x => Ω x) w) ∧
    (w = 0 →
      subdifferential (fun x => Ω x) w =
        {z : EuclideanSpace ℝ (Fin p) | dualNorm Ω z ≤ 1}) ∧
    (w ≠ 0 →
      subdifferential (fun x => Ω x) w =
        {z : EuclideanSpace ℝ (Fin p) |
          dualNorm Ω z = 1 ∧ inner ℝ z w = Ω w}) := by
  sorry
