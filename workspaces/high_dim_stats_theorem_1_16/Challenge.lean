import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_16
open MeasureTheory

theorem theorem_1_16 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d N : ℕ} [NeZero N]
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {vertices : Fin N → EuclideanSpace ℝ (Fin d)}
    {X : Ω → EuclideanSpace ℝ (Fin d)} {sigma : ℝ}
    (hP : IsListedConvexPolytope P vertices)
    (h_vertex_subG :
      ∀ i : Fin N, IsSubGaussian μ (vertexLinearForms vertices X i) sigma) :
    (Integrable (pointwiseLinearFormSupOn P X) μ ∧
      (∫ ω, pointwiseLinearFormSupOn P X ω ∂μ) ≤
        sigma * Real.sqrt (2 * Real.log (N : ℝ))) ∧
    (Integrable (pointwiseAbsLinearFormSupOn P X) μ ∧
      (∫ ω, pointwiseAbsLinearFormSupOn P X ω ∂μ) ≤
        sigma * Real.sqrt (2 * Real.log (2 * (N : ℝ)))) ∧
    (∀ t : ℝ, 0 < t →
      μ.real {ω | pointwiseLinearFormSupOn P X ω > t} ≤
        (N : ℝ) * Real.exp (-(t ^ 2) / (2 * sigma ^ 2)) ∧
      μ.real {ω | pointwiseAbsLinearFormSupOn P X ω > t} ≤
        (2 * (N : ℝ)) * Real.exp (-(t ^ 2) / (2 * sigma ^ 2))) := by
  sorry
