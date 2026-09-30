import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_15
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped InnerProductSpace ENNReal

theorem theorem_2_15 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {d n : ℕ}
  {Y : Ω → (EuclideanSpace ℝ (Fin n))} {X : Mat n d} {θstar : (EuclideanSpace ℝ (Fin d))} {ε : Ω → (EuclideanSpace ℝ (Fin n))}
  {θhatLASSO : Ω → (EuclideanSpace ℝ (Fin d))}
  {sigma : ℝ}
  {τ : ℝ}
  {δ : ℝ}
  (h_model : LinearRegressionModel Y X θstar ε)
  (h_subG : IsSubgaussian ε (sigma ^ 2).toNNReal P)
  (h_sigma : 0 < sigma)
  (h_norm : IsNormalized X)
  (h_LSE : IsLASSOEstimator θhatLASSO Y X τ)
  (h_τ : τ = sigma * √(2 * log (2 * ↑d) / ↑n)
           + sigma * √(2 * log (1 / δ) / ↑n))
  (h_delta : 0 < δ ∧ δ < 1)
  :
  P {ω | MSE X (θhatLASSO ω) θstar
    ≤ 4 * (Norm1 d θstar) * sigma * √(2 * log (2 * ↑d) / ↑n)
    + 4 * (Norm1 d θstar) * sigma * √(2 * log (1 / δ) / ↑n)} ≥ ENNReal.ofReal (1 - δ)
  := by
  sorry
