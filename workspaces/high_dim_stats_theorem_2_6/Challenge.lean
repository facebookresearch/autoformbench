/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_6
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Nat
open scoped InnerProductSpace ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {d n : ℕ}

theorem theorem_2_6 :
  ∃ C : ℝ, 0 < C ∧ ∀
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {d n k : ℕ}
  {Y : Ω → (EuclideanSpace ℝ (Fin n))} {X : Mat n d} {ε : Ω → (EuclideanSpace ℝ (Fin n))}
  {θhatLSB0k : Ω → (EuclideanSpace ℝ (Fin d))}
  {θstar : (EuclideanSpace ℝ (Fin d))}
  {sigma2 : ℝ}
  {δ : ℝ}
  (h_k : 2 * k ≤ d)
  (h_model : LinearRegressionModel Y X θstar ε)
  (h_meas : Measurable θhatLSB0k)
  (h_θstar : θstar ∈ B0 d k)
  (h_sigma2 : 0 < sigma2)
  (h_subG : IsSubgaussian ε sigma2.toNNReal P)
  (h_LSE : IsConstrainedLeastSquaresEstimator (B0 d k) θhatLSB0k Y X)
  (h_delta : 0 < δ ∧ δ < 1),
  P {ω | MSE X (θhatLSB0k ω) θstar
    ≤ C * sigma2 * (log (choose d (2 * k) : Real) + ↑k + log (1 / δ)) / ↑n} ≥ ENNReal.ofReal (1 - δ) := by
  sorry
