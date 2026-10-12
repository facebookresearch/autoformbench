/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_14
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped InnerProductSpace ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {d n : ℕ}

theorem theorem_2_14 :
  ∃ C : ℝ, 0 < C ∧ ∀
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {d n : ℕ}
  {Y : Ω → (EuclideanSpace ℝ (Fin n))} {X : Mat n d} {θstar : (EuclideanSpace ℝ (Fin d))} {ε : Ω → (EuclideanSpace ℝ (Fin n))}
  {θhatBIC : Ω → (EuclideanSpace ℝ (Fin d))}
  {sigma : ℝ}
  {τ : ℝ}
  {δ : ℝ}
  (h_n : 0 < n)
  (h_sigma : 0 < sigma)
  (h_model : LinearRegressionModel Y X θstar ε)
  (h_subG : IsSubgaussian ε (sigma^2).toNNReal P)
  (h_LSE : IsBICEstimator θhatBIC Y X τ)
  (h_meas : Measurable θhatBIC)
  (h_τ : τ^2 = 16 * log 6 * sigma^2 / ↑n + 32 * sigma^2 * log (exp 1 * ↑d) / ↑n)
  (h_delta : 0 < δ ∧ δ < 1),
  ∃ A : Set Ω,
    MeasurableSet A ∧
    P A ≥ ENNReal.ofReal (1 - δ) ∧
    ∀ ω : A,
      MSE X (θhatBIC ω) θstar
      ≤ C * sigma^2 *
          (↑(SupportCard d θstar) * log (exp 1 * ↑d) + log (1 / δ)) / ↑n := by
  exact Submission.theorem_2_14
