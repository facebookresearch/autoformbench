/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Real Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem theorem_1_14 {n : ℕ} [NeZero n]
    {X : Fin n → Ω → ℝ}
    {σ : ℝ} (hσ : 0 < σ)
    (hsubG : ∀ i, HasSubgaussianMGF (X i) (σ ^ 2).toNNReal P) :
    (∫ ω, univ.sup' univ_nonempty (fun i => X i ω) ∂P) ≤
      σ * sqrt (2 * log (↑n)) ∧
    (∫ ω, univ.sup' univ_nonempty (fun i => |X i ω|) ∂P) ≤
      σ * sqrt (2 * log (2 * ↑n)) ∧
    (∀ t : ℝ, 0 < t →
      P {ω | univ.sup' univ_nonempty (fun i => X i ω) > t} ≤
        ENNReal.ofReal (↑n * exp (-t ^ 2 / (2 * σ ^ 2))) ∧
      P {ω | univ.sup' univ_nonempty (fun i => |X i ω|) > t} ≤
        ENNReal.ofReal (2 * ↑n * exp (-t ^ 2 / (2 * σ ^ 2)))) := by
  sorry
