/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.InnerProductSpace.PiL2
import ChallengeDeps

open Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_19_part2_bound
open MeasureTheory MeasureTheory.Measure ProbabilityTheory InnerProductSpace Real


namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_19_part2_bound


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]





section
variable (σ2 : NNReal) {d : ℕ} (X : Ω → (EuclideanSpace ℝ (Fin d))) (hX : IsSubgaussian X σ2 P)


theorem theorem_1_19_left_sup_mem (ω : Ω) :
    sSup ((fun θ => ⟪θ, X ω⟫_ℝ) '' B2 d) ∈
    (fun θ => ⟪θ, X ω⟫_ℝ) '' B2 d := by
  sorry
theorem theorem_1_19_right_sup_mem (ω : Ω) :
    sSup ((fun θ => |⟪θ, X ω⟫_ℝ|) '' B2 d) ∈
    (fun θ => |⟪θ, X ω⟫_ℝ|) '' B2 d := by
  sorry


theorem theorem_1_19_part1_eq :
    (∫ ω, sSup ((fun θ => ⟪θ, X ω⟫_ℝ) '' B2 d) ∂P) =
    (∫ ω, sSup ((fun θ => |⟪θ, X ω⟫_ℝ|) '' B2 d) ∂P) := by
  sorry


theorem theorem_1_19_part1_bound (hX : IsSubgaussian X σ2 P) :
    (∫ ω, sSup ((fun θ => |⟪θ, X ω⟫_ℝ|) '' B2 d) ∂P) ≤
    4 * (σ2 : ℝ).sqrt * (d : ℝ).sqrt := by
  sorry


theorem theorem_1_19_part2_eq (ω : Ω) :
    sSup ((fun θ => ⟪θ, X ω⟫_ℝ) '' B2 d) =
    sSup ((fun θ => |⟪θ, X ω⟫_ℝ|) '' B2 d) := by
  sorry


theorem theorem_1_19_part2_bound (hX : IsSubgaussian X σ2 P)
    (δ : ℝ) (hδ : 0 < δ) :
    P {ω | sSup ((fun θ => |⟪θ, X ω⟫_ℝ|) '' B2 d) ≤
      4 * (σ2 : ℝ).sqrt * (d : ℝ).sqrt +
      2 * (σ2 : ℝ).sqrt * (2 * log (1 / δ)).sqrt} ≥
    ENNReal.ofReal (1 - δ) := by
  sorry

end

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_1_19_part2_bound
