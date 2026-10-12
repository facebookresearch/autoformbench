/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Functions_of_a_Complex_Variable_complex_var_PoissonIntegralUnitDisc_harmonic_and_boundary
open Complex Filter Metric
open scoped Topology Interval

namespace Submission

theorem PoissonIntegralUnitDisc_harmonic_and_boundary (U : ℂ → ℝ)
    (hU : PiecewiseContinuousOnUnitCircle U) :
    let u : ℂ → ℝ := PoissonIntegralUnitDisc U
    InnerProductSpace.HarmonicOnNhd u (Metric.ball (0 : ℂ) 1) ∧
      ∀ φ₀ : ℝ,
        ContinuousWithinAt U
          (Metric.sphere (0 : ℂ) 1)
          (Complex.exp ((φ₀ : ℂ) * Complex.I)) →
        Tendsto u
          (𝓝[Metric.ball (0 : ℂ) 1]
            (Complex.exp ((φ₀ : ℂ) * Complex.I)))
          (𝓝 (U (Complex.exp ((φ₀ : ℂ) * Complex.I)))) := by
  sorry

end Submission
