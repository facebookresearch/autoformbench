/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Differential_Analysis_diff_analysis_theorem_10_5
open scoped BigOperators LineDeriv Pointwise

namespace Submission

theorem theorem_10_5 (n : ℕ) (u : TemperedDistribution (Rn n) ℂ) :
    (∃ m : ℕ,
      ∃ coeffs : DoubleMultiIndex n →₀ (Rn n → ℂ),
        HasDegreeBound m coeffs ∧
        (∀ γ : DoubleMultiIndex n, γ ∈ coeffs.support → IsC0Function (coeffs γ)) ∧
        ∃ coeffTD : DoubleMultiIndex n →₀ TemperedDistribution (Rn n) ℂ,
          coeffTD.support = coeffs.support ∧
          (∀ γ : DoubleMultiIndex n, γ ∈ coeffs.support →
            RepresentsTemperedDistribution (coeffs γ) (coeffTD γ)) ∧
          u = Finset.sum coeffs.support (fun γ : DoubleMultiIndex n =>
            (TemperedDistribution.smulLeftCLM ℂ (coordMonomial γ.1))
              (iteratedCoordMelroseDeriv γ.2 (coeffTD γ)))) ∧
    (∃ m : ℕ,
      ∃ coeffs : DoubleMultiIndex n →₀ (Rn n → ℂ),
        HasDegreeBound m coeffs ∧
        (∀ γ : DoubleMultiIndex n, γ ∈ coeffs.support → IsC0Function (coeffs γ)) ∧
        ∃ coeffTD : DoubleMultiIndex n →₀ TemperedDistribution (Rn n) ℂ,
          coeffTD.support = coeffs.support ∧
          (∀ γ : DoubleMultiIndex n, γ ∈ coeffs.support →
            RepresentsTemperedDistribution (coeffs γ) (coeffTD γ)) ∧
          u = Finset.sum coeffs.support (fun γ : DoubleMultiIndex n =>
            iteratedCoordMelroseDeriv γ.2
              ((TemperedDistribution.smulLeftCLM ℂ (coordMonomial γ.1))
                (coeffTD γ)))) := by
  sorry

end Submission
