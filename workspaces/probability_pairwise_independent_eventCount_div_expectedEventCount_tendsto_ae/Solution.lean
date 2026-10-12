/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Theory_of_Probability_probability_pairwise_independent_eventCount_div_expectedEventCount_tendsto_ae
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem pairwise_independent_eventCount_div_expectedEventCount_tendsto_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Set Ω)
    (hmeas : ∀ n : ℕ, MeasurableSet (A (n + 1)))
    (hpair : Pairwise (fun m n : ℕ => IndepSet (A (m + 1)) (A (n + 1)) μ))
    (hdiv : (∑' n : ℕ, μ (A (n + 1))) = (∞ : ℝ≥0∞)) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => eventCount A n ω / expectedEventCount A μ n)
        atTop
        (nhds (1 : ℝ)) := by
  exact Submission.pairwise_independent_eventCount_div_expectedEventCount_tendsto_ae μ A hmeas hpair hdiv
