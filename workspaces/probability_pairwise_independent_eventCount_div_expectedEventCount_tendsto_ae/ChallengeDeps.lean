/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MeasureTheory

namespace Autoform_Theory_of_Probability_probability_pairwise_independent_eventCount_div_expectedEventCount_tendsto_ae

variable {Ω : Type*} [MeasurableSpace Ω]








noncomputable def eventCount (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, (A (i + 1)).indicator (fun _ : Ω => (1 : ℝ)) ω





noncomputable def expectedEventCount (A : ℕ → Set Ω) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ ω, eventCount A n ω ∂μ



end Autoform_Theory_of_Probability_probability_pairwise_independent_eventCount_div_expectedEventCount_tendsto_ae
