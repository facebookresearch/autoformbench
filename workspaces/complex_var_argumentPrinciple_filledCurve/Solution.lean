/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Functions_of_a_Complex_Variable_complex_var_argumentPrinciple_filledCurve
open Set Metric MeromorphicOn
open scoped BigOperators

theorem argumentPrinciple_filledCurve {Ω : Set ℂ} {f : ℂ → ℂ}
    (J : FilledCurve)
    (inside : Finset ℂ)
    (hΩ : IsRegion Ω)
    (hfilled_subset : J.filled ⊆ Ω)
    (hf : MeromorphicOn f Ω)
    (hlogDeriv_regular :
      DifferentiableOn ℂ
        (logDeriv f)
        (Ω \ (divisor f Ω).support))
    (hboundary_smooth : J.HasSmoothBoundary)
    (hboundary_integrable :
      J.BoundaryIntegrable (logDeriv f))
    (hboundary_avoids :
      ∀ z : ℂ, z ∈ J.curve → (divisor f Ω) z = 0)
    (hinside :
      ∀ a : ℂ,
        a ∈ inside ↔ a ∈ (divisor f Ω).support ∧ a ∈ J.interior)
    (horient : J.PositivelyOriented) :
    twoPiI⁻¹ * J.boundaryIntegral (logDeriv f) =
      (zeroCount (divisor f Ω) inside : ℂ) -
        (poleCount (divisor f Ω) inside : ℂ) := by
  exact Submission.argumentPrinciple_filledCurve J inside hΩ hfilled_subset hf hlogDeriv_regular hboundary_smooth hboundary_integrable hboundary_avoids hinside horient
