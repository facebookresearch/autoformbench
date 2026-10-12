/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Complex Filter Topology Set MeasureTheory

theorem newman_analytic_theorem (f : ℝ → ℂ)
    (hf_bound : ∃ M, ∀ t ≥ 0, ‖f t‖ ≤ M)
    (hf_locint : ∀ T ≥ 0, MeasureTheory.IntegrableOn f (Set.Icc 0 T))
    (g : ℂ → ℂ)
    (hg_holo : AnalyticOnNhd ℂ g {z : ℂ | 0 ≤ z.re})
    (hG_eq : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ici (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * f t) :
    Tendsto (fun T : ℝ ↦ ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (g 0)) := by
  sorry
