/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Number_Theory_I_number_theory_Lemma19_5

theorem Lemma19_5 (n : ℕ) (hn : 1 ≤ n) (S : Set (Fin n → ℝ))
    (hS_meas : MeasurableSet S)
    (hS_boundary : BoundaryLipschitzParametrizable n S)
    (hS_finite : ∀ t : ℝ, 0 < t → (latticePoints S t).Finite) :
      (fun t : ℝ =>
          (latticePointCount S t : ℝ) -
            ENNReal.toReal (MeasureTheory.volume S) * t ^ n)
        =O[Filter.atTop]
      (fun t : ℝ => t ^ (n - 1)) := by
  sorry
