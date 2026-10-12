/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

theorem Theorem18_29 :
    (fun x : ℝ =>
        (harmonic ⌊x⌋₊ : ℝ) -
          (Real.log x + Real.eulerMascheroniConstant))
      =O[Filter.atTop]
    (fun x : ℝ => x⁻¹) := by
  sorry
