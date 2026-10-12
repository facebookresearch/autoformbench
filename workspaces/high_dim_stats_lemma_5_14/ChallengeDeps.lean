/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_5_14








abbrev BinaryVector (d : ℕ) :=
  Fin d → ℝ







def IsBinaryVector
    {d : ℕ}
    (omega : BinaryVector d) : Prop :=
  ∀ i : Fin d, omega i = 0 ∨ omega i = 1






def ellZeroNorm
    {d : ℕ}
    (omega : BinaryVector d) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Fin d)).filter
      (fun i : Fin d => omega i ≠ 0)).card








def hammingDistance
    {d : ℕ}
    (omega omega' : BinaryVector d) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Fin d)).filter
      (fun i : Fin d => omega i ≠ omega' i)).card





def sparseVGSeparationThreshold
    (k : ℕ) : ℝ :=
  (k : ℝ) / 2





def sparseVGLogCardinalityLowerBound
    (d k : ℕ) : ℝ :=
  ((k : ℝ) / 8) *
    Real.log (1 + (d : ℝ) / (2 * (k : ℝ)))















def IsSparseVarshamovGilbertFamily
    (d k M : ℕ)
    (omega : Fin M → BinaryVector d) : Prop :=
  0 < M ∧
    (∀ j : Fin M, IsBinaryVector (omega j)) ∧
      (∀ j : Fin M, ellZeroNorm (omega j) = k) ∧
        (∀ i j : Fin M, i ≠ j →
          sparseVGSeparationThreshold k ≤
            (hammingDistance (omega i) (omega j) : ℝ)) ∧
          sparseVGLogCardinalityLowerBound d k ≤ Real.log (M : ℝ)



end Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_5_14

end
