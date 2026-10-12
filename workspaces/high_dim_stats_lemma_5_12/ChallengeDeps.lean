/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_5_12








abbrev BinaryVector (d : ℕ) :=
  Fin d → ℝ







def IsBinaryVector
    {d : ℕ}
    (omega : BinaryVector d) : Prop :=
  ∀ i : Fin d, omega i = 0 ∨ omega i = 1








def hammingDistance
    {d : ℕ}
    (omega omega' : BinaryVector d) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Fin d)).filter
      (fun i : Fin d => omega i ≠ omega' i)).card








def varshamovGilbertCardinality
    (gamma : ℝ) (d : ℕ) : ℕ :=
  Nat.floor (Real.exp (gamma ^ 2 * (d : ℝ)))





def varshamovGilbertSeparationThreshold
    (gamma : ℝ) (d : ℕ) : ℝ :=
  (1 / 2 - gamma) * (d : ℝ)











def varshamovGilbertCardinalityLowerBound
    (gamma : ℝ) (d : ℕ) : ℝ :=
  Real.exp (gamma ^ 2 * (d : ℝ) / 2)







def IsHammingSeparatedBinaryFamily
    (gamma : ℝ) (d M : ℕ)
    (omega : Fin M → BinaryVector d) : Prop :=
  (∀ j : Fin M, IsBinaryVector (omega j)) ∧
    (∀ j k : Fin M, j ≠ k →
      varshamovGilbertSeparationThreshold gamma d ≤
        (hammingDistance (omega j) (omega k) : ℝ))








def IsVarshamovGilbertExactFloorFamily
    (gamma : ℝ) (d M : ℕ)
    (omega : Fin M → BinaryVector d) : Prop :=
  M = varshamovGilbertCardinality gamma d ∧
    IsHammingSeparatedBinaryFamily gamma d M omega












def IsVarshamovGilbertLargeFamily
    (gamma : ℝ) (d M : ℕ)
    (omega : Fin M → BinaryVector d) : Prop :=
  varshamovGilbertCardinalityLowerBound gamma d ≤ (M : ℝ) ∧
    IsHammingSeparatedBinaryFamily gamma d M omega



end Autoform_High_Dimensional_Statistics_high_dim_stats_lemma_5_12

end
