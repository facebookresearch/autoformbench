/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_proposition_2_16







abbrev DesignMatrix (n d : ℕ) :=
  Fin n → Fin d → ℝ







def ComponentwiseMeasurableMatrix
    {Ω : Type*} [MeasurableSpace Ω]
    {n d : ℕ}
    (X : Ω → DesignMatrix n d) : Prop :=
  ∀ i : Fin n, ∀ j : Fin d, Measurable (fun ω => X ω i j)







def IsRademacherSignMatrix
    {n d : ℕ}
    (A : DesignMatrix n d) : Prop :=
  ∀ i : Fin n, ∀ j : Fin d, A i j = 1 ∨ A i j = -1









def IsIidRademacherMatrix
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n d : ℕ}
    (X : Ω → DesignMatrix n d) : Prop :=
  ComponentwiseMeasurableMatrix X ∧
    μ.real {ω | IsRademacherSignMatrix (X ω)} = 1 ∧
      ∀ A : DesignMatrix n d, IsRademacherSignMatrix A →
        μ.real {ω | X ω = A} = (1 / 2 : ℝ) ^ (n * d)







def normalizedGramEntry
    {n d : ℕ}
    (X : DesignMatrix n d) (j l : Fin d) : ℝ :=
  (∑ i : Fin n, X i j * X i l) / (n : ℝ)




def identityEntry
    {d : ℕ}
    (j l : Fin d) : ℝ :=
  if j = l then 1 else 0








def HasIncoherence
    {n d : ℕ}
    (X : DesignMatrix n d) (k : ℕ) : Prop :=
  0 < k ∧
    ∀ j : Fin d, ∀ l : Fin d,
      |normalizedGramEntry X j l - identityEntry j l| ≤
        1 / (14 * (k : ℝ))



end Autoform_High_Dimensional_Statistics_high_dim_stats_proposition_2_16

end
