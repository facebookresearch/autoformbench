/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Autoform_Theory_of_Probability_probability_deMoivreLaplace_limit_theorem

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

namespace Lecture12










noncomputable def bernoulliPartialSum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, X i ω










noncomputable def standardizedBernoulliPartialSum
    {Ω : Type*} (p : unitInterval) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω =>
    (bernoulliPartialSum X n ω - (n : ℝ) * (p : ℝ)) /
      Real.sqrt ((n : ℝ) * (p : ℝ) * (1 - (p : ℝ)))



end Lecture12

end Autoform_Theory_of_Probability_probability_deMoivreLaplace_limit_theorem
