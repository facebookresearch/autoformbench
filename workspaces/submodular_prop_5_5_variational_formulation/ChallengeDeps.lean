/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators
open ENNReal

namespace Autoform_Learning_with_Submodular_Functions_submodular_prop_5_5_variational_formulation

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]























def IsSubmodularSetFunction (F : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, F (A ∪ B) + F (A ∩ B) ≤ F A + F B








noncomputable def lovaszExtension (F : Finset α → ℝ) (w : α → ℝ) : ℝ := by
  classical
  exact
    ∑ a ∈ (Finset.univ.image w),
      a *
        (F (Finset.univ.filter fun i : α => a ≤ w i) -
         F (Finset.univ.filter fun i : α => a < w i))






noncomputable def lpNormOn (p : ℝ) (x : α → ℝ) (A : Finset α) : ℝ :=
  Real.rpow (∑ i ∈ A, Real.rpow |x i| p) (1 / p)






noncomputable def omegaQStar (r : ℝ) (F : Finset α → ℝ) (s : α → ℝ) : ℝ :=
  sSup
    {c : ℝ |
      ∃ A : Finset α,
        A.Nonempty ∧
          c = lpNormOn r s A / Real.rpow (F A) (1 / r)}







noncomputable def omegaQ (r : ℝ) (F : Finset α → ℝ) (w : α → ℝ) : ℝ :=
  sSup
    {c : ℝ |
      ∃ s : α → ℝ,
        omegaQStar r F s ≤ 1 ∧
          c = ∑ i, w i * s i}










noncomputable def variationalTerm (q : ℝ) (w η : α → ℝ) (k : α) : ℝ≥0∞ := by
  classical
  exact
    if w k = 0 then
      0
    else if 0 < η k then
      ENNReal.ofReal
        (Real.rpow |w k| q / Real.rpow (η k) (q - 1))
    else
      ⊤








noncomputable def variationalObjective
    (q r : ℝ) (F : Finset α → ℝ) (w η : α → ℝ) : ℝ≥0∞ := by
  classical
  exact
    if ∀ k : α, 0 ≤ η k then
      ENNReal.ofReal (1 / q) * (∑ k, variationalTerm q w η k)
        + ENNReal.ofReal (1 / r) * ENNReal.ofReal (lovaszExtension F η)
    else
      ⊤



end Autoform_Learning_with_Submodular_Functions_submodular_prop_5_5_variational_formulation
