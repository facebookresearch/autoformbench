/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







def IsSubmodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι, F A + F B ≥ F (A ∪ B) + F (A ∩ B)







def IsRealVectorNorm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (N : E → ℝ) : Prop :=
  (∃ p : Seminorm ℝ E, ∀ x : E, p x = N x) ∧
    ∀ x : E, N x = 0 → x = 0









noncomputable def lovaszExtension (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ := by
  classical
  exact
    ∑ a ∈ ((Finset.univ : Finset ι).image w),
      a *
        (F ((Finset.univ : Finset ι).filter (fun i : ι => a ≤ w i)) -
         F ((Finset.univ : Finset ι).filter (fun i : ι => a < w i)))




noncomputable def omegaInfinity (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  lovaszExtension F (fun i : ι => |w i|)








noncomputable def dualNormOf (N : (ι → ℝ) → ℝ) (s : ι → ℝ) : ℝ :=
  sSup { r : ℝ | ∃ w : ι → ℝ, N w ≤ 1 ∧ r = |∑ i : ι, s i * w i| }




def nonemptySubsets (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Finset (Finset ι) :=
  ((Finset.univ : Finset ι).powerset).erase ∅

theorem nonemptySubsets_nonempty [Nonempty ι] :
    (nonemptySubsets ι).Nonempty := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  refine ⟨({i} : Finset ι), ?_⟩
  simp [nonemptySubsets, i]







noncomputable def dualOmegaInfinityFormula [Nonempty ι]
    (F : Finset ι → ℝ) (s : ι → ℝ) : ℝ :=
  (nonemptySubsets ι).sup'
    (nonemptySubsets_nonempty (ι := ι))
    (fun A : Finset ι => (∑ i ∈ A, |s i|) / F A)



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_2
