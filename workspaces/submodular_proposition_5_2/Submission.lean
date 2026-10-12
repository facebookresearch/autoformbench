/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_2
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Submission

theorem proposition_5_2 [Nonempty ι]
    (F : Finset ι → ℝ)
    (hF_empty : F ∅ = 0)
    (hF_submodular : IsSubmodular F)
    (hF_mono : Monotone F) :
    (IsRealVectorNorm (omegaInfinity F) ↔
        ∀ i : ι, 0 < F ({i} : Finset ι)) ∧
      ((∀ i : ι, 0 < F ({i} : Finset ι)) →
        ∀ s : ι → ℝ,
          dualNormOf (omegaInfinity F) s = dualOmegaInfinityFormula F s) := by
  sorry

end Submission
