/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_8_6
open scoped BigOperators

variable {p : ℕ}

theorem proposition_8_6 (F : Finset (Fin p) → ℝ)
    (hF : IsSubmodularSetFunction F)
    (hF0 : F ∅ = 0)
    (w : Vec (Fin p))
    (hw : IsUniqueMinimizerOn
      (quadraticObjective (lovaszExtension F)) Set.univ w) :
    IsUniqueMinimizerOn
        (fun s : Vec (Fin p) => ‖s‖)
        (basePolyhedron F)
        (-w) ∧
      ∀ χ : ℝ,
        IsMaximalMinimizer
          (cardinalityShiftedObjective F χ)
          (weakUpperLevelSet w χ) ∧
        IsMinimalMinimizer
          (cardinalityShiftedObjective F χ)
          (strictUpperLevelSet w χ) := by
  sorry
