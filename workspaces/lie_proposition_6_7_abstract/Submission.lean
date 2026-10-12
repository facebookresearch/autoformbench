/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Lie_groups_lie_algebras_lie_proposition_6_7_abstract
open scoped Quaternion

namespace Submission

theorem proposition_6_7_abstract :
    ∃ e : UnitQuaternion ≃* SU2,
      Continuous (e : UnitQuaternion → SU2) ∧
      Continuous (e.symm : SU2 → UnitQuaternion) ∧
      (∃ F : ℍ → (Fin 2 × Fin 2 → ℂ),
        ContDiff ℝ (⊤ : WithTop ℕ∞) F ∧
        ∀ (q : UnitQuaternion) (i j : Fin 2),
          F q (i, j) = (e q : Matrix (Fin 2) (Fin 2) ℂ) i j) ∧
      (∃ G : (Fin 2 × Fin 2 → ℂ) → ℍ,
        ContDiff ℝ (⊤ : WithTop ℕ∞) G ∧
        ∀ A : SU2,
          G (fun ij ↦ (A : Matrix (Fin 2) (Fin 2) ℂ) ij.1 ij.2) = (e.symm A : ℍ)) := by
  sorry

end Submission
