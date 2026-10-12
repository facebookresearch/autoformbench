/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Learning_with_Submodular_Functions_submodular_prop_5_5_variational_formulation
open scoped BigOperators
open ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem prop_5_5_variational_formulation {q r : ℝ} {F : Finset α → ℝ}
    (hq : 1 < q)
    (hr : 1 < r)
    (hconj : 1 / q + 1 / r = 1)
    (hF_empty : F (∅ : Finset α) = 0)
    (hF_submod : IsSubmodularSetFunction F)
    (hF_mono : Monotone F)
    (hF_singleton_pos : ∀ k : α, 0 < F ({k} : Finset α))
    (w : α → ℝ) :
    ENNReal.ofReal (omegaQ r F w)
      = ⨅ η : α → ℝ, variationalObjective q r F w η := by
  exact Submission.prop_5_5_variational_formulation hq hr hconj hF_empty hF_submod hF_mono hF_singleton_pos w
