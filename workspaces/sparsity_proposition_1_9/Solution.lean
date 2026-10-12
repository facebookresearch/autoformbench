/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_9
open scoped BigOperators

theorem proposition_1_9 {p : ℕ} (Ω : Seminorm ℝ (Vec p))
    (hΩ_definite : ∀ w : Vec p, Ω w = 0 → w = 0) :
    IsSubquadratic Ω ↔ IsHNorm Ω := by
  exact Submission.proposition_1_9 Ω hΩ_definite
