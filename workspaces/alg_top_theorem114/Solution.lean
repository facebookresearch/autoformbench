/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Algebraic_Topology_I_alg_top_theorem114
open CategoryTheory Limits

theorem theorem114 (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (h𝒜 : IsCover X 𝒜) :
    ∀ n : ℕ, IsIso (ASmallHomologyMap X 𝒜 n) := by
  exact Submission.theorem114 X 𝒜 h𝒜
