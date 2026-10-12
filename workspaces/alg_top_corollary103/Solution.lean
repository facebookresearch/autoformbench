/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Algebraic_Topology_I_alg_top_corollary103
open CategoryTheory Limits AlgebraicTopology

theorem corollary103 (X : TopCat) (A B : Set ↑X)
    (hA : A.Nonempty)
    (hAB : A ⊆ B)
    (hcl : closure A ⊆ interior B)
    (hdef : IsDeformationRetract (Subspace X B) ((↑) ⁻¹' A)) :
    ∀ n : ℕ, IsIso (RelativeHomologyMap (collapsePairMap X A) n) := by
  exact Submission.corollary103 X A B hA hAB hcl hdef
