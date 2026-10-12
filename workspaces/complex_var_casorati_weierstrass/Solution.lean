/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Functions_of_a_Complex_Variable_complex_var_casorati_weierstrass
open Filter
open scoped Topology

theorem casorati_weierstrass {f : ℂ → ℂ} {c : ℂ}
    (h : EssentialSingularityAt f c) :
    ∀ a : ℂ, ∀ U : Set ℂ, ∀ ε : ℝ, 0 < ε → U ∈ 𝓝[≠] c →
      ∃ z : ℂ, z ∈ U ∧ ‖f z - a‖ < ε := by
  exact Submission.casorati_weierstrass h
