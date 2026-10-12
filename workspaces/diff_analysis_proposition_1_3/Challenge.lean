/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe u

theorem proposition_1_3 {𝕜 : Type u} [RCLike 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
    (u : V →ₗ[ℝ] ℝ) :
    (Continuous u ↔ ContinuousAt u 0) ∧
    (Continuous u ↔ ∃ C : ℝ, ∀ v : V, ‖v‖ ≤ 1 → ‖u v‖ ≤ C) ∧
    (Continuous u ↔ ∃ C : ℝ, ∀ v : V, ‖u v‖ ≤ C * ‖v‖) := by
  sorry
