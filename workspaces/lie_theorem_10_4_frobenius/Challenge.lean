/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_theorem_10_4_frobenius
open scoped Manifold ContDiff
open Module

universe u𝕜 uH uE uM

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {M : Type uM} [TopologicalSpace M]
variable {I : ModelWithCorners 𝕜 E H}
variable [ChartedSpace H M]
variable [IsManifold I 1 M]

theorem theorem_10_4_frobenius [FiniteDimensional 𝕜 E]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    {k : ℕ} (D : SmoothDistribution I M k) :
    IsIntegrable D ↔ IsInvolutive D := by
  sorry
