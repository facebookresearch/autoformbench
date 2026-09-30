/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_third_fundamental_theorem_of_lie_theory
open scoped Manifold

universe u v w

theorem third_fundamental_theorem_of_lie_theory (𝕜 : Type u) [RCLike 𝕜]
    (L : Type v)
    [LieRing L] [LieAlgebra 𝕜 L]
    [FiniteDimensional 𝕜 L] :
    ∃ G : BundledFiniteDimensionalLieGroup 𝕜,
      Nonempty (G.LieAlg ≃ₗ⁅𝕜⁆ L) := by
  sorry
