/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_theorem_8_8_lieHom_exists_agrees_derivative

universe uκ uHG uHK uEG uEK uG uK

variable {𝕜 : Type uκ} [RCLike 𝕜]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable (IG : ModelWithCorners 𝕜 EG HG)
variable {HK : Type uHK} [TopologicalSpace HK]
variable {EK : Type uEK} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK]
variable (IK : ModelWithCorners 𝕜 EK HK)
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {K : Type uK} [Group K] [TopologicalSpace K] [ChartedSpace HK K]

theorem theorem_8_8_lieHom_exists_agrees_derivative [LieGroup IG (minSmoothness 𝕜 3) G]
    [LieGroup IK (minSmoothness 𝕜 3) K]
    [CompleteSpace EG] [CompleteSpace EK]
    (φ : G →* K)
    (_hφ : ContMDiff IG IK (minSmoothness 𝕜 3) (φ : G → K)) :
    ∃ Φ : GroupLieAlgebra IG G →ₗ⁅𝕜⁆ GroupLieAlgebra IK K,
      ∀ x : GroupLieAlgebra IG G,
        Φ x = lieGroupHomDerivative IG IK φ x := by
  sorry
