/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_2_2

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]














class BookLieGroup
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] : Prop
    extends ContMDiffMul I n G



end Autoform_Lie_groups_lie_algebras_lie_proposition_2_2
