/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped Manifold

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_20_10

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [Group G] [TopologicalSpace G] [ChartedSpace E G]
variable [LieGroup 𝓘(ℂ, E) (minSmoothness ℂ 3) G]










noncomputable def AdActionOf (g : G) :
    GroupLieAlgebra 𝓘(ℂ, E) G → GroupLieAlgebra 𝓘(ℂ, E) G :=
  fun v => cast (by simp [GroupLieAlgebra, MulAut.conj])
      (((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (MulAut.conj g) 1) v) :
        TangentSpace 𝓘(ℂ, E) (MulAut.conj g 1))
















end Autoform_Lie_groups_lie_algebras_lie_theorem_20_10

end