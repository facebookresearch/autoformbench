/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Connected.Basic
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Lie_groups_lie_algebras_lie_theorem_9_11_bijective
noncomputable section

universe u𝕜 uM uE uG

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_9_11_bijective

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {M : Type uM} [TopologicalSpace M]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E M)
variable (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace M G]


attribute [instance]
  LieSubgroupPresentation.instGroup
  LieSubgroupPresentation.instTopologicalSpace
  LieSubgroupPresentation.instModelTopologicalSpace
  LieSubgroupPresentation.instNormedAddCommGroup
  LieSubgroupPresentation.instNormedSpace
  LieSubgroupPresentation.instChartedSpace





variable {I G}


@[ext]
theorem ext {H K : ConnectedLieSubgroup I G} (h : H.subgroup = K.subgroup) : H = K := by
  cases H
  cases K
  simpa



variable [CompleteSpace E]
variable [LieGroup I (minSmoothness 𝕜 3) G]










theorem lieSubalgebra_lie_mem (H : ConnectedLieSubgroup I G)
    (x y : GroupLieAlgebra (presentation H).J (presentation H).carrier) :
    lieMap H ⁅x, y⁆ = ⁅lieMap H x, lieMap H y⁆ := by
  sorry












noncomputable def lieSubalgebra (H : ConnectedLieSubgroup I G) :
    LieSubalgebra 𝕜 (GroupLieAlgebra I G) where
  carrier := Set.range (lieMap H)

  zero_mem' := by
    exact ⟨0, by simp [lieMap]⟩

  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by simp⟩

  smul_mem' := by
    intro c _ hx
    rcases hx with ⟨x, rfl⟩
    exact ⟨c • x, by simp⟩

  lie_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨⁅x, y⁆, lieSubalgebra_lie_mem H x y⟩






theorem theorem_9_11_bijective
    [IsRCLikeNormedField 𝕜] [I.Boundaryless]
    [FiniteDimensional 𝕜 E] [T2Space G] [SecondCountableTopology G] :
    Function.Bijective
      (lieSubalgebra (I := I) (G := G) :
        ConnectedLieSubgroup I G → LieSubalgebra 𝕜 (GroupLieAlgebra I G)) := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_theorem_9_11_bijective


end
end Submission
