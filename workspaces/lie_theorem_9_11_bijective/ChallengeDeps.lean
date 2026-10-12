/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

universe u𝕜 uM uE uG

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_9_11_bijective

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {M : Type uM} [TopologicalSpace M]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (I : ModelWithCorners 𝕜 E M)
variable (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace M G]








structure LieSubgroupPresentation (S : Subgroup G) where
  carrier : Type uG
  [instGroup : Group carrier]
  [instTopologicalSpace : TopologicalSpace carrier]
  [instT2Space : T2Space carrier]
  [instSecondCountableTopology : SecondCountableTopology carrier]
  modelSpace : Type uM
  [instModelTopologicalSpace : TopologicalSpace modelSpace]
  modelVector : Type uE
  [instNormedAddCommGroup : NormedAddCommGroup modelVector]
  [instNormedSpace : NormedSpace 𝕜 modelVector]
  [instCompleteSpace : CompleteSpace modelVector]
  [instFiniteDimensional : FiniteDimensional 𝕜 modelVector]
  J : ModelWithCorners 𝕜 modelVector modelSpace
  [instChartedSpace : ChartedSpace modelSpace carrier]
  [instLieGroup : LieGroup J (minSmoothness 𝕜 3) carrier]
  [instConnectedSpace : ConnectedSpace carrier]
  incl : carrier →* G
  incl_injective : Function.Injective (incl : carrier → G)
  incl_range : incl.range = S

  
  incl_smooth : ContMDiff J I (minSmoothness 𝕜 3) (incl : carrier → G)

  
  incl_immersion : Manifold.IsImmersion J I (minSmoothness 𝕜 3) (incl : carrier → G)

attribute [instance]
  LieSubgroupPresentation.instGroup
  LieSubgroupPresentation.instTopologicalSpace
  LieSubgroupPresentation.instModelTopologicalSpace
  LieSubgroupPresentation.instNormedAddCommGroup
  LieSubgroupPresentation.instNormedSpace
  LieSubgroupPresentation.instChartedSpace









abbrev IsConnectedLieSubgroup (S : Subgroup G) : Prop :=
  Nonempty (LieSubgroupPresentation I G S)





structure ConnectedLieSubgroup where
  subgroup : Subgroup G
  is_lie_subgroup : IsConnectedLieSubgroup I G subgroup

variable {I G}


noncomputable def presentation (H : ConnectedLieSubgroup I G) :
    LieSubgroupPresentation I G H.subgroup :=
  Classical.choice H.is_lie_subgroup

variable [CompleteSpace E]
variable [LieGroup I (minSmoothness 𝕜 3) G]








noncomputable def lieMap (H : ConnectedLieSubgroup I G) :
    GroupLieAlgebra (presentation H).J (presentation H).carrier →L[𝕜]
      GroupLieAlgebra I G := by
  let P := presentation H
  change GroupLieAlgebra P.J P.carrier →L[𝕜] GroupLieAlgebra I G
  exact (mfderiv P.J I (P.incl : P.carrier → G) (1 : P.carrier))






end Autoform_Lie_groups_lie_algebras_lie_theorem_9_11_bijective

end