/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

universe uE uG


namespace Autoform_Lie_groups_lie_algebras_lie_theorem_3_13_closed_subgroup_is_closed_lie_subgroup















structure SmoothRealClosedLieSubgroup {n : WithTop ℕ∞}
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) n G]
    (K : Subgroup G) where
  E_sub : Type uE
  [sub_normedAddCommGroup : NormedAddCommGroup E_sub]
  [sub_normedSpace : NormedSpace ℝ E_sub]
  [sub_finiteDimensional : FiniteDimensional ℝ E_sub]
  [sub_chartedSpace : ChartedSpace E_sub K]
  [sub_lieGroup : LieGroup (modelWithCornersSelf ℝ E_sub) n K]
  inclusion_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ E_sub)
      (modelWithCornersSelf ℝ E)
      n
      (Subtype.val : K → G)



end Autoform_Lie_groups_lie_algebras_lie_theorem_3_13_closed_subgroup_is_closed_lie_subgroup
