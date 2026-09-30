/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_theorem_3_13_closed_subgroup_is_closed_lie_subgroup

universe uE uG

theorem theorem_3_13_closed_subgroup_is_closed_lie_subgroup {n : WithTop ℕ∞}
    {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG}
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) n G]
    [T2Space G] [SecondCountableTopology G]
    (K : Subgroup G)
    (hK : IsClosed (K : Set G))
    (hn : 1 ≤ n) :
    Nonempty (SmoothRealClosedLieSubgroup (n := n) (E := E) (G := G) K) := by
  exact Submission.theorem_3_13_closed_subgroup_is_closed_lie_subgroup K hK hn
