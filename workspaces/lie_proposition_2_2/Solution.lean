/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_proposition_2_2

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]

theorem proposition_2_2 (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [T2Space G] [SecondCountableTopology G] [CompleteSpace E]
    [BoundarylessManifold I G] [BookLieGroup I n G] (hn : (1 : WithTop ℕ∞) ≤ n) :
    (∃ invDiff : Diffeomorph I I G G n,
        ∀ g : G, invDiff g = g⁻¹) ∧
      mfderiv I I (fun g : G => g⁻¹) (1 : G) =
        - (ContinuousLinearMap.id 𝕜 (TangentSpace I (1 : G))) := by
  exact Submission.proposition_2_2 I n hn
