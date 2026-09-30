/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped Manifold

universe u𝕜 uH uE uG

namespace Autoform_Lie_groups_lie_algebras_lie_theorem14_6

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}

variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]





noncomputable def modelToLieAlg
    (I : ModelWithCorners 𝕜 E H)
    (G : Type uG) [TopologicalSpace G] [ChartedSpace H G] [Group G]
    (v : E) : GroupLieAlgebra I G := by
  unfold GroupLieAlgebra
  unfold TangentSpace
  exact v







structure OneParameterSubgroup
    (I : ModelWithCorners 𝕜 E H)
    (G : Type uG) [TopologicalSpace G] [ChartedSpace H G] [Group G] where
  toFun : 𝕜 → G
  map_zero : toFun 0 = 1
  map_add : ∀ s t : 𝕜, toFun (s + t) = toFun s * toFun t
  contMDiff_toFun :
    ContMDiff (modelWithCornersSelf 𝕜 𝕜) I ⊤ toFun

namespace OneParameterSubgroup

instance instCoeFunOneParameterSubgroup :
    CoeFun (OneParameterSubgroup I G) (fun _ => 𝕜 → G) where
  coe γ := γ.toFun




noncomputable def tangentOneAtZero :
    TangentSpace (modelWithCornersSelf 𝕜 𝕜) (0 : 𝕜) := by
  unfold TangentSpace
  exact (1 : 𝕜)





noncomputable def velocityAtZero (γ : OneParameterSubgroup I G) :
    GroupLieAlgebra I G :=
  (mfderiv (modelWithCornersSelf 𝕜 𝕜) I
    (fun t : 𝕜 => γ t) (0 : 𝕜))
    (tangentOneAtZero (𝕜 := 𝕜))

end OneParameterSubgroup








inductive BCHGenerator where
  | X
  | Y
  deriving DecidableEq, Repr







abbrev UniversalBCHLiePolynomial : Type :=
  FreeLieAlgebra ℚ BCHGenerator






noncomputable def evalUniversalBCHLiePolynomial
    {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (p : UniversalBCHLiePolynomial) (x y : L) : L :=
  ((FreeLieAlgebra.lift ℚ)
    (fun g : BCHGenerator =>
      match g with
      | BCHGenerator.X => x
      | BCHGenerator.Y => y)) p







noncomputable def lieAlgToModel
    (I : ModelWithCorners 𝕜 E H)
    (G : Type uG) [TopologicalSpace G] [ChartedSpace H G] [Group G]
    (x : GroupLieAlgebra I G) : E := by
  unfold GroupLieAlgebra at x
  unfold TangentSpace at x
  exact x




