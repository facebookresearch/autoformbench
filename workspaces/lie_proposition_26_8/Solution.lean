/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_proposition_26_8

open scoped BigOperators

universe u_g u_v u_i

variable {𝔤 : Type u_g} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

theorem proposition_26_8 [LieAlgebra.IsSemisimple ℂ 𝔤]
    [LieAlgebra.IsKilling ℂ 𝔤]
    [FiniteDimensional ℂ 𝔤]
    (H : LieSubalgebra ℂ 𝔤)
    [H.IsCartanSubalgebra]
    [LieRing.IsNilpotent H]
    [LieModule.IsTriangularizable ℂ H 𝔤]
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (B : (LieAlgebra.IsKilling.rootSystem H).InvariantForm)
    (χ : Module.Dual ℂ H)
    (_hχ : χ ∈ dominantIntegralWeights
        (LieAlgebra.IsKilling.rootSystem H) b) :
    (Module.finrank ℂ (L H b χ) : ℂ) =
      weylDimensionQuotient
        (LieAlgebra.IsKilling.rootSystem H) B b χ := by
  apply Submission.proposition_26_8 <;> assumption
