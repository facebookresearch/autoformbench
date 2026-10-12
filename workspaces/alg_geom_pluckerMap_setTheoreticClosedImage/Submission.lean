/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/






















import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.Defs.Induced
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Algebraic_Geometry_I_alg_geom_pluckerMap_setTheoreticClosedImage
set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Autoform_Algebraic_Geometry_I_alg_geom_pluckerMap_setTheoreticClosedImage

universe u v w z



namespace ClassicalGrassmannian

variable {K : Type u} [Field K]
variable {n k : ℕ}

@[ext]
theorem ext {W₁ W₂ : ClassicalGrassmannian K n k}
    (h : W₁.toSubmodule = W₂.toSubmodule) : W₁ = W₂ := by
  cases W₁
  cases W₂
  simp at h
  subst h
  simp

end ClassicalGrassmannian























attribute [instance] AffineCoordinateAlgebra.commRing
attribute [instance] AffineCoordinateAlgebra.algebra



























variable (K : Type u) [Field K]
variable (n k : ℕ)









theorem pluckerLine_finrank
    (W : ClassicalGrassmannian K n k) :
    Module.finrank K (pluckerLine K n k W) = 1 := by
  sorry








def pluckerMap :
    ClassicalGrassmannian K n k →
      Projectivization K (↥(⋀[K]^k (Fin n → K))) :=
  fun W =>
    Projectivization.mk''
      (pluckerLine K n k W)
      (pluckerLine_finrank K n k W)









def GrassmannianPluckerTheoremStatement
    [IsAlgClosed K] (hkn : k ≤ n) : Prop :=
  ∃ (Gvar : ClassicalAlgebraicVarietyStructure.{u,u,u} K
        (ClassicalGrassmannian K n k))
    (Pvar : ClassicalAlgebraicVarietyStructure.{u,u,u} K
      (Projectivization K (↥(⋀[K]^k (Fin n → K))))),
    Nonempty (IsGrassmannianChartDefinedVariety K n k hkn Gvar) ∧
    Nonempty (IsProjectiveSpaceVarietyWithCoordinates
      (standardExteriorPowerBasis K n k) Pvar) ∧
    Nonempty (IsProjectiveClosedImmersionWithCoordinates
      (standardExteriorPowerBasis K n k)
      Gvar Pvar
      (pluckerMap K n k))













theorem pluckerMap_isProjectiveClosedEmbedding
    [IsAlgClosed K] (hkn : k ≤ n) :
    GrassmannianPluckerTheoremStatement K n k hkn := by
  sorry






theorem pluckerMap_setTheoreticClosedImage
    [IsAlgClosed K] (hkn : k ≤ n) :
    IsSetTheoreticProjectiveClosedEmbeddingWithCoordinates
      (standardExteriorPowerBasis K n k)
      (pluckerMap K n k) := by
  sorry

end Autoform_Algebraic_Geometry_I_alg_geom_pluckerMap_setTheoreticClosedImage

