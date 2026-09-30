/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


























noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_northcott_25_18


abbrev Qbar : Type := AlgebraicClosure ℚ


abbrev AlgebraicProjectiveSpace (n : ℕ) : Type :=
  Projectivization Qbar (Fin (n + 1) → Qbar)


structure NumberFieldModel where
  K : Type
  [fieldK : Field K]
  [numberFieldK : NumberField K]

attribute [instance] NumberFieldModel.fieldK
attribute [instance] NumberFieldModel.numberFieldK


def mapVectorToQbar
    (M : NumberFieldModel)
    (e : M.K →ₐ[ℚ] Qbar) {n : ℕ} (v : Fin (n + 1) → M.K) : Fin (n + 1) → Qbar :=
  fun i => e (v i)








structure PointModel (n : ℕ) (P : AlgebraicProjectiveSpace n) where
  M : NumberFieldModel
  embedding : M.K →ₐ[ℚ] Qbar
  vector : Fin (n + 1) → M.K
  vector_ne_zero : vector ≠ 0
  mapped_vector_ne_zero : mapVectorToQbar M embedding vector ≠ 0
  represents_point :
    Projectivization.mk Qbar (mapVectorToQbar M embedding vector) mapped_vector_ne_zero = P


def PointModel.degree {n : ℕ} {P : AlgebraicProjectiveSpace n}
    (m : PointModel n P) : ℕ :=
  Module.finrank ℚ m.M.K









def PointModel.absoluteLogHeight {n : ℕ} {P : AlgebraicProjectiveSpace n}
    (m : PointModel n P) : ℝ :=
  Projectivization.logHeight (Projectivization.mk m.M.K m.vector m.vector_ne_zero) /
    (Module.finrank ℚ m.M.K : ℝ)


def HasDegreeAtMost (n : ℕ) (P : AlgebraicProjectiveSpace n) (d : ℕ) : Prop :=
  ∃ m : PointModel n P, m.degree ≤ d









def HasAbsoluteLogHeightAtMost
    (n : ℕ) (P : AlgebraicProjectiveSpace n) (B : ℝ) : Prop :=
  ∀ m : PointModel n P, m.absoluteLogHeight ≤ B





def NorthcottSet (B d n : ℕ) : Set (AlgebraicProjectiveSpace n) :=
  { P | HasAbsoluteLogHeightAtMost n P (B : ℝ) ∧ HasDegreeAtMost n P d }



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_northcott_25_18
