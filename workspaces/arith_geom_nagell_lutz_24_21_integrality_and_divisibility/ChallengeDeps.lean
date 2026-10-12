/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib



























noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_nagell_lutz_24_21_integrality_and_divisibility








def NagellLutzCurve (a₄ a₆ : ℤ) : WeierstrassCurve.Affine ℚ :=
  { a₁ := 0
    a₂ := 0
    a₃ := 0
    a₄ := (a₄ : ℚ)
    a₆ := (a₆ : ℚ) }


def AdditiveFiniteOrder {G : Type*} [AddMonoid G] (P : G) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ n • P = 0





def NagellLutzAffinePoint
    (a₄ a₆ : ℤ) (x₀ y₀ : ℚ)
    (hP : (NagellLutzCurve a₄ a₆).Nonsingular x₀ y₀) :
    (NagellLutzCurve a₄ a₆).Point :=
  WeierstrassCurve.Affine.Point.some x₀ y₀ hP


def NagellLutzDivisibilityInteger (a₄ a₆ : ℤ) : ℤ :=
  4 * a₄ ^ 3 + 27 * a₆ ^ 2



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_nagell_lutz_24_21_integrality_and_divisibility
