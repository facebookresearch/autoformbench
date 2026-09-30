/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mazur_24_20

















noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mazur_24_20



theorem EllipticCurveRationalTorsionSubgroup_add_mem
    (E : WeierstrassCurve.Affine ℚ) [WeierstrassCurve.IsElliptic E]
    (P Q : E.Point) (hP : ∃ m : ℕ, m ≠ 0 ∧ m • P = 0)
    (hQ : ∃ n : ℕ, n ≠ 0 ∧ n • Q = 0) :
    ∃ k : ℕ, k ≠ 0 ∧ k • (P + Q) = 0 := by
  
  sorry


theorem EllipticCurveRationalTorsionSubgroup_neg_mem
    (E : WeierstrassCurve.Affine ℚ) [WeierstrassCurve.IsElliptic E]
    (n : ℕ) (P : E.Point) (hn_ne : n ≠ 0) (hnP : n • P = 0) :
    n • -P = 0 := by
  
  sorry











def EllipticCurveRationalTorsionSubgroup
    (E : WeierstrassCurve.Affine ℚ) [WeierstrassCurve.IsElliptic E] :
    AddSubgroup E.Point where
  carrier := { P : E.Point | ∃ n : ℕ, n ≠ 0 ∧ n • P = 0 }
  zero_mem' := by
    refine ⟨1, by norm_num, ?_⟩
    simp
  add_mem' := by
    intro P Q hP hQ
    exact EllipticCurveRationalTorsionSubgroup_add_mem E P Q hP hQ
  neg_mem' := by
    intro P hP
    rcases hP with ⟨n, hn_ne, hnP⟩
    exact ⟨n, hn_ne, EllipticCurveRationalTorsionSubgroup_neg_mem E n P hn_ne hnP⟩









theorem mazur_24_20
    (E : WeierstrassCurve.Affine ℚ) [WeierstrassCurve.IsElliptic E] :
    IsMazurTorsionGroup (EllipticCurveRationalTorsionSubgroup E) := by
  sorry

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_mazur_24_20

end