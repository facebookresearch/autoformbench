/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


















noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_hasse_minkowski_9_10







structure RationalQuadraticForm (ι : Type*) [Fintype ι] where
  coeff : Matrix ι ι ℚ
  coeff_symm : coeff.IsSymm


def NonzeroVector {ι K : Type*} [Zero K] (x : ι → K) : Prop :=
  ∃ i : ι, x i ≠ 0





def MatrixQuadraticValue
    {ι : Type*} [Fintype ι]
    {K : Type*} [Field K] [Algebra ℚ K]
    (Q : RationalQuadraticForm ι) (x : ι → K) : K :=
  ∑ i, ∑ j, algebraMap ℚ K (Q.coeff i j) * x i * x j





def RepresentsZeroOver
    {ι : Type*} [Fintype ι]
    (Q : RationalQuadraticForm ι)
    (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  ∃ x : ι → K, NonzeroVector x ∧ MatrixQuadraticValue Q x = 0


def RepresentsZeroOverEveryFinitePadicCompletion
    {ι : Type*} [Fintype ι]
    (Q : RationalQuadraticForm ι) : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    RepresentsZeroOver Q (ℚ_[p])





def RepresentsZeroOverEveryCompletion
    {ι : Type*} [Fintype ι]
    (Q : RationalQuadraticForm ι) : Prop :=
  RepresentsZeroOver Q ℝ ∧ RepresentsZeroOverEveryFinitePadicCompletion Q



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_hasse_minkowski_9_10
