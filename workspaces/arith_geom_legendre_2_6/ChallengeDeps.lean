/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib















namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_legendre_2_6


def SquarefreeInt (n : ℤ) : Prop :=
  ∀ d : ℤ, d * d ∣ n → IsUnit d


def IntCoprime (m n : ℤ) : Prop :=
  ∃ u v : ℤ, u * m + v * n = 1


def PairwiseCoprime3 (a b c : ℤ) : Prop :=
  IntCoprime a b ∧ IntCoprime a c ∧ IntCoprime b c


def SignsNotAllSame (a b c : ℤ) : Prop :=
  ¬ ((0 < a ∧ 0 < b ∧ 0 < c) ∨ (a < 0 ∧ b < 0 ∧ c < 0))


def CongruentMod (m x y : ℤ) : Prop :=
  m ∣ x - y


def NonzeroRationalTriple (x y z : ℚ) : Prop :=
  x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0


def DiagonalConicEquationRat (a b c : ℤ) (x y z : ℚ) : Prop :=
  (a : ℚ) * x ^ 2 + (b : ℚ) * y ^ 2 + (c : ℚ) * z ^ 2 = 0


def HasNonzeroRationalSolution (a b c : ℤ) : Prop :=
  ∃ x y z : ℚ,
    NonzeroRationalTriple x y z ∧ DiagonalConicEquationRat a b c x y z





def LegendreCongruencesSolvable (a b c : ℤ) : Prop :=
  ∃ X Y Z : ℤ,
    CongruentMod a (X ^ 2) (-(b * c)) ∧
      CongruentMod b (Y ^ 2) (-(c * a)) ∧
        CongruentMod c (Z ^ 2) (-(a * b))



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_legendre_2_6
