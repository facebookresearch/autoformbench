/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Tensor_Categories_tensor_cat_eigenvalue_eq_lambda_of_positive_eigenvector

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]


def MatrixNonneg (B : Matrix n n ℝ) : Prop :=
  ∀ i j, 0 ≤ B i j


def MatrixPos (B : Matrix n n ℝ) : Prop :=
  ∀ i j, 0 < B i j


def VecNonneg (v : n → ℝ) : Prop :=
  ∀ i, 0 ≤ v i


def VecPos (v : n → ℝ) : Prop :=
  ∀ i, 0 < v i


noncomputable def complexify (B : Matrix n n ℝ) : Matrix n n ℂ :=
  B.map fun x : ℝ => (x : ℂ)


noncomputable def lambda (B : Matrix n n ℝ) : ℝ :=
  (spectralRadius ℂ (Matrix.toLin' (complexify B))).toReal







end Autoform_Tensor_Categories_tensor_cat_eigenvalue_eq_lambda_of_positive_eigenvector

end
