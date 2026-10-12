/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix Real

namespace Autoform_Tensor_Categories_tensor_cat_kronecker_matrix_eigenvalue

noncomputable def lambda {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  (B : Matrix n n ℂ) : ℝ :=
  (spectralRadius ℂ (Matrix.toLin' B)).toReal

def to_compl {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (B : Matrix n n ℕ)
  : Matrix n n ℂ
  := B.map fun x : ℕ => (x : ℂ)



end Autoform_Tensor_Categories_tensor_cat_kronecker_matrix_eigenvalue
