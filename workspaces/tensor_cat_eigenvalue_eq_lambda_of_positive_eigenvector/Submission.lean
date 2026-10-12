/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Tensor_Categories_tensor_cat_eigenvalue_eq_lambda_of_positive_eigenvector
noncomputable section

open scoped BigOperators

namespace Autoform_Tensor_Categories_tensor_cat_eigenvalue_eq_lambda_of_positive_eigenvector

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
















theorem perron_frobenius_nonnegative
    {B : Matrix n n ℝ}
    (hB : MatrixNonneg B) :
    Module.End.HasEigenvalue (Matrix.toLin' B) (lambda B) ∧
    (∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' B) (lambda B) v ∧
      VecNonneg v) := by
  sorry




theorem perron_frobenius_positive
    {B : Matrix n n ℝ}
    (hB : MatrixPos B) :
    0 < lambda B ∧
    Module.End.HasEigenvalue (Matrix.toLin' B) (lambda B) ∧
    Polynomial.rootMultiplicity (lambda B : ℂ)
      (LinearMap.charpoly (Matrix.toLin' (complexify B))) = 1 ∧
    (∃ v : n → ℝ,
      Module.End.HasEigenvector (Matrix.toLin' B) (lambda B) v ∧
      VecPos v) ∧
    (∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.toLin' (complexify B)) μ →
      μ ≠ (lambda B : ℂ) →
      ‖μ‖ < lambda B) := by
  sorry



theorem eigenvalue_eq_lambda_of_positive_eigenvector
    {B : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}
    (hB : MatrixNonneg B)
    (hv : VecPos v)
    (hμv : Module.End.HasEigenvector (Matrix.toLin' B) μ v) :
    μ = lambda B := by
  sorry

end Autoform_Tensor_Categories_tensor_cat_eigenvalue_eq_lambda_of_positive_eigenvector

end

end Submission
