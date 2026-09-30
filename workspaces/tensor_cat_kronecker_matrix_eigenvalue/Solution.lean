import ChallengeDeps
import Submission

open Autoform_Tensor_Categories_tensor_cat_kronecker_matrix_eigenvalue
open Matrix Real

theorem kronecker_matrix_eigenvalue {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m] (B : Matrix m m ℕ)
    (h_eq :
      lambda ((to_compl B) * (to_compl B)ᵀ) = (lambda (to_compl B)) ^ 2)
    (h_lt : lambda (to_compl B) < 2) :
    ∃ n : ℕ, n ≥ 2 ∧
      lambda (to_compl B) =
        2 * Real.cos (Real.pi / (n : ℝ)) := by
  exact Submission.kronecker_matrix_eigenvalue B h_eq h_lt
