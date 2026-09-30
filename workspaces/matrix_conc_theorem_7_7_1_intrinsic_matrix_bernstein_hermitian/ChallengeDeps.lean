/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator





noncomputable instance matrixContinuousENorm {n : Type*} [Fintype n] [DecidableEq n] :
    ContinuousENorm (Matrix n n ℂ) := SeminormedAddGroup.toContinuousENorm


noncomputable section

namespace Autoform_Matrix_Concentration_Inequalities_matrix_conc_theorem_7_7_1_intrinsic_matrix_bernstein_hermitian

variable {Ω κ n : Type*}
variable [MeasurableSpace Ω]
variable [Fintype κ] [DecidableEq κ]
variable [Fintype n] [DecidableEq n] [Nonempty n]
















noncomputable def lambdaMax (A : Matrix n n ℂ) : ℝ :=
  sSup (spectrum ℝ A)








noncomputable def matrixVarianceHerm
    (μ : Measure Ω) (Y : Ω → Matrix n n ℂ) : Matrix n n ℂ :=
  ∫ ω, (Y ω - (∫ ω', Y ω' ∂ μ)) ^ (2 : ℕ) ∂ μ
















noncomputable def intrinsicDimension (A : Matrix n n ℂ) : ℝ :=
  Complex.re (Matrix.trace A) / ‖A‖



end Autoform_Matrix_Concentration_Inequalities_matrix_conc_theorem_7_7_1_intrinsic_matrix_bernstein_hermitian
