/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory





noncomputable instance matrixContinuousENorm {n : Type*} [Fintype n] [DecidableEq n] :
    ContinuousENorm (Matrix n n ℂ) := SeminormedAddGroup.toContinuousENorm


namespace Autoform_Matrix_Concentration_Inequalities_matrix_conc_thm_3_6_1_master_bounds








scoped instance matrixMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs (MeasurableSpace (m → n → α))












noncomputable def matrixLog {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) : Matrix n n ℂ :=
  hA.isHermitian.cfc Real.log







noncomputable def lambdaMax {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  sSup (Set.range hA.eigenvalues)







noncomputable def lambdaMin {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  sInf (Set.range hA.eigenvalues)








noncomputable def matrixMgf {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] (μ : Measure Ω)
    (X : Ω → Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  ∫ ω, NormedSpace.exp ((θ : ℂ) • X ω) ∂μ








