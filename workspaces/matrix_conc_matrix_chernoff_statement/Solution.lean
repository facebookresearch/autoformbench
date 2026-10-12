/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.CStarAlgebra.Matrix
import Submission
import ChallengeDeps

open Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory




namespace Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement

noncomputable section





















theorem isHermitian_integral
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    (Pr : Measure Ω) (A : Ω → Matrix n n ℂ)
    (hA : ∀ᵐ ω ∂Pr, (A ω).IsHermitian)
    (hA_int : Integrable A Pr) :
    (∫ ω, A ω ∂Pr).IsHermitian := by apply Submission.Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement.isHermitian_integral <;> assumption







theorem integrable_univ_sum_matrix
    {Ω ι n : Type*} [MeasurableSpace Ω] [Fintype ι]
    [Fintype n] [DecidableEq n]
    (Pr : Measure Ω) (A : ι → Ω → Matrix n n ℂ)
    (hA : ∀ i, Integrable (A i) Pr) :
    Integrable (fun ω => ∑ i, A i ω) Pr := by apply Submission.Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement.integrable_univ_sum_matrix <;> assumption










theorem matrix_chernoff_statement
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {d : ℕ} [Nonempty (Fin d)]
    (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ι → Ω → Matrix (Fin d) (Fin d) ℂ)
    (L : ℝ)
    (hL_pos : 0 < L)
    
    (h_indep : iIndepFun X Pr)
    
    
    (hX_int : ∀ k, Integrable (X k) Pr)
    
    (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    
    (hX_min_nonneg :
      ∀ k ω, 0 ≤ hermitianMinEigenvalue (X k ω) (hX_herm k ω))
    
    (hX_max_le :
      ∀ k ω, hermitianMaxEigenvalue (X k ω) (hX_herm k ω) ≤ L) :
    
    let Y : Ω → Matrix (Fin d) (Fin d) ℂ := fun ω => ∑ k, X k ω
    let hY : ∀ ω, (Y ω).IsHermitian := fun ω => by
      dsimp [Y]
      exact isHermitian_univ_sum
        (fun k => X k ω)
        (fun k => hX_herm k ω)
    let hY_int : Integrable Y Pr := by
      dsimp [Y]
      exact integrable_univ_sum_matrix Pr X hX_int
    
    
    let EY : Matrix (Fin d) (Fin d) ℂ := ∫ ω, Y ω ∂Pr
    let hEY : EY.IsHermitian := by
      dsimp [EY]
      exact isHermitian_integral Pr Y
        (Filter.Eventually.of_forall hY)
        hY_int
    
    let μmin : ℝ := hermitianMinEigenvalue EY hEY
    
    let μmax : ℝ := hermitianMaxEigenvalue EY hEY

    
    (∀ θ : ℝ, 0 < θ →
      (∫ ω : Ω, hermitianMinEigenvalue (Y ω) (hY ω) ∂Pr)
        ≥ ((1 - Real.exp (-θ)) / θ) * μmin
          - (1 / θ) * L * Real.log (d : ℝ))
    ∧
    
    (∀ θ : ℝ, 0 < θ →
      (∫ ω : Ω, hermitianMaxEigenvalue (Y ω) (hY ω) ∂Pr)
        ≤ ((Real.exp θ - 1) / θ) * μmax
          + (1 / θ) * L * Real.log (d : ℝ))
    ∧
    
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      Pr.real {ω : Ω |
          hermitianMinEigenvalue (Y ω) (hY ω) ≤ (1 - ε) * μmin}
        ≤ (d : ℝ) *
            Real.rpow
              (Real.exp (-ε) / Real.rpow (1 - ε) (1 - ε))
              (μmin / L))
    ∧
    
    (∀ ε : ℝ, 0 ≤ ε →
      Pr.real {ω : Ω |
          (1 + ε) * μmax ≤ hermitianMaxEigenvalue (Y ω) (hY ω)}
        ≤ (d : ℝ) *
            Real.rpow
              (Real.exp ε / Real.rpow (1 + ε) (1 + ε))
              (μmax / L)) := by apply Submission.Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement.matrix_chernoff_statement <;> assumption

end

end Autoform_Matrix_Concentration_Inequalities_matrix_conc_matrix_chernoff_statement
