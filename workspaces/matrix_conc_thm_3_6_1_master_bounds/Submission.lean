import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Matrix_Concentration_Inequalities_matrix_conc_thm_3_6_1_master_bounds
noncomputable section

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory




namespace Autoform_Matrix_Concentration_Inequalities_matrix_conc_thm_3_6_1_master_bounds



















theorem matrixMgf_posDef {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Matrix n n ℂ} {θ : ℝ}
    (hX : ∀ ω, (X ω).IsHermitian)
    (h_int : Integrable (fun ω => NormedSpace.exp ((θ : ℂ) • X ω)) μ) :
    (matrixMgf μ X θ).PosDef := by
  sorry











noncomputable def matrixCgf {Ω n : Type*} [MeasurableSpace Ω]
    [Fintype n] [DecidableEq n] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix n n ℂ) (hX : ∀ ω, (X ω).IsHermitian)
    (h_exp_int : ∀ θ : ℝ,
      Integrable (fun ω => NormedSpace.exp ((θ : ℂ) • X ω)) μ)
    (θ : ℝ) : Matrix n n ℂ :=
  matrixLog (matrixMgf μ X θ)
    (matrixMgf_posDef (μ := μ) (X := X) (θ := θ) hX (h_exp_int θ))









theorem sum_isHermitian {ι n : Type*} [Fintype ι]
    {A : ι → Matrix n n ℂ}
    (hA : ∀ i : ι, (A i).IsHermitian) :
    (∑ i : ι, A i).IsHermitian := by
  sorry







noncomputable def lambdaMaxSum {Ω ι n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (X : ι → Ω → Matrix n n ℂ)
    (hX : ∀ i : ι, ∀ ω : Ω, (X i ω).IsHermitian) : Ω → ℝ :=
  fun ω =>
    lambdaMax (∑ i : ι, X i ω)
      (sum_isHermitian (A := fun i : ι => X i ω) (fun i => hX i ω))







noncomputable def lambdaMinSum {Ω ι n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n] [Nonempty n]
    (X : ι → Ω → Matrix n n ℂ)
    (hX : ∀ i : ι, ∀ ω : Ω, (X i ω).IsHermitian) : Ω → ℝ :=
  fun ω =>
    lambdaMin (∑ i : ι, X i ω)
      (sum_isHermitian (A := fun i : ι => X i ω) (fun i => hX i ω))
















noncomputable def traceExpCgfSum {Ω ι n : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → Matrix n n ℂ)
    (hX : ∀ i : ι, ∀ ω : Ω, (X i ω).IsHermitian)
    (h_exp_int : ∀ i : ι, ∀ θ : ℝ,
      Integrable (fun ω => NormedSpace.exp ((θ : ℂ) • X i ω)) μ)
    (θ : ℝ) : ℝ :=
  Complex.re
    ((NormedSpace.exp
      (∑ i : ι,
        matrixCgf μ (X i) (hX i) (fun θ' => h_exp_int i θ') θ)).trace)

























theorem thm_3_6_1_master_bounds
    {Ω ι n : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ι → Ω → Matrix n n ℂ)
    (hX_meas : ∀ i : ι, Measurable (X i))
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ i : ι, ∀ ω : Ω, (X i ω).IsHermitian)
    (h_exp_int : ∀ i : ι, ∀ θ : ℝ,
      Integrable (fun ω => NormedSpace.exp ((θ : ℂ) • X i ω)) μ)
    (h_lmax_int : Integrable (lambdaMaxSum X hX) μ)
    (h_lmin_int : Integrable (lambdaMinSum X hX) μ) :
    (∫ ω, lambdaMaxSum X hX ω ∂μ
      ≤ ⨅ θ : {θ : ℝ // 0 < θ},
          (1 / θ.1) * Real.log (traceExpCgfSum μ X hX h_exp_int θ.1))
    ∧
    ((⨆ θ : {θ : ℝ // θ < 0},
          (1 / θ.1) * Real.log (traceExpCgfSum μ X hX h_exp_int θ.1))
      ≤ ∫ ω, lambdaMinSum X hX ω ∂μ)
    ∧
    (∀ t : ℝ,
      (μ {ω | lambdaMaxSum X hX ω ≥ t}).toReal
        ≤ ⨅ θ : {θ : ℝ // 0 < θ},
            Real.exp (- θ.1 * t) * traceExpCgfSum μ X hX h_exp_int θ.1)
    ∧
    (∀ t : ℝ,
      (μ {ω | lambdaMinSum X hX ω ≤ t}).toReal
        ≤ ⨅ θ : {θ : ℝ // θ < 0},
            Real.exp (- θ.1 * t) * traceExpCgfSum μ X hX h_exp_int θ.1) := by
  sorry

end Autoform_Matrix_Concentration_Inequalities_matrix_conc_thm_3_6_1_master_bounds

