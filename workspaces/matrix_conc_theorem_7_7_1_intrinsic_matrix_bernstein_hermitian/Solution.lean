import ChallengeDeps
import Submission

open Autoform_Matrix_Concentration_Inequalities_matrix_conc_theorem_7_7_1_intrinsic_matrix_bernstein_hermitian
open MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {Ω κ n : Type*}
variable [MeasurableSpace Ω]
variable [Fintype κ] [DecidableEq κ]
variable [Fintype n] [DecidableEq n] [Nonempty n]

theorem theorem_7_7_1_intrinsic_matrix_bernstein_hermitian (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : κ → Ω → Matrix n n ℂ)
    (V : Matrix n n ℂ)
    (L t : ℝ)
    
    (hX_measurable : ∀ k : κ, StronglyMeasurable (X k))
    (hX_integrable : ∀ k : κ, Integrable (X k) μ)
    (hY_variance_integrable :
      Integrable
        (fun ω =>
          ((∑ k : κ, X k ω) -
            (∫ ω', (∑ k : κ, X k ω') ∂ μ)) ^ (2 : ℕ)) μ)
    
    (hX_indep :
      @ProbabilityTheory.iIndepFun Ω κ _ (fun _ : κ => Matrix n n ℂ)
      (fun _ : κ => borel (Matrix n n ℂ)) (fun k => X k) μ)
    (hX_hermitian : ∀ k : κ, ∀ ω : Ω, (X k ω).IsHermitian)
    
    (hX_mean_zero : ∀ k : κ, ∫ ω, X k ω ∂ μ = 0)
    (hL_nonneg : 0 ≤ L)
    (hX_lambdaMax_bound : ∀ k : κ, ∀ᵐ ω ∂ μ, lambdaMax (X k ω) ≤ L)
    
    (hV_psd : 0 ≤ V)
    (hV_norm_pos : 0 < ‖V‖)
    (hV_upper :
      matrixVarianceHerm μ (fun ω => ∑ k : κ, X k ω) ≤ V)
    
    (ht : Real.sqrt (‖V‖) + L / 3 ≤ t) :
    (μ {ω : Ω | lambdaMax (∑ k : κ, X k ω) ≥ t}).toReal
      ≤
        4 * intrinsicDimension V *
          Real.exp ((- (t ^ 2 / 2)) / (‖V‖ + L * t / 3)) := by
  apply Submission.theorem_7_7_1_intrinsic_matrix_bernstein_hermitian <;> assumption
