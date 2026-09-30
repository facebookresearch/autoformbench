import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Convex.Basic
import Batteries.Data.Fin.Basic
import Mathlib.Algebra.Notation.Support
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_11.HardThresholdingEstimator
open _root_.Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_11
open _root_.Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_11.IsSubGaussianSequenceModel
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped InnerProductSpace ENNReal


noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_11



variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {d n : ℕ}












theorem mse_of_ort (X : Mat n d) (θ : (EuclideanSpace ℝ (Fin d)))
    (θstar : (EuclideanSpace ℝ (Fin d))) (h_n : 0 < n) (h_ORT : AssumptionORT X) :
  MSE X θ θstar = ( ‖θ - θstar‖ )^2
  := by
    sorry















theorem subGaussianSequenceModel_of_ort (Y : Ω → (EuclideanSpace ℝ (Fin n))) (X : Mat n d) (θstar : (EuclideanSpace ℝ (Fin d)))
  (ε : Ω → (EuclideanSpace ℝ (Fin n))) (sigma2 : NNReal) (μ : Measure Ω)
  (h_model : LinearRegressionModel Y X θstar ε)
  (h_subG : IsSubgaussian ε sigma2 μ)
  (h_n : 0 < n)
  (h_ORT : AssumptionORT X)
  :
  IsSubGaussianSequenceModel d n sigma2
    (fun ω => (1 / (n : Real)) • X.transpose.toEuclideanLin (Y ω)) θstar
    (fun ω => (1 / (n : Real)) • X.transpose.toEuclideanLin (ε ω)) μ
  := by
    sorry



theorem ort_of_subGaussianSequenceModel (d n : ℕ) (sigma2 : NNReal)
  (y : Ω → (EuclideanSpace ℝ (Fin d))) (θstar : (EuclideanSpace ℝ (Fin d)))
  (ξ : Ω → (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω)
  (h_subGSM : IsSubGaussianSequenceModel d n sigma2 y θstar ξ μ)
  (h_d : 0 < d) (h_n : 0 < n) (h_dn : d ≤ n)
  :
  ∃ (X : Mat n d) (Y : Ω → (EuclideanSpace ℝ (Fin n)))
      (ε : Ω → (EuclideanSpace ℝ (Fin n))),
    LinearRegressionModel Y X θstar ε ∧
    IsSubgaussian ε sigma2 μ ∧
    AssumptionORT X ∧
    y = (fun ω => (1 / (n : ℝ)) • X.transpose.toEuclideanLin (Y ω)) ∧
    ξ = (fun ω => (1 / (n : ℝ)) • X.transpose.toEuclideanLin (ε ω))
  := by
    sorry






theorem theorem_2_11 :
  ∃ C : ℝ, 0 < C ∧ ∀
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {d n k : ℕ}
  {sigma : ℝ}
  {y : Ω → (EuclideanSpace ℝ (Fin d))}
  {θstar : (EuclideanSpace ℝ (Fin d))}
  {ξ : Ω → (EuclideanSpace ℝ (Fin d))}
  {τ : ℝ}
  {θhatHRD : Ω → (EuclideanSpace ℝ (Fin d))}
  {δ : ℝ}
  (h_model : IsSubGaussianSequenceModel d n (sigma^2).toNNReal y θstar ξ P)
  (h_meas : Measurable y)
  (h_θhatHRD : HardThresholdingEstimator θhatHRD y τ)
  (h_τ : τ = sigma * √(2 * log (2 * ↑d / δ) / ↑n) )
  (h_k : k = Fintype.card { i : Fin d // θstar i ≠ 0 } )
  (h_n : 0 < n)
  (h_sigma : 0 < sigma)
  (h_delta : 0 < δ ∧ δ < 1),
  ∃ A : Set Ω,
    MeasurableSet A ∧
    P A ≥ ENNReal.ofReal (1 - δ) ∧
    ∀ ω : A,
      (‖θhatHRD ω - θstar‖)^2 ≤ C * sigma^2 * ↑k * log (2 * ↑d / δ) / ↑n ∧
    ∀ ω : A,
      (minCond3τ θstar τ) → ∀ j : Fin d, (θhatHRD ω j ≠ 0 ↔ θstar j ≠ 0)
  := by
    sorry

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_11

end

end Submission
