import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.LinearAlgebra.Matrix.Rank
import Submission
import ChallengeDeps
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped InnerProductSpace ENNReal


noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_2_part2



variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {d n : ℕ}














theorem theorem_2_2_part1 :
  ∃ C : ℝ, 0 < C ∧ ∀
  {d n : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : Ω → (EuclideanSpace ℝ (Fin n))} {X : Mat n d} {ε : Ω → (EuclideanSpace ℝ (Fin n))}
  {θhatLS : Ω → (EuclideanSpace ℝ (Fin d))}
  {θstar : (EuclideanSpace ℝ (Fin d))}
  {sigma2 : ℝ}
  (h_model : LinearRegressionModel Y X θstar ε)
  (h_sigma2 : 0 < sigma2)
  (h_subG : IsSubgaussian ε sigma2.toNNReal P)
  (h_LSE : IsLeastSquaresEstimator θhatLS Y X),
  ∫ ω, MSE X (θhatLS ω) θstar ∂P ≤ C * sigma2 * (X.rank : Real) / (n : Real) := Submission.Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_2_part2.theorem_2_2_part1



theorem theorem_2_2_part2 :
  ∃ C : ℝ, 0 < C ∧ ∀
  {d n : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : Ω → (EuclideanSpace ℝ (Fin n))} {X : Mat n d} {ε : Ω → (EuclideanSpace ℝ (Fin n))}
  {θhatLS : Ω → (EuclideanSpace ℝ (Fin d))}
  {θstar : (EuclideanSpace ℝ (Fin d))}
  {sigma2 : ℝ}
  {δ : ℝ}
  {r : ℝ}
  (h_model : LinearRegressionModel Y X θstar ε)
  (h_sigma2 : 0 < sigma2)
  (h_subG : IsSubgaussian ε sigma2.toNNReal P)
  (h_LSE : IsLeastSquaresEstimator θhatLS Y X)
  (h_r : r = (X.rank : ℝ))
  (h_delta : 0 < δ ∧ δ < 1),
  P {ω | MSE X (θhatLS ω) θstar
    ≤ C * sigma2 * (r + log (1 / δ)) / (n : Real)} ≥ ENNReal.ofReal (1 - δ) := Submission.Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_2_part2.theorem_2_2_part2

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_2_part2

end
