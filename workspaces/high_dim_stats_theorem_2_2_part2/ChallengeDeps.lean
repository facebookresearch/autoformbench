import Mathlib

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped InnerProductSpace ENNReal


noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_2_part2

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {d n : ℕ}


def LinearRegressionModel (Y : Ω → (EuclideanSpace ℝ (Fin n))) (X : Mat n d)
  (θstar : (EuclideanSpace ℝ (Fin d))) (ε : Ω → (EuclideanSpace ℝ (Fin n))) : Prop :=
  Y = ε + fun _ => X.toEuclideanLin θstar


abbrev MSE (X : Mat n d) (θ : (EuclideanSpace ℝ (Fin d))) (θstar : (EuclideanSpace ℝ (Fin d))) :=
  (‖X.toEuclideanLin (θ - θstar)‖) ^ 2 / (n : Real)

abbrev SquaredErrorOfY (Y : (EuclideanSpace ℝ (Fin n))) (X : Mat n d) (θ : (EuclideanSpace ℝ (Fin d))) :=
  (‖Y - X.toEuclideanLin θ‖) ^ 2

def IsLeastSquaresEstimator (θhatLS : Ω → (EuclideanSpace ℝ (Fin d)))
  (Y : Ω → (EuclideanSpace ℝ (Fin n))) (X : Mat n d) : Prop :=
  ∀ ω : Ω, ∀ θ : (EuclideanSpace ℝ (Fin d)),
  SquaredErrorOfY (Y ω) X (θhatLS ω) ≤ SquaredErrorOfY (Y ω) X θ

def IsSubgaussian (X : Ω → (EuclideanSpace ℝ (Fin n))) (sigma2 : NNReal) (μ : Measure Ω) : Prop :=
  ∀ u : (EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → HasSubgaussianMGF (fun ω => ⟪u, X ω⟫_ℝ) sigma2 μ






end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_2_part2

end
