import Mathlib

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped InnerProductSpace ENNReal


noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_15

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {d n : ℕ}


def LinearRegressionModel (Y : Ω → (EuclideanSpace ℝ (Fin n))) (X : Mat n d)
  (θstar : (EuclideanSpace ℝ (Fin d))) (ε : Ω → (EuclideanSpace ℝ (Fin n))) : Prop :=
  Y = ε + fun _ => X.toEuclideanLin θstar


abbrev MSE (X : Mat n d) (θ : (EuclideanSpace ℝ (Fin d))) (θstar : (EuclideanSpace ℝ (Fin d))) :=
  (‖X.toEuclideanLin (θ - θstar)‖) ^ 2 / (n : Real)


def Norm1 (d : ℕ) (θ : (EuclideanSpace ℝ (Fin d))) := ∑ j : Fin d, |θ j|

abbrev SquaredErrorLASSO (Y : (EuclideanSpace ℝ (Fin n))) (X : Mat n d) (θ : (EuclideanSpace ℝ (Fin d))) (τ : ℝ) :=
  (1 / ↑n) * (‖Y - X.toEuclideanLin θ‖)^2 + 2 * τ * (Norm1 d θ)

def IsLASSOEstimator (θhat : Ω → (EuclideanSpace ℝ (Fin d)))
  (Y : Ω → (EuclideanSpace ℝ (Fin n))) (X : Mat n d) (τ : ℝ) : Prop :=
  ∀ ω : Ω, ∀ θ : (EuclideanSpace ℝ (Fin d)),
  SquaredErrorLASSO (Y ω) X (θhat ω) τ ≤ SquaredErrorLASSO (Y ω) X θ τ

def IsSubgaussian (X : Ω → (EuclideanSpace ℝ (Fin n))) (sigma2 : NNReal) (μ : Measure Ω) : Prop :=
  ∀ u : (EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → HasSubgaussianMGF (fun ω => ⟪u, X ω⟫_ℝ) sigma2 μ

def IsNormalized (X : Mat n d) : Prop :=
  ∀ j : Fin d, (X.transpose * X).diag j ≤ n



end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_15

end
