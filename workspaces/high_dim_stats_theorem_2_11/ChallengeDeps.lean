import Mathlib

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped InnerProductSpace ENNReal


noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_11

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {d n : ℕ}


def LinearRegressionModel (Y : Ω → (EuclideanSpace ℝ (Fin n))) (X : Mat n d)
  (θstar : (EuclideanSpace ℝ (Fin d))) (ε : Ω → (EuclideanSpace ℝ (Fin n))) : Prop :=
  Y = ε + fun _ => X.toEuclideanLin θstar


abbrev MSE (X : Mat n d) (θ : (EuclideanSpace ℝ (Fin d))) (θstar : (EuclideanSpace ℝ (Fin d))) :=
  (‖X.toEuclideanLin (θ - θstar)‖) ^ 2 / (n : Real)

def IsSubgaussian (X : Ω → (EuclideanSpace ℝ (Fin n))) (sigma2 : NNReal) (μ : Measure Ω) : Prop :=
  ∀ u : (EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → HasSubgaussianMGF (fun ω => ⟪u, X ω⟫_ℝ) sigma2 μ

def AssumptionORT (X : Mat n d) : Prop := X.transpose * X = (n : Real) • (1 : Mat d d)




structure IsSubGaussianSequenceModel (d n : ℕ) (sigma2 : NNReal)
  (y : Ω → (EuclideanSpace ℝ (Fin d))) (θstar : (EuclideanSpace ℝ (Fin d))) (ξ : Ω → (EuclideanSpace ℝ (Fin d))) (μ : Measure Ω) : Prop where
  model : y = ξ + fun _ => θstar
  subG : IsSubgaussian (n := d) ξ (sigma2 / (n : NNReal)) μ















structure HardThresholdingEstimator (θ : Ω → (EuclideanSpace ℝ (Fin d))) (y : Ω → (EuclideanSpace ℝ (Fin d))) (τ : ℝ) : Prop where
  support_c : ∀ ω : Ω, ∀ j : Fin d, 2 * τ ≥ |y ω j| → θ ω j = 0
  otherwise : ∀ ω : Ω, ∀ j : Fin d, 2 * τ < |y ω j| → θ ω j = y ω j


abbrev minCond3τ (θ : (EuclideanSpace ℝ (Fin d))) (τ : ℝ) : Prop :=
  ∀ j : Fin d, θ j ≠ 0 → 3 * τ < |θ j|



end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_11

end
