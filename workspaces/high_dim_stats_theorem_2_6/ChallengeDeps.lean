/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Nat
open scoped InnerProductSpace ENNReal


noncomputable section

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_6

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

def IsSubgaussian (X : Ω → (EuclideanSpace ℝ (Fin n))) (sigma2 : NNReal) (μ : Measure Ω) : Prop :=
  ∀ u : (EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → HasSubgaussianMGF (fun ω => ⟪u, X ω⟫_ℝ) sigma2 μ


def SupportCard (d : ℕ) (θ : (EuclideanSpace ℝ (Fin d))) := Fintype.card { j : Fin d // θ j ≠ 0 }

abbrev B0 (d : ℕ) (k : ℕ) : Set ((EuclideanSpace ℝ (Fin d))) := {θ | SupportCard d θ ≤ k}

structure IsConstrainedLeastSquaresEstimator (K : Set ((EuclideanSpace ℝ (Fin d)))) (θhatLS : Ω → (EuclideanSpace ℝ (Fin d)))
  (Y : Ω → (EuclideanSpace ℝ (Fin n))) (X : Mat n d) : Prop where
  minimize : ∀ ω : Ω, ∀ θ : K, SquaredErrorOfY (Y ω) X (θhatLS ω) ≤ SquaredErrorOfY (Y ω) X θ
  range : ∀ ω : Ω, θhatLS ω ∈ K



end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_6

end
