import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_PDEs_pde_classMeeting13_lemma_1_0_2_of_waveEquation








def minkowskiMetric (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun μ => if μ = 0 then (-1 : ℝ) else 1)








def coordDeriv {n : ℕ} (μ : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (fderiv ℝ f x) (Pi.single μ 1)







def waveOperator {n : ℕ}
    (φ : (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
    minkowskiMetric n α β * coordDeriv α (coordDeriv β φ) x






def energyMomentumDown {n : ℕ}
    (φ : (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun μ ν =>
    coordDeriv μ φ x * coordDeriv ν φ x -
      (1 / 2 : ℝ) * minkowskiMetric n μ ν *
        (∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
          minkowskiMetric n α β * coordDeriv α φ x * coordDeriv β φ x)







def energyMomentumUp {n : ℕ}
    (φ : (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun μ ν =>
    ∑ α : Fin (n + 1), ∑ β : Fin (n + 1),
      minkowskiMetric n μ α * minkowskiMetric n ν β *
        energyMomentumDown φ x α β





end Autoform_Introduction_to_PDEs_pde_classMeeting13_lemma_1_0_2_of_waveEquation

end
