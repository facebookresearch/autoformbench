import Mathlib

noncomputable section

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_5_1




















def matrixFractional {p : ℕ}
    (Λ : Matrix (Fin p) (Fin p) ℝ)
    (w : Fin p → ℝ) : ENNReal :=
  ⨅ x : {x : Fin p → ℝ // Λ.mulVec x = w},
    ENNReal.ofReal (dotProduct x.1 (Λ.mulVec x.1))



end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_5_1
