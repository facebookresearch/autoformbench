import Mathlib

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_2

noncomputable section





def subdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → ℝ) (x : E) : Set E :=
  {z : E | ∀ y : E, g x + inner ℝ z (y - x) ≤ g y}








def dualNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Seminorm ℝ E) (z : E) : ℝ :=
  sSup ((fun u : E => inner ℝ z u) '' Ω.closedBall 0 1)



end

end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_2
