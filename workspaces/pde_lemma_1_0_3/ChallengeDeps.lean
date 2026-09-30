import Mathlib

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace Autoform_Introduction_to_PDEs_pde_lemma_1_0_3












def heatFundamentalSolution
    (n : ℕ) (D t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / Real.rpow (4 * Real.pi * D * t) ((n : ℝ) / 2)) *
    Real.exp (-(‖x‖ ^ (2 : ℕ)) / (4 * D * t))



end Autoform_Introduction_to_PDEs_pde_lemma_1_0_3

end
