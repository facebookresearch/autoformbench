/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_8








noncomputable def quadraticOverLinear (x y : ℝ) : ENNReal :=
  ENNReal.ofReal (x ^ 2) / ENNReal.ofReal y










noncomputable def hNorm {p : ℕ}
    (H : Set (Fin p → ℝ)) (w : Fin p → ℝ) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (⨅ η : H,
        ∑ i : Fin p, quadraticOverLinear (w i) (η.1 i)))









noncomputable def dualNorm {p : ℕ}
    (Ω : (Fin p → ℝ) → ℝ) (κ : Fin p → ℝ) : ℝ :=
  sSup
    (Set.image
      (fun w : Fin p → ℝ => dotProduct κ w)
      {w | Ω w ≤ 1})



end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_8
