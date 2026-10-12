/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_6









noncomputable def dualNorm {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (z : EuclideanSpace ℝ (Fin p)) : ℝ :=
  sSup
    ((fun w : EuclideanSpace ℝ (Fin p) => inner ℝ z w) ''
      {w : EuclideanSpace ℝ (Fin p) | Ω w ≤ 1})








noncomputable def fenchelConjugate {p : ℕ}
    (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (z : EuclideanSpace ℝ (Fin p)) : EReal :=
  ⨆ w : EuclideanSpace ℝ (Fin p),
    ((inner ℝ z w - f w : ℝ) : EReal)



end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_6
