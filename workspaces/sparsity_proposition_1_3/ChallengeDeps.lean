/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_3








def objective {n p : ℕ}
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ)
    (lam : ℝ)
    (w : Fin p → ℝ) : ℝ :=
  let r : Fin n → ℝ := y - X.mulVec w
  (1 / (2 * (n : ℝ))) * dotProduct r r
    + lam * Finset.univ.sum (fun j ↦ abs (w j))



end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_3
