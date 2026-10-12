/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open InnerProductSpace

noncomputable section

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_lemma_3_1









def dualNorm {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (z : EuclideanSpace ℝ (Fin p)) : ℝ :=
  sSup
    (Set.range
      (fun w :
          {w : EuclideanSpace ℝ (Fin p) // Ω w ≤ 1} =>
        ⟪z, (w : EuclideanSpace ℝ (Fin p))⟫_ℝ))





def dualNormBall {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (μ : NNReal) : Set (EuclideanSpace ℝ (Fin p)) :=
  {v | dualNorm Ω v ≤ (μ : ℝ)}





def dualObjective {p : ℕ}
    (u v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  -((1 / 2 : ℝ) * (‖v - u‖ ^ 2 - ‖u‖ ^ 2))






