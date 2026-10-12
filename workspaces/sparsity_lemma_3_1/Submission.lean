/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Seminorm
import Mathlib.Logic.ExistsUnique
import Mathlib.Order.Filter.Extr
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_lemma_3_1
open InnerProductSpace

noncomputable section

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_lemma_3_1
theorem existsUniqueProximalPoint {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (μ : NNReal)
    (u : EuclideanSpace ℝ (Fin p)) :
    ∃! w : EuclideanSpace ℝ (Fin p),
      IsMinOn
        (fun v : EuclideanSpace ℝ (Fin p) =>
          (1 / 2 : ℝ) * ‖u - v‖ ^ 2 + (μ : ℝ) * Ω v)
        Set.univ
        w := by
  sorry






def proximalOperator {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (μ : NNReal) :
    EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
  fun u =>
    Exists.choose
      (ExistsUnique.exists (existsUniqueProximalPoint Ω μ u))
theorem existsUniqueDualBallProjection {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin p), Ω x = 0 ↔ x = 0)
    (μ : NNReal)
    (u : EuclideanSpace ℝ (Fin p)) :
    ∃! v : EuclideanSpace ℝ (Fin p),
      v ∈ dualNormBall Ω μ ∧
        IsMinOn
          (fun z : EuclideanSpace ℝ (Fin p) => ‖u - z‖)
          (dualNormBall Ω μ)
          v := by
  sorry








def dualBallProjection {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin p), Ω x = 0 ↔ x = 0)
    (μ : NNReal) :
    EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) :=
  fun u =>
    Exists.choose
      (ExistsUnique.exists
        (existsUniqueDualBallProjection Ω hΩ μ u))










theorem lemma_3_1 {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (hΩ : ∀ x : EuclideanSpace ℝ (Fin p), Ω x = 0 ↔ x = 0)
    (μ : NNReal) :
    (∀ u : EuclideanSpace ℝ (Fin p),
      dualBallProjection Ω hΩ μ u ∈ dualNormBall Ω μ ∧
        IsMaxOn
          (dualObjective u)
          (dualNormBall Ω μ)
          (dualBallProjection Ω hΩ μ u)) ∧
      proximalOperator Ω μ =
        fun u => u - dualBallProjection Ω hΩ μ u := by
  sorry

end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_lemma_3_1

