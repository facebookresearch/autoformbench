/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_lemma_3_3
open NNReal

universe u

variable {p : ℕ}
variable {H : Fin p → Type u}
variable [(i : Fin p) → NormedAddCommGroup (H i)]
variable [(i : Fin p) → InnerProductSpace ℝ (H i)]
variable [(i : Fin p) → CompleteSpace (H i)]

theorem lemma_3_3 (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (hΩ : IsMonotonicNorm Ω)
    (μ : ℝ≥0)
    (g : PiLp 2 H) :
    proximalOperator μ (liftedNorm Ω) g =
      WithLp.toLp 2 fun i : Fin p =>
        (proximalOperator μ (fun x => Ω x) (componentNorms g)) i •
          NormedSpace.normalize (g i) := by
  exact Submission.lemma_3_3 Ω hΩ μ g
