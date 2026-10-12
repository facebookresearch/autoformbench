/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open NNReal

namespace Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_lemma_3_3

universe u














noncomputable def proximalOperator
    {E : Type u} [NormedAddCommGroup E]
    (μ : ℝ≥0) (Φ : E → ℝ) (u : E) : E :=
  letI : Nonempty E := ⟨0⟩
  Classical.epsilon fun w =>
    IsMinOn
      (fun z => ‖u - z‖ ^ 2 / 2 + (μ : ℝ) * Φ z)
      Set.univ
      w










def IsMonotonicNorm
    {p : ℕ}
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p))) : Prop :=
  (∀ x : EuclideanSpace ℝ (Fin p), Ω x = 0 ↔ x = 0) ∧
    ∀ v w : EuclideanSpace ℝ (Fin p),
      (∀ i : Fin p, |v i| ≤ |w i|) →
        Ω v ≤ Ω w

variable {p : ℕ}
variable {H : Fin p → Type u}
variable [(i : Fin p) → NormedAddCommGroup (H i)]
variable [(i : Fin p) → InnerProductSpace ℝ (H i)]
variable [(i : Fin p) → CompleteSpace (H i)]



















noncomputable def componentNorms
    (g : PiLp 2 H) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun i : Fin p => ‖g i‖








noncomputable def liftedNorm
    (Ω : Seminorm ℝ (EuclideanSpace ℝ (Fin p)))
    (h : PiLp 2 H) : ℝ :=
  Ω (componentNorms h)



end Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_lemma_3_3
