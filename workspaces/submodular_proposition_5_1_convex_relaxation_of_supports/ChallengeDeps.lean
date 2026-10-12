/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators

noncomputable section

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_1_convex_relaxation_of_supports

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











def Submodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι, F (A ∪ B) + F (A ∩ B) ≤ F A + F B









def unitLinftyBall : Set (ι → ℝ) :=
  { w | ∀ i : ι, |w i| ≤ (1 : ℝ) }




noncomputable def supportFinset (w : ι → ℝ) : Finset ι := by
  classical
  exact (Finset.univ : Finset ι).filter (fun i : ι => w i ≠ 0)




noncomputable def supportPenalty (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  F (supportFinset (ι := ι) w)















def IsConvexEnvelopeOn
    (K : Set (ι → ℝ))
    (φ ψ : (ι → ℝ) → ℝ) : Prop :=
  ConvexOn ℝ K φ ∧
    (∀ w ∈ K, φ w ≤ ψ w) ∧
    ∀ θ : (ι → ℝ) → ℝ,
      ConvexOn ℝ K θ →
      (∀ w ∈ K, θ w ≤ ψ w) →
      ∀ w ∈ K, θ w ≤ φ w



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_1_convex_relaxation_of_supports
