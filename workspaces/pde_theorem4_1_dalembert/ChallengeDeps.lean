/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Interval

namespace Autoform_Introduction_to_PDEs_pde_theorem4_1_dalembert












def IsWaveCauchySolution
    (f g : ℝ → ℝ) (u : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Set.Ici (0 : ℝ) ×ˢ Set.univ) ∧
    (∀ t x : ℝ, 0 < t →
      -iteratedDeriv 2 (fun τ : ℝ => u (τ, x)) t +
          iteratedDeriv 2 (fun y : ℝ => u (t, y)) x = 0) ∧
    (∀ x : ℝ, u (0, x) = f x) ∧
    (∀ x : ℝ,
      derivWithin (fun τ : ℝ => u (τ, x)) (Set.Ici (0 : ℝ)) 0 = g x)



end Autoform_Introduction_to_PDEs_pde_theorem4_1_dalembert
