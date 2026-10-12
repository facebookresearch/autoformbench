/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Introduction_to_PDEs_pde_classMeeting19_proposition_2_0_1
open MeasureTheory
open scoped ContDiff

theorem classMeeting19_proposition_2_0_1 {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ_smooth : ContDiff ℝ ∞ φ)
    (hφ_compact : HasCompactSupport φ)
    (ψ : ℝ → EuclideanSpace ℝ (Fin n) → ℂ)
    (hψ :
      ∀ s : ℝ, ∀ x : EuclideanSpace ℝ (Fin n),
        ψ s x =
          FourierTransformInv.fourierInv
            (fun ξ : EuclideanSpace ℝ (Fin n) =>
              schrodingerFourierMultiplier n s ξ *
                FourierTransform.fourier φ ξ) x)
    {t : ℝ}
    (ht : 0 < t) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ψ t x =
          MeasureTheory.convolution
            (schrodingerKernel n t) φ
            (ContinuousLinearMap.mul ℂ ℂ) volume x ∧
      MeasureTheory.convolution
            (schrodingerKernel n t) φ
            (ContinuousLinearMap.mul ℂ ℂ) volume x =
          (∫ y : EuclideanSpace ℝ (Fin n),
            schrodingerKernel n t y * φ (x - y) ∂volume) ∧
      (∫ y : EuclideanSpace ℝ (Fin n),
          schrodingerKernel n t y * φ (x - y) ∂volume) =
        ∫ y : EuclideanSpace ℝ (Fin n),
          schrodingerKernel n t (x - y) * φ y ∂volume := by
  sorry
