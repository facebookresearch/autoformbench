/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Introduction_to_PDEs_pde_classMeeting4_corollary_1_0_1

theorem classMeeting4_corollary_1_0_1 {T D : ℝ} {Ω : Set ℝ}
    {v w f g : ℝ × ℝ → ℝ}
    (hT : 0 < T)
    (hD : 0 < D)
    (hΩ_open : IsOpen Ω)
    (hΩ_connected : IsConnected Ω)
    (hΩ_bounded : Bornology.IsBounded Ω)
    (hv : IsHeatSolutionOn T D Ω v f)
    (hw : IsHeatSolutionOn T D Ω w g)
    (hf_cont : ContinuousOn f (closure (spacetimeCylinder T Ω)))
    (hg_cont : ContinuousOn g (closure (spacetimeCylinder T Ω))) :
    (((∀ p ∈ parabolicBoundary T Ω, w p ≤ v p) ∧
        (∀ p ∈ spacetimeCylinder T Ω, g p ≤ f p)) →
      (∀ p ∈ closure (spacetimeCylinder T Ω), w p ≤ v p)) ∧
    sSup
        (Set.image (fun p : ℝ × ℝ => |v p - w p|)
          (closure (spacetimeCylinder T Ω))) ≤
      sSup
          (Set.image (fun p : ℝ × ℝ => |v p - w p|)
            (parabolicBoundary T Ω)) +
        T * sSup
          (Set.image (fun p : ℝ × ℝ => |f p - g p|)
            (closure (spacetimeCylinder T Ω))) := by
  sorry
