/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Introduction_to_PDEs_pde_proposition_1_0_1

theorem proposition_1_0_1 (u : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ)
    (f g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h_u_C2 :
      ContDiffOn ℝ 2
        (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => u p.1 p.2)
        (Set.Ici (0 : ℝ) ×ˢ
          (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))))
    (h_wave :
      ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), 0 ≤ t →
        -(iteratedDerivWithin 2 (fun s : ℝ => u s x)
            (Set.Ici (0 : ℝ)) t) +
          Laplacian.laplacian (u t) x = 0)
    (h_initial_position :
      ∀ x : EuclideanSpace ℝ (Fin 3), u 0 x = f x)
    (h_initial_velocity :
      ∀ x : EuclideanSpace ℝ (Fin 3),
        derivWithin (fun t : ℝ => u t x) (Set.Ici (0 : ℝ)) 0 = g x) :
    ∀ x : EuclideanSpace ℝ (Fin 3),
      ContDiffOn ℝ 2
        (fun p : ℝ × ℝ =>
          modifiedSphericalAverage (u p.1) p.2 x)
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∧
      (∀ (t r : ℝ), 0 ≤ t → 0 ≤ r →
        -(iteratedDerivWithin 2
            (fun τ : ℝ => modifiedSphericalAverage (u τ) r x)
            (Set.Ici (0 : ℝ)) t) +
          iteratedDerivWithin 2
            (fun ρ : ℝ => modifiedSphericalAverage (u t) ρ x)
            (Set.Ici (0 : ℝ)) r = 0) ∧
      (∀ t : ℝ, 0 ≤ t →
        modifiedSphericalAverage (u t) 0 x = 0) ∧
      (∀ r : ℝ, 0 < r →
        modifiedSphericalAverage (u 0) r x =
          modifiedSphericalAverage f r x) ∧
      (∀ r : ℝ, 0 < r →
        derivWithin
            (fun t : ℝ => modifiedSphericalAverage (u t) r x)
            (Set.Ici (0 : ℝ)) 0 =
          modifiedSphericalAverage g r x) ∧
      (∀ t : ℝ, 0 ≤ t →
        Filter.Tendsto
          (fun r : ℝ => sphericalAverage (u t) r x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (u t x))) := by
  exact Submission.proposition_1_0_1 u f g h_u_C2 h_wave h_initial_position h_initial_velocity
