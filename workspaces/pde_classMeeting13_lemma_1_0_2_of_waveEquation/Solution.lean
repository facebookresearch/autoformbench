/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Submission
import ChallengeDeps
noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_PDEs_pde_classMeeting13_lemma_1_0_2_of_waveEquation



















theorem classMeeting13_lemma_1_0_2
    {n : ℕ}
    (φ : (Fin (n + 1) → ℝ) → ℝ)
    (hφ : ContDiff ℝ 2 φ)
    (ν : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    (∑ μ : Fin (n + 1),
      coordDeriv μ (fun y => energyMomentumUp φ y μ ν) x) =
      waveOperator φ x *
        (∑ α : Fin (n + 1),
          minkowskiMetric n ν α * coordDeriv α φ x) := Submission.Autoform_Introduction_to_PDEs_pde_classMeeting13_lemma_1_0_2_of_waveEquation.classMeeting13_lemma_1_0_2 φ hφ ν x





theorem classMeeting13_lemma_1_0_2_of_waveEquation
    {n : ℕ}
    (φ : (Fin (n + 1) → ℝ) → ℝ)
    (hφ : ContDiff ℝ 2 φ)
    (hWave : ∀ x, waveOperator φ x = 0)
    (ν : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    (∑ μ : Fin (n + 1),
      coordDeriv μ (fun y => energyMomentumUp φ y μ ν) x) = 0 := Submission.Autoform_Introduction_to_PDEs_pde_classMeeting13_lemma_1_0_2_of_waveEquation.classMeeting13_lemma_1_0_2_of_waveEquation φ hφ hWave ν x

end Autoform_Introduction_to_PDEs_pde_classMeeting13_lemma_1_0_2_of_waveEquation

end
