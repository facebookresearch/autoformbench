/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators LineDeriv Pointwise

namespace Autoform_Differential_Analysis_diff_analysis_lemma_11_5


abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)



def coordDirection {n : ℕ} (j : Fin n) : Rn n :=
  EuclideanSpace.single j (1 : ℝ)



def coordDeriv {n : ℕ} (j : Fin n) (u : TemperedDistribution (Rn n) ℂ) :
    TemperedDistribution (Rn n) ℂ :=
  LineDeriv.lineDerivOp (coordDirection j) u




def cauchyKernel2D (x : Rn 2) : ℂ :=
  if x = 0 then 0 else
    (((2 * Real.pi : ℂ) * ((x 0 : ℂ) + Complex.I * (x 1 : ℂ)))⁻¹)


def dbarOp (u : TemperedDistribution (Rn 2) ℂ) :
    TemperedDistribution (Rn 2) ℂ :=
  coordDeriv (0 : Fin 2) u + Complex.I • coordDeriv (1 : Fin 2) u



def IsCauchyKernelDistribution (E : TemperedDistribution (Rn 2) ℂ) : Prop :=
  ∀ φ : SchwartzMap (Rn 2) ℂ,
    E φ = ∫ x, cauchyKernel2D x * φ x


def IsDBarFundamentalSolution (E : TemperedDistribution (Rn 2) ℂ) : Prop :=
  dbarOp E = TemperedDistribution.delta (0 : Rn 2)



end Autoform_Differential_Analysis_diff_analysis_lemma_11_5

end
