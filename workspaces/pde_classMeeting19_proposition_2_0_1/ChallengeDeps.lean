/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Autoform_Introduction_to_PDEs_pde_classMeeting19_proposition_2_0_1





def schrodingerFourierMultiplier (n : ℕ) (t : ℝ)
    (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp
    (-(2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.I * (t : ℂ) *
      ((‖ξ‖ ^ 2 : ℝ) : ℂ))









def schrodingerKernel (n : ℕ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (Complex.cpow
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      ((n : ℂ) / 2))⁻¹ *
    Complex.exp
      (Complex.I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ))



end Autoform_Introduction_to_PDEs_pde_classMeeting19_proposition_2_0_1

end
