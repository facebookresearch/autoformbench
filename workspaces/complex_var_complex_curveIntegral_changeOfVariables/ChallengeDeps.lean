/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped unitInterval

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_complex_curveIntegral_changeOfVariables


abbrev complexLineForm (f : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun w => (ContinuousLinearMap.lsmul ℂ ℂ) (f w)



end Autoform_Functions_of_a_Complex_Variable_complex_var_complex_curveIntegral_changeOfVariables

end
