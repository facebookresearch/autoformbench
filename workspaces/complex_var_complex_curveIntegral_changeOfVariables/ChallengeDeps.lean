import Mathlib

noncomputable section

open scoped unitInterval

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_complex_curveIntegral_changeOfVariables


abbrev complexLineForm (f : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun w => (ContinuousLinearMap.lsmul ℂ ℂ) (f w)



end Autoform_Functions_of_a_Complex_Variable_complex_var_complex_curveIntegral_changeOfVariables

end
