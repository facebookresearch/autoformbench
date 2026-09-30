import Mathlib

noncomputable section

namespace Autoform_Number_Theory_I_number_theory_Theorem19_12


def classNumberStrip (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s : ℂ | 1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ) < s.re}














def analyticClassNumberFormulaResidue
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  ((2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces K *
      ((2 : ℝ) * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (NumberField.classNumber K : ℝ) *
          NumberField.Units.regulator K) /
    ((NumberField.Units.torsionOrder K : ℝ) *
      Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|)



end Autoform_Number_Theory_I_number_theory_Theorem19_12
