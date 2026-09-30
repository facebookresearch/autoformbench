import Mathlib




























noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Autoform_Theory_of_Probability_probability_kolmogorov_three_series

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


def truncation (A : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => if |X n ω| ≤ A then X n ω else 0



end Autoform_Theory_of_Probability_probability_kolmogorov_three_series
