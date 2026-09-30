import ChallengeDeps
import Submission.Helpers

open Autoform_Number_Theory_I_number_theory_Theorem21_15
open scoped BigOperators NumberField Topology
open Filter

namespace Submission

theorem Theorem21_15 {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra (𝓞 K) (𝓞 L)]
    [IsNaturalRingOfIntegersAlgebra K L]
    [IsGalois K L] :
    HasPolarDensity K (SplitsCompletelySet K L)
      ((1 : ℚ) / (Module.finrank K L : ℚ)) := by
  sorry

end Submission
