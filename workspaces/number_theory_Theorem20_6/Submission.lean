import ChallengeDeps
import Submission.Helpers

open Autoform_Number_Theory_I_number_theory_Theorem20_6
open scoped Cyclotomic NumberField

namespace Submission

theorem Theorem20_6 (p exponent : ℕ)
    [Fact p.Prime]
    (K : Type*) [Field K]
    [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K]
    [IsGalois ℚ_[p] K]
    [IsCyclic (K ≃ₐ[ℚ_[p]] K)]
    (hdeg : Module.finrank ℚ_[p] K = p ^ exponent)
    (hodd : Odd (Module.finrank ℚ_[p] K)) :
    ContainedInCyclotomicField ℚ_[p] K := by
  sorry

end Submission
