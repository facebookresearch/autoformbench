import Mathlib

noncomputable section

open scoped Cyclotomic NumberField

namespace Autoform_Number_Theory_I_number_theory_Proposition20_3







def ContainedInCyclotomicField
    (F : Type*) (K : Type*) [Field F] [CharZero F] [Field K] [Algebra F K] : Prop :=
  ∃ (m : ℕ),
    Nonempty (K →ₐ[F] CyclotomicField m F)







def LocalKroneckerWeberStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [IsAbelianGalois ℚ_[p] K],
      ContainedInCyclotomicField ℚ_[p] K







def GlobalKroneckerWeberStatement : Prop :=
  ∀ (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K],
      ContainedInCyclotomicField ℚ K



end Autoform_Number_Theory_I_number_theory_Proposition20_3
