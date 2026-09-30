import Mathlib

noncomputable section

open scoped Cyclotomic NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem20_6







def ContainedInCyclotomicField
    (F : Type*) (K : Type*) [Field F] [CharZero F] [Field K] [Algebra F K] : Prop :=
  ∃ (m : ℕ),
    Nonempty (K →ₐ[F] CyclotomicField m F)



end Autoform_Number_Theory_I_number_theory_Theorem20_6
