import Mathlib

namespace Autoform_Lie_groups_lie_algebras_lie_cartanCriterionSolvability

variable (K L : Type*)
variable [Field K] [CharZero K]
variable [LieRing L] [LieAlgebra K L]
variable [FiniteDimensional K L]







abbrev commutant : LieIdeal K L :=
  LieAlgebra.derivedSeries K L 1







noncomputable abbrev killingKernel : LieIdeal K L :=
  LieIdeal.killingCompl K L ⊤



end Autoform_Lie_groups_lie_algebras_lie_cartanCriterionSolvability
