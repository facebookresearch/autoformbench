import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_cartanCriterionSolvability

variable (K L : Type*)
variable [Field K] [CharZero K]
variable [LieRing L] [LieAlgebra K L]
variable [FiniteDimensional K L]

theorem cartanCriterionSolvability :
    LieAlgebra.IsSolvable L ↔
      commutant K L ≤ killingKernel K L := by
  apply Submission.cartanCriterionSolvability <;> assumption
