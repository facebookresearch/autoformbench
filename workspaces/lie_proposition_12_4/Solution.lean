import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_proposition_12_4
open UniversalEnvelopingAlgebra

universe u v

variable (K : Type u) (L : Type v)
variable [Field K] [LieRing L] [LieAlgebra K L]

theorem proposition_12_4 :
    Subalgebra.center K (UEA K L) = adInvariantSubalgebra K L := by
  apply Submission.proposition_12_4 <;> assumption
