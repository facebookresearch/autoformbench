import ChallengeDeps
import Submission

open Autoform_Lie_groups_lie_algebras_lie_theorem_18_9

universe u v w

theorem theorem_18_9 (k : Type u) (L : Type v) (V : Type w)
    [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L]
    [LieAlgebra.HasTrivialRadical k L]
    [AddCommGroup V] [Module k V]
    [LieRingModule L V] [LieModule k L V]
    [FiniteDimensional k V] :
    CompletelyReducibleLieModule k L V := by
  exact Submission.theorem_18_9 k L V
