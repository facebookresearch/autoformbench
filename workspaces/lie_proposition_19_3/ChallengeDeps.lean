import Mathlib

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_19_3

variable {K L : Type*}
variable [Field K] [CharZero K]
variable [LieRing L] [LieAlgebra K L]
variable [FiniteDimensional K L]


def IsLieSemisimpleElement (x : L) : Prop :=
  Module.End.IsSemisimple ((LieAlgebra.ad K L) x)


def IsLieNilpotentElement (x : L) : Prop :=
  IsNilpotent ((LieAlgebra.ad K L) x)






def IsAddJordanChevalleyDecomposition (x xs xn : L) : Prop :=
  x = xs + xn ∧
    IsLieSemisimpleElement (K := K) (L := L) xs ∧
    IsLieNilpotentElement (K := K) (L := L) xn ∧
    ⁅xs, xn⁆ = 0



end Autoform_Lie_groups_lie_algebras_lie_proposition_19_3
