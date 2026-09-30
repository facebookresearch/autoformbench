



import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Lie_groups_lie_algebras_lie_levi_decomposition_splitting
noncomputable section

open LieAlgebra

namespace Autoform_Lie_groups_lie_algebras_lie_levi_decomposition_splitting

universe u v

variable (k : Type u) (g : Type v)
variable [Field k]
variable [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]












theorem radicalDerivation_mem (s : LieSubalgebra k g) (x : s)
    (y : LieAlgebra.radical k g) :
    ⁅(x : g), (y : g)⁆ ∈ LieAlgebra.radical k g := by
  sorry




theorem radicalDerivation_map_add (s : LieSubalgebra k g) (x : s)
    (y z : LieAlgebra.radical k g) :
    ⁅(x : g), ((y + z : LieAlgebra.radical k g) : g)⁆ =
      ⁅(x : g), (y : g)⁆ + ⁅(x : g), (z : g)⁆ := by
  sorry




theorem radicalDerivation_map_smul (s : LieSubalgebra k g) (x : s) (a : k)
    (y : LieAlgebra.radical k g) :
    ⁅(x : g), ((a • y : LieAlgebra.radical k g) : g)⁆ =
      (RingHom.id k) a • ⁅(x : g), (y : g)⁆ := by
  sorry




theorem radicalDerivation_leibniz (s : LieSubalgebra k g) (x : s)
    (y z : LieAlgebra.radical k g) :
    ⁅(x : g), ((⁅y, z⁆ : LieAlgebra.radical k g) : g)⁆ =
      ⁅(y : g), ⁅(x : g), (z : g)⁆⁆ - ⁅(z : g), ⁅(x : g), (y : g)⁆⁆ := by
  sorry









def radicalDerivationOfSubalgebraElement
    (s : LieSubalgebra k g) (x : s) :
    LieDerivation k (LieAlgebra.radical k g) (LieAlgebra.radical k g) where
  toFun := fun y =>
    ⟨⁅(x : g), (y : g)⁆, radicalDerivation_mem k g s x y⟩
  map_add' := by
    intro y z
    exact Subtype.ext (radicalDerivation_map_add k g s x y z)
  map_smul' := by
    intro a y
    exact Subtype.ext (radicalDerivation_map_smul k g s x a y)
  leibniz' := by
    intro y z
    exact Subtype.ext (radicalDerivation_leibniz k g s x y z)



theorem leviAction_map_add (s : LieSubalgebra k g) (x y : s) :
    radicalDerivationOfSubalgebraElement k g s (x + y) =
      radicalDerivationOfSubalgebraElement k g s x +
        radicalDerivationOfSubalgebraElement k g s y := by
  sorry




theorem leviAction_map_smul (s : LieSubalgebra k g) (a : k) (x : s) :
    radicalDerivationOfSubalgebraElement k g s (a • x) =
      (RingHom.id k) a • radicalDerivationOfSubalgebraElement k g s x := by
  sorry




theorem leviAction_map_lie (s : LieSubalgebra k g) (x y : s) :
    radicalDerivationOfSubalgebraElement k g s ⁅x, y⁆ =
      ⁅radicalDerivationOfSubalgebraElement k g s x,
        radicalDerivationOfSubalgebraElement k g s y⁆ := by
  sorry











def leviAction (s : LieSubalgebra k g) :
    s →ₗ⁅k⁆ LieDerivation k (LieAlgebra.radical k g) (LieAlgebra.radical k g) where
  toFun := radicalDerivationOfSubalgebraElement k g s
  map_add' := by
    intro x y
    exact leviAction_map_add k g s x y
  map_smul' := by
    intro a x
    exact leviAction_map_smul k g s a x
  map_lie' := by
    intro x y
    exact leviAction_map_lie k g s x y











theorem levi_decomposition_semidirect (hchar : CharZero k) :
    LieAlgebra.HasTrivialRadical k (ssQuotient k g) ∧
      ∃ (s : LieSubalgebra k g)
        (e : g ≃ₗ⁅k⁆ ((LieAlgebra.radical k g) ⋊⁅leviAction k g s⁆ s)),
        Nonempty (s ≃ₗ⁅k⁆ ssQuotient k g) ∧
        IsCompl (radSubmodule k g) s.toSubmodule := by
  sorry











theorem levi_decomposition_splitting (hchar : CharZero k) :
    LieAlgebra.HasTrivialRadical k (ssQuotient k g) ∧
      ∃ q : ssQuotient k g →ₗ⁅k⁆ g,
        (radicalQuotientMap k g).comp q =
          LieHom.id := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_levi_decomposition_splitting


end
end Submission