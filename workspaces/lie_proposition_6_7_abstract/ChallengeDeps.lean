import Mathlib

noncomputable section

open scoped Quaternion

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_6_7_abstract


abbrev UnitQuaternion : Type :=
  ↥(unitary ℍ)


abbrev SU2 : Type :=
  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)



end Autoform_Lie_groups_lie_algebras_lie_proposition_6_7_abstract
