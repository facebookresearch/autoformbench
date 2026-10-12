/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped Quaternion

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_6_7_abstract


abbrev UnitQuaternion : Type :=
  ↥(unitary ℍ)


abbrev SU2 : Type :=
  ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)



end Autoform_Lie_groups_lie_algebras_lie_proposition_6_7_abstract
