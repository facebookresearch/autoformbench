/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open LieAlgebra

namespace Autoform_Lie_groups_lie_algebras_lie_levi_decomposition_splitting

universe u v

variable (k : Type u) (g : Type v)
variable [Field k]
variable [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]



abbrev radSubmodule : Submodule k g :=
  (LieAlgebra.radical k g).toSubmodule


abbrev ssQuotient : Type v :=
  g ⧸ (LieAlgebra.radical k g)







def radicalQuotientMap : g →ₗ⁅k⁆ ssQuotient k g where
  toFun := LieSubmodule.Quotient.mk' (LieAlgebra.radical k g)
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro a x
    simp
  map_lie' := by
    intro x y
    exact LieSubmodule.Quotient.mk_bracket (LieAlgebra.radical k g) x y





















end Autoform_Lie_groups_lie_algebras_lie_levi_decomposition_splitting

end