/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

universe u v

open UniversalEnvelopingAlgebra

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_12_4

variable (K : Type u) (L : Type v)
variable [Field K] [LieRing L] [LieAlgebra K L]


abbrev UEA : Type (max u v) :=
  UniversalEnvelopingAlgebra K L

abbrev ι : L → UEA K L :=
  fun x => (UniversalEnvelopingAlgebra.ι K) x










def adInvariantSubalgebra : Subalgebra K (UEA K L) :=
  Subalgebra.centralizer K (Set.range (ι K L))



end Autoform_Lie_groups_lie_algebras_lie_proposition_12_4
