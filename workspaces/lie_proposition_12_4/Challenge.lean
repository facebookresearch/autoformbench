/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_proposition_12_4
open UniversalEnvelopingAlgebra

universe u v

variable (K : Type u) (L : Type v)
variable [Field K] [LieRing L] [LieAlgebra K L]

theorem proposition_12_4 :
    Subalgebra.center K (UEA K L) = adInvariantSubalgebra K L := by
  sorry
