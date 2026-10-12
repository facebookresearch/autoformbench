/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Set

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_22_15

variable {ι M N : Type*}
variable [Finite ι]
variable [NormedAddCommGroup M] [InnerProductSpace ℝ M] [FiniteDimensional ℝ M]
variable [AddCommGroup N] [Module ℝ N]










def regularSet (P : RootPairing ι ℝ M N) : Set M :=
  {x : M | ∀ i : ι, (P.toLinearMap x) (P.coroot i) ≠ 0}









structure WeylChamber (P : RootPairing ι ℝ M N) where
  carrier : Set M
  is_connected : IsConnected carrier
  subset_regular : carrier ⊆ regularSet P
  maximal_connected :
    ∀ C : Set M,
      IsConnected C →
      C ⊆ regularSet P →
      carrier ⊆ C →
      C = carrier












end Autoform_Lie_groups_lie_algebras_lie_proposition_22_15

end