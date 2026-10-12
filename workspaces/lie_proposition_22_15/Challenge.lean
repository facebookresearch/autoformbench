/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps





import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.GroupAction.Basic

open Autoform_Lie_groups_lie_algebras_lie_proposition_22_15
noncomputable section

open Set

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_22_15

variable {ι M N : Type*}
variable [Finite ι]
variable [NormedAddCommGroup M] [InnerProductSpace ℝ M] [FiniteDimensional ℝ M]
variable [AddCommGroup N] [Module ℝ N]





omit [Finite ι] [FiniteDimensional ℝ M] in







theorem mapChamber_is_connected
    (P : RootPairing ι ℝ M N)
    (w : P.weylGroup)
    (C : WeylChamber P) :
    IsConnected ((fun x : M => w • x) '' C.carrier) := by
  sorry

omit [Finite ι] [FiniteDimensional ℝ M] in






theorem mapChamber_subset_regular
    (P : RootPairing ι ℝ M N)
    (w : P.weylGroup)
    (C : WeylChamber P) :
    (fun x : M => w • x) '' C.carrier ⊆ regularSet P := by
  sorry

omit [Finite ι] [FiniteDimensional ℝ M] in







theorem mapChamber_maximal_connected
    (P : RootPairing ι ℝ M N)
    (w : P.weylGroup)
    (C : WeylChamber P) :
    ∀ C' : Set M,
      IsConnected C' →
      C' ⊆ regularSet P →
      (fun x : M => w • x) '' C.carrier ⊆ C' →
      C' = (fun x : M => w • x) '' C.carrier := by
  sorry















def mapChamber
    (P : RootPairing ι ℝ M N)
    (w : P.weylGroup)
    (C : WeylChamber P) : WeylChamber P where
  carrier := (fun x : M => w • x) '' C.carrier
  is_connected := mapChamber_is_connected P w C
  subset_regular := mapChamber_subset_regular P w C
  maximal_connected := mapChamber_maximal_connected P w C

omit [Finite ι] [FiniteDimensional ℝ M] in






theorem instMulActionWeylGroupWeylChamber_one_smul
    (P : RootPairing ι ℝ M N)
    (C : WeylChamber P) :
    mapChamber P 1 C = C := by
  sorry

omit [Finite ι] [FiniteDimensional ℝ M] in






theorem instMulActionWeylGroupWeylChamber_mul_smul
    (P : RootPairing ι ℝ M N)
    (w₁ w₂ : P.weylGroup)
    (C : WeylChamber P) :
    mapChamber P (w₁ * w₂) C = mapChamber P w₁ (mapChamber P w₂ C) := by
  sorry









noncomputable instance instMulActionWeylGroupWeylChamber
    (P : RootPairing ι ℝ M N) :
    MulAction P.weylGroup (WeylChamber P) where
  smul w C := mapChamber P w C
  one_smul C := instMulActionWeylGroupWeylChamber_one_smul P C
  mul_smul w₁ w₂ C := instMulActionWeylGroupWeylChamber_mul_smul P w₁ w₂ C









theorem proposition_22_15
    (P : RootPairing ι ℝ M N)
    [RootPairing.IsRootSystem P]
    [P.IsCrystallographic] :
    Nonempty (WeylChamber P) ∧
      ∀ C D : WeylChamber P, ∃! w : P.weylGroup, w • C = D := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_proposition_22_15

end