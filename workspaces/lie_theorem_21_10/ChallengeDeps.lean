/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped BigOperators
open RootPairing

universe u

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_21_10









section Product

variable {K : Type*} [Field K]
variable {ι₁ ι₂ M₁ M₂ N₁ N₂ : Type*}
variable [AddCommGroup M₁] [Module K M₁]
variable [AddCommGroup M₂] [Module K M₂]
variable [AddCommGroup N₁] [Module K N₁]
variable [AddCommGroup N₂] [Module K N₂]



































end Product








structure RootSystem (K : Type*) [Field K] where
  ι : Type*
  M : Type*
  N : Type*
  [addM : AddCommGroup M]
  [moduleM : Module K M]
  [addN : AddCommGroup N]
  [moduleN : Module K N]
  [finiteIndex : Finite ι]
  [finiteDimM : FiniteDimensional K M]
  pairing : RootPairing ι K M N
  [isRootSystem : pairing.IsRootSystem]

attribute [instance] RootSystem.addM RootSystem.moduleM
attribute [instance] RootSystem.addN RootSystem.moduleN
attribute [instance] RootSystem.finiteIndex RootSystem.finiteDimM
attribute [instance] RootSystem.isRootSystem

namespace RootSystem

variable {K : Type*} [Field K] [CharZero K]


noncomputable def rank (R : RootSystem K) : ℕ :=
  Module.finrank K R.M


def IsReduced (R : RootSystem K) : Prop :=
  R.pairing.IsReduced





def Isomorphic (R S : RootSystem K) : Prop :=
  ∃ (e : R.ι ≃ S.ι)
    (f : R.M ≃ₗ[K] S.M)
    (g : R.N ≃ₗ[K] S.N),
      RootPairing.map (P := R.pairing) e f g = S.pairing


noncomputable def ofPairing
    {ι M N : Type*}
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    [Finite ι] [FiniteDimensional K M]
    (P : RootPairing ι K M N) [P.IsRootSystem] :
    RootSystem K where
  ι := ι
  M := M
  N := N
  addM := inferInstance
  moduleM := inferInstance
  addN := inferInstance
  moduleN := inferInstance
  finiteIndex := inferInstance
  finiteDimM := inferInstance
  pairing := P
  isRootSystem := inferInstance







theorem finiteDimensional_of_lieSubalgebra
    {L₀ : Type u} [LieRing L₀] [LieAlgebra K L₀] [FiniteDimensional K L₀]
    (G : LieSubalgebra K L₀) :
    FiniteDimensional K (↥G) := by
  exact FiniteDimensional.of_injective G.subtype (by
    intro x y hxy
    exact Subtype.ext hxy)





noncomputable def ofLiePair
    {L : Type*} [CharZero K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    (H : LieSubalgebra K L)
    (hKilling : LieAlgebra.IsKilling K L)
    (hCartan : H.IsCartanSubalgebra)
    (hSplit : LieModule.IsTriangularizable K (↥H) L) :
    RootSystem K := by
  exact ofPairing (LieAlgebra.IsKilling.rootSystem H)











def IsAssociatedToLieSubalgebra
    {L₀ : Type u} [LieRing L₀] [LieAlgebra K L₀] [FiniteDimensional K L₀]
    (R : RootSystem K) (G : LieSubalgebra K L₀) : Prop :=
  letI : LieRing (↥G) :=
    LieSubalgebra.lieRing K L₀ G
  letI : LieAlgebra K (↥G) :=
    LieSubalgebra.lieAlgebra K L₀ G
  letI : FiniteDimensional K (↥G) :=
    finiteDimensional_of_lieSubalgebra G
  ∃ (H : LieSubalgebra K (↥G))
    (hKilling : LieAlgebra.IsKilling K (↥G))
    (hCartan : H.IsCartanSubalgebra)
    (hSplit : LieModule.IsTriangularizable K (↥H) (↥G)),
      R.Isomorphic (ofLiePair H hKilling hCartan hSplit)

end RootSystem





attribute [scoped instance 100] LieRing.ofAssociativeRing

namespace RootSystem

variable {K : Type*} [Field K] [CharZero K]





def IsTypeA (R : RootSystem K) (n : ℕ) : Prop :=
  RootSystem.IsAssociatedToLieSubalgebra (K := K) R
    (LieAlgebra.SpecialLinear.sl (Fin (n + 1)) K)





def IsTypeB (R : RootSystem K) (n : ℕ) : Prop :=
  RootSystem.IsAssociatedToLieSubalgebra (K := K) R
    (LieAlgebra.Orthogonal.typeB (Fin n) K)

end RootSystem







end Autoform_Lie_groups_lie_algebras_lie_theorem_21_10
