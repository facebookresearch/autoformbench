/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.RCLike.Basic
import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_theorem_21_10
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



theorem productPairingAux_map_add
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (x : M₁ × M₂) (y z : N₁ × N₂) :
    (P.toLinearMap x.1) (y + z).1 + (Q.toLinearMap x.2) (y + z).2 =
      ((P.toLinearMap x.1) y.1 + (Q.toLinearMap x.2) y.2) +
        ((P.toLinearMap x.1) z.1 + (Q.toLinearMap x.2) z.2) := by
  sorry



theorem productPairingAux_map_smul
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (x : M₁ × M₂) (m : K) (y : N₁ × N₂) :
    (P.toLinearMap x.1) (m • y).1 + (Q.toLinearMap x.2) (m • y).2 =
      (RingHom.id K) m • ((P.toLinearMap x.1) y.1 + (Q.toLinearMap x.2) y.2) := by
  sorry




noncomputable def productPairingAux
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (x : M₁ × M₂) :
    (N₁ × N₂) →ₗ[K] K where
  toFun y := (P.toLinearMap x.1) y.1 + (Q.toLinearMap x.2) y.2
  map_add' := productPairingAux_map_add P Q x
  map_smul' := productPairingAux_map_smul P Q x



theorem productPairing_map_add
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (x y : M₁ × M₂) :
    productPairingAux P Q (x + y) = productPairingAux P Q x + productPairingAux P Q y := by
  sorry



theorem productPairing_map_smul
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (m : K) (x : M₁ × M₂) :
    productPairingAux P Q (m • x) = (RingHom.id K) m • productPairingAux P Q x := by
  sorry







noncomputable def productPairing
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    (M₁ × M₂) →ₗ[K] (N₁ × N₂ →ₗ[K] K) where
  toFun x := productPairingAux P Q x
  map_add' := productPairing_map_add P Q
  map_smul' := productPairing_map_smul P Q


def productRootFun
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    (ι₁ ⊕ ι₂) → (M₁ × M₂)
  | Sum.inl i => (P.root i, 0)
  | Sum.inr j => (0, Q.root j)

theorem productRootFun_injective
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    Function.Injective (productRootFun P Q) := by
  sorry







def productRoot
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    (ι₁ ⊕ ι₂) ↪ (M₁ × M₂) where
  toFun := productRootFun P Q
  inj' := productRootFun_injective P Q


def productCorootFun
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    (ι₁ ⊕ ι₂) → (N₁ × N₂)
  | Sum.inl i => (P.coroot i, 0)
  | Sum.inr j => (0, Q.coroot j)

theorem productCorootFun_injective
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    Function.Injective (productCorootFun P Q) := by
  sorry







def productCoroot
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    (ι₁ ⊕ ι₂) ↪ (N₁ × N₂) where
  toFun := productCorootFun P Q
  inj' := productCorootFun_injective P Q





def productReflectionPerm
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    (ι₁ ⊕ ι₂) → ((ι₁ ⊕ ι₂) ≃ (ι₁ ⊕ ι₂))
  | Sum.inl i =>
      { toFun := fun x =>
          match x with
          | Sum.inl i' => Sum.inl ((P.reflectionPerm i) i')
          | Sum.inr j' => Sum.inr j'
        invFun := fun x =>
          match x with
          | Sum.inl i' => Sum.inl ((P.reflectionPerm i).symm i')
          | Sum.inr j' => Sum.inr j'
        left_inv := by
          intro x
          cases x <;> simp
        right_inv := by
          intro x
          cases x <;> simp }
  | Sum.inr j =>
      { toFun := fun x =>
          match x with
          | Sum.inl i' => Sum.inl i'
          | Sum.inr j' => Sum.inr ((Q.reflectionPerm j) j')
        invFun := fun x =>
          match x with
          | Sum.inl i' => Sum.inl i'
          | Sum.inr j' => Sum.inr ((Q.reflectionPerm j).symm j')
        left_inv := by
          intro x
          cases x <;> simp
        right_inv := by
          intro x
          cases x <;> simp }

theorem productRootPairing_map_add
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (x y : M₁ × M₂) :
    (productPairing P Q) (x + y) = (productPairing P Q) x + (productPairing P Q) y := by
  sorry


theorem productRootPairing_map_smul
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (m : K) (x : M₁ × M₂) :
    (productPairing P Q) (m • x) = (RingHom.id K) m • (productPairing P Q) x := by
  sorry


theorem productRootPairing_isPerfPair
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    (productPairing P Q).IsPerfPair := by
  sorry


theorem productRootPairing_root_coroot_two
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (i : ι₁ ⊕ ι₂) :
    (productPairing P Q) ((productRoot P Q) i) ((productCoroot P Q) i) = 2 := by
  sorry


theorem productRootPairing_reflectionPerm_root
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (i j : ι₁ ⊕ ι₂) :
    (productRoot P Q) j -
        (productPairing P Q) ((productRoot P Q) j) ((productCoroot P Q) i) •
          (productRoot P Q) i =
      (productRoot P Q) ((productReflectionPerm P Q i) j) := by
  sorry


theorem productRootPairing_reflectionPerm_coroot
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    (i j : ι₁ ⊕ ι₂) :
    (productCoroot P Q) j -
        (productPairing P Q) ((productRoot P Q) i) ((productCoroot P Q) j) •
          (productCoroot P Q) i =
      (productCoroot P Q) ((productReflectionPerm P Q i) j) := by
  sorry





noncomputable def productRootPairing
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂) :
    RootPairing (ι₁ ⊕ ι₂) K (M₁ × M₂) (N₁ × N₂) where
  toFun := productPairing P Q
  map_add' := productRootPairing_map_add P Q
  map_smul' := productRootPairing_map_smul P Q
  isPerfPair_toLinearMap := productRootPairing_isPerfPair P Q
  root := productRoot P Q
  coroot := productCoroot P Q
  root_coroot_two := productRootPairing_root_coroot_two P Q
  reflectionPerm := productReflectionPerm P Q
  reflectionPerm_root := productRootPairing_reflectionPerm_root P Q
  reflectionPerm_coroot := productRootPairing_reflectionPerm_coroot P Q
instance instIsRootSystemProduct
    [NeZero (2 : K)]
    (P : RootPairing ι₁ K M₁ N₁)
    (Q : RootPairing ι₂ K M₂ N₂)
    [P.IsRootSystem] [Q.IsRootSystem] :
    (productRootPairing P Q).IsRootSystem := by
  sorry

end Product










attribute [instance] RootSystem.addM RootSystem.moduleM
attribute [instance] RootSystem.addN RootSystem.moduleN
attribute [instance] RootSystem.finiteIndex RootSystem.finiteDimM
attribute [instance] RootSystem.isRootSystem

namespace RootSystem

variable {K : Type*} [Field K] [CharZero K]



















def IsAssociatedToLieAlgebra
    {L : Type*} [CharZero K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    (R : RootSystem K) : Prop :=
  ∃ (H : LieSubalgebra K L)
    (hKilling : LieAlgebra.IsKilling K L)
    (hCartan : H.IsCartanSubalgebra)
    (hSplit : LieModule.IsTriangularizable K (↥H) L),
      R.Isomorphic (ofLiePair H hKilling hCartan hSplit)



end RootSystem





attribute [scoped instance 100] LieRing.ofAssociativeRing

namespace RootSystem

variable {K : Type*} [Field K] [CharZero K]


noncomputable def product (R S : RootSystem K) : RootSystem K where
  ι := R.ι ⊕ S.ι
  M := R.M × S.M
  N := R.N × S.N
  addM := inferInstance
  moduleM := inferInstance
  addN := inferInstance
  moduleN := inferInstance
  finiteIndex := inferInstance
  finiteDimM := inferInstance
  pairing := productRootPairing R.pairing S.pairing
  isRootSystem := inferInstance





end RootSystem





universe uK uι uM uN















theorem theorem_21_10
    {K : Type uK} [Field K] [CharZero K]
    (R : RootSystem.{uK, uι, uM, uN} K)
    (h_crystallographic : R.pairing.IsCrystallographic)
    (h_reduced : R.IsReduced)
    (h_rank : R.rank = 2) :
    (∃ R₁ R₂ : RootSystem.{uK, uι, uM, uN} K,
        R₁.IsTypeA 1 ∧
        R₂.IsTypeA 1 ∧
        R.Isomorphic (R₁.product R₂)) ∨
    (∃ RA₂ : RootSystem.{uK, uι, uM, uN} K,
        RA₂.IsTypeA 2 ∧
        R.Isomorphic RA₂) ∨
    (∃ RB₂ : RootSystem.{uK, uι, uM, uN} K,
        RB₂.IsTypeB 2 ∧
        R.Isomorphic RB₂) ∨
    R.pairing.IsG2 := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_theorem_21_10
