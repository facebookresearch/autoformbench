/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps






import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

open Autoform_Lie_groups_lie_algebras_lie_proposition_5_10_ii
open scoped TensorProduct

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_5_10_ii

universe u𝕜 uE uH uG uF uB

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

variable {E : Type uE}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)

variable {G : Type uG}
variable [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [IsManifold I (⊤ : WithTop ℕ∞) G]
variable [LieGroup I (⊤ : WithTop ℕ∞) G]




































section BundleInterface

variable {F : Type uF}
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {B : G → Type uB}
variable [TopologicalSpace (Bundle.TotalSpace F B)]
variable [(g : G) → TopologicalSpace (B g)]
variable [FiberBundle F B]
variable [(g : G) → AddCommGroup (B g)]
variable [(g : G) → Module 𝕜 (B g)]
variable [VectorBundle 𝕜 F B]
variable [ContMDiffVectorBundle (⊤ : WithTop ℕ∞) F B I]







variable {k m : ℕ}
variable (MT : IsMixedTensorBundle (𝕜 := 𝕜) (I := I) (B := B) (F := F) k m)


















theorem LeftInvariantTensorFields_zero_mem :
    IsLeftInvariant (I := I) (B := B) (F := F) MT 0 := by
  sorry






theorem LeftInvariantTensorFields_add_mem
    (T S : SmoothTensorField (I := I) (B := B) (F := F))
    (hT : IsLeftInvariant (I := I) (B := B) (F := F) MT T)
    (hS : IsLeftInvariant (I := I) (B := B) (F := F) MT S) :
    IsLeftInvariant (I := I) (B := B) (F := F) MT (T + S) := by
  sorry






theorem LeftInvariantTensorFields_smul_mem
    (c : 𝕜) (T : SmoothTensorField (I := I) (B := B) (F := F))
    (hT : IsLeftInvariant (I := I) (B := B) (F := F) MT T) :
    IsLeftInvariant (I := I) (B := B) (F := F) MT (c • T) := by
  sorry





noncomputable def LeftInvariantTensorFields :
    Submodule 𝕜 (SmoothTensorField (I := I) (B := B) (F := F)) :=
{ carrier := {T | IsLeftInvariant (I := I) (B := B) (F := F) MT T}
  zero_mem' := LeftInvariantTensorFields_zero_mem (I := I) (B := B) (F := F) MT
  add_mem' := fun {T S} hT hS =>
    LeftInvariantTensorFields_add_mem (I := I) (B := B) (F := F) MT T S hT hS
  smul_mem' := fun c {T} hT =>
    LeftInvariantTensorFields_smul_mem (I := I) (B := B) (F := F) MT c T hT }





theorem RightInvariantTensorFields_zero_mem :
    IsRightInvariant (I := I) (B := B) (F := F) MT 0 := by
  sorry






theorem RightInvariantTensorFields_add_mem
    (T S : SmoothTensorField (I := I) (B := B) (F := F))
    (hT : IsRightInvariant (I := I) (B := B) (F := F) MT T)
    (hS : IsRightInvariant (I := I) (B := B) (F := F) MT S) :
    IsRightInvariant (I := I) (B := B) (F := F) MT (T + S) := by
  sorry






theorem RightInvariantTensorFields_smul_mem
    (c : 𝕜) (T : SmoothTensorField (I := I) (B := B) (F := F))
    (hT : IsRightInvariant (I := I) (B := B) (F := F) MT T) :
    IsRightInvariant (I := I) (B := B) (F := F) MT (c • T) := by
  sorry





noncomputable def RightInvariantTensorFields :
    Submodule 𝕜 (SmoothTensorField (I := I) (B := B) (F := F)) :=
{ carrier := {T | IsRightInvariant (I := I) (B := B) (F := F) MT T}
  zero_mem' := RightInvariantTensorFields_zero_mem (I := I) (B := B) (F := F) MT
  add_mem' := fun {T S} hT hS =>
    RightInvariantTensorFields_add_mem (I := I) (B := B) (F := F) MT T S hT hS
  smul_mem' := fun c {T} hT =>
    RightInvariantTensorFields_smul_mem (I := I) (B := B) (F := F) MT c T hT }


theorem proposition_5_10_i
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    (∃! T : SmoothTensorField (I := I) (B := B) (F := F),
      IsLeftInvariant (I := I) (B := B) (F := F) MT T ∧
        valueAtOne (I := I) (B := B) (F := F) MT T = τ)
    ∧
    (∃! T : SmoothTensorField (I := I) (B := B) (F := F),
      IsRightInvariant (I := I) (B := B) (F := F) MT T ∧
        valueAtOne (I := I) (B := B) (F := F) MT T = τ) := by
  sorry





theorem leftInvariantFieldsEquivLieTensor_mem
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    leftInvariantExtension (I := I) (B := B) (F := F) MT τ ∈
      LeftInvariantTensorFields (I := I) (B := B) (F := F) MT := by
  sorry





theorem leftInvariantFieldsEquivLieTensor_map_add
    (T S : LeftInvariantTensorFields (I := I) (B := B) (F := F) MT) :
    valueAtOne (I := I) (B := B) (F := F) MT ((T + S : _) : SmoothTensorField (I := I) (B := B) (F := F)) =
      valueAtOne (I := I) (B := B) (F := F) MT (T : SmoothTensorField (I := I) (B := B) (F := F)) +
        valueAtOne (I := I) (B := B) (F := F) MT (S : SmoothTensorField (I := I) (B := B) (F := F)) := by
  sorry





theorem leftInvariantFieldsEquivLieTensor_map_smul
    (c : 𝕜) (T : LeftInvariantTensorFields (I := I) (B := B) (F := F) MT) :
    valueAtOne (I := I) (B := B) (F := F) MT ((c • T : _) : SmoothTensorField (I := I) (B := B) (F := F)) =
      c • valueAtOne (I := I) (B := B) (F := F) MT (T : SmoothTensorField (I := I) (B := B) (F := F)) := by
  sorry






theorem leftInvariantFieldsEquivLieTensor_left_inv
    (T : LeftInvariantTensorFields (I := I) (B := B) (F := F) MT) :
    leftInvariantExtension (I := I) (B := B) (F := F) MT
        (valueAtOne (I := I) (B := B) (F := F) MT
          (T : SmoothTensorField (I := I) (B := B) (F := F)))
      = (T : SmoothTensorField (I := I) (B := B) (F := F)) := by
  sorry





theorem leftInvariantFieldsEquivLieTensor_right_inv
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    valueAtOne (I := I) (B := B) (F := F) MT
        (leftInvariantExtension (I := I) (B := B) (F := F) MT τ) = τ := by
  sorry




noncomputable def leftInvariantFieldsEquivLieTensor :
    LeftInvariantTensorFields (I := I) (B := B) (F := F) MT
      ≃ₗ[𝕜] LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m :=
{ toFun := fun T => valueAtOne (I := I) (B := B) (F := F) MT T.1
  invFun := fun τ =>
    ⟨leftInvariantExtension (I := I) (B := B) (F := F) MT τ,
      leftInvariantFieldsEquivLieTensor_mem (I := I) (B := B) (F := F) MT τ⟩
  map_add' := fun T S =>
    leftInvariantFieldsEquivLieTensor_map_add (I := I) (B := B) (F := F) MT T S
  map_smul' := fun c T =>
    leftInvariantFieldsEquivLieTensor_map_smul (I := I) (B := B) (F := F) MT c T
  left_inv := fun T =>
    Subtype.ext
      (leftInvariantFieldsEquivLieTensor_left_inv (I := I) (B := B) (F := F) MT T)
  right_inv := fun τ =>
    leftInvariantFieldsEquivLieTensor_right_inv (I := I) (B := B) (F := F) MT τ }





theorem rightInvariantFieldsEquivLieTensor_mem
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    rightInvariantExtension (I := I) (B := B) (F := F) MT τ ∈
      RightInvariantTensorFields (I := I) (B := B) (F := F) MT := by
  sorry





theorem rightInvariantFieldsEquivLieTensor_map_add
    (T S : RightInvariantTensorFields (I := I) (B := B) (F := F) MT) :
    valueAtOne (I := I) (B := B) (F := F) MT ((T + S : _) : SmoothTensorField (I := I) (B := B) (F := F)) =
      valueAtOne (I := I) (B := B) (F := F) MT (T : SmoothTensorField (I := I) (B := B) (F := F)) +
        valueAtOne (I := I) (B := B) (F := F) MT (S : SmoothTensorField (I := I) (B := B) (F := F)) := by
  sorry





theorem rightInvariantFieldsEquivLieTensor_map_smul
    (c : 𝕜) (T : RightInvariantTensorFields (I := I) (B := B) (F := F) MT) :
    valueAtOne (I := I) (B := B) (F := F) MT ((c • T : _) : SmoothTensorField (I := I) (B := B) (F := F)) =
      c • valueAtOne (I := I) (B := B) (F := F) MT (T : SmoothTensorField (I := I) (B := B) (F := F)) := by
  sorry






theorem rightInvariantFieldsEquivLieTensor_left_inv
    (T : RightInvariantTensorFields (I := I) (B := B) (F := F) MT) :
    rightInvariantExtension (I := I) (B := B) (F := F) MT
        (valueAtOne (I := I) (B := B) (F := F) MT
          (T : SmoothTensorField (I := I) (B := B) (F := F)))
      = (T : SmoothTensorField (I := I) (B := B) (F := F)) := by
  sorry





theorem rightInvariantFieldsEquivLieTensor_right_inv
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    valueAtOne (I := I) (B := B) (F := F) MT
        (rightInvariantExtension (I := I) (B := B) (F := F) MT τ) = τ := by
  sorry




noncomputable def rightInvariantFieldsEquivLieTensor :
    RightInvariantTensorFields (I := I) (B := B) (F := F) MT
      ≃ₗ[𝕜] LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m :=
{ toFun := fun T => valueAtOne (I := I) (B := B) (F := F) MT T.1
  invFun := fun τ =>
    ⟨rightInvariantExtension (I := I) (B := B) (F := F) MT τ,
      rightInvariantFieldsEquivLieTensor_mem (I := I) (B := B) (F := F) MT τ⟩
  map_add' := fun T S =>
    rightInvariantFieldsEquivLieTensor_map_add (I := I) (B := B) (F := F) MT T S
  map_smul' := fun c T =>
    rightInvariantFieldsEquivLieTensor_map_smul (I := I) (B := B) (F := F) MT c T
  left_inv := fun T =>
    Subtype.ext
      (rightInvariantFieldsEquivLieTensor_left_inv (I := I) (B := B) (F := F) MT T)
  right_inv := fun τ =>
    rightInvariantFieldsEquivLieTensor_right_inv (I := I) (B := B) (F := F) MT τ }




theorem proposition_5_10_ii
    (τ : LieTensor (𝕜 := 𝕜) (I := I) (G := G) k m) :
    (IsRightInvariant (I := I) (B := B) (F := F) MT
        (leftInvariantExtension (I := I) (B := B) (F := F) MT τ)
      ↔ IsLeftInvariant (I := I) (B := B) (F := F) MT
        (rightInvariantExtension (I := I) (B := B) (F := F) MT τ))
    ∧
    (IsRightInvariant (I := I) (B := B) (F := F) MT
        (leftInvariantExtension (I := I) (B := B) (F := F) MT τ)
      ↔ IsAdInvariant (𝕜 := 𝕜) (I := I) (B := B) (F := F) MT τ)
    ∧
    (IsLeftInvariant (I := I) (B := B) (F := F) MT
        (rightInvariantExtension (I := I) (B := B) (F := F) MT τ)
      ↔ IsAdInvariant (𝕜 := 𝕜) (I := I) (B := B) (F := F) MT τ) := by
  sorry

end BundleInterface

end Autoform_Lie_groups_lie_algebras_lie_proposition_5_10_ii
