/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option maxSynthPendingDepth 3






























noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open TensorProduct
open DirectSum

universe u

namespace Autoform_Tensor_Categories_tensor_cat_theorem_1_23_1

variable (k : Type u) [Field k]








section CoendConstruction

variable {C : Type u} [Category.{u} C]






abbrev Summand (F : C ⥤ ModuleCat.{u} k) (X : C) : Type u :=
  Module.Dual k (F.obj X) ⊗[k] (F.obj X)










abbrev Raw (F : C ⥤ ModuleCat.{u} k) :=
  ⨁ X , Summand k F X






noncomputable def lofRaw
    (F : C ⥤ ModuleCat.{u} k) (X : C) :
    Summand k F X →ₗ[k] Raw k F :=
  letI : DecidableEq C := Classical.decEq C
  DirectSum.lof k C (fun X : C => Summand k F X) X










noncomputable def dinaturalityGenerator
    (F : C ⥤ ModuleCat.{u} k) {X Y : C} (f : X ⟶ Y)
    (y : Module.Dual k (F.obj Y)) (x : F.obj X) :
    Raw k F :=
  lofRaw k F Y
      (y ⊗ₜ[k] ((F.map f).hom x))
    -
  lofRaw k F X
      (((F.map f).hom.dualMap y) ⊗ₜ[k] x)






def Relations (F : C ⥤ ModuleCat.{u} k) :
    Submodule k (Raw k F) :=
  Submodule.span k
    { z : Raw k F |
      ∃ (X Y : C) (f : X ⟶ Y)
        (y : Module.Dual k (F.obj Y)) (x : F.obj X),
        z = dinaturalityGenerator k F f y x }







abbrev Space (F : C ⥤ ModuleCat.{u} k) : Type u :=
  Raw k F ⧸ Relations k F







noncomputable def ι (F : C ⥤ ModuleCat.{u} k) (X : C) :
    Summand k F X →ₗ[k] Space k F :=
  (Submodule.mkQ (Relations k F)).comp (lofRaw k F X)





















































end CoendConstruction






abbrev Coend {C : Type u} [Category.{u} C]
    (F : C ⥤ ModuleCat.{u} k) : Type u :=
  Space k F









section RightComoduleCat

variable {k}
variable {H : Type u} [AddCommGroup H] [Module k H]
variable {coalg : Coalgebra k H}

end RightComoduleCat







section FiniteRightComoduleCat

variable {k}
variable {H : Type u} [AddCommGroup H] [Module k H]
variable {coalg : Coalgebra k H}


end FiniteRightComoduleCat














section Reconstruction

variable {C : Type u}
variable [Category.{u} C]















noncomputable def fiberCoaction
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    (X : C) :
    F.obj X →ₗ[k] (F.obj X ⊗[k] Coend k F) := by
  classical
  letI : FiniteDimensional k (F.obj X) := hF_finite X
  exact
    (LinearMap.lTensor
        (F.obj X)
        (ι k F X)) ∘ₗ
      (TensorProduct.assoc k
        (F.obj X)
        (Module.Dual k (F.obj X))
        (F.obj X)).toLinearMap ∘ₗ
        (LinearMap.rTensor
          (F.obj X)
          (coevaluation k (F.obj X))) ∘ₗ
          (TensorProduct.lid k (F.obj X)).symm.toLinearMap















end Reconstruction










section ReconstructionTheorem

variable {C : Type u}
variable [Category.{u} C] [Preadditive C] [Abelian C] [Linear k C]



end ReconstructionTheorem

end Autoform_Tensor_Categories_tensor_cat_theorem_1_23_1
end