/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.Coevaluation
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Tensor_Categories_tensor_cat_theorem_1_23_1
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


























noncomputable def summandCounit
    (F : C ⥤ ModuleCat.{u} k) (X : C) :
    Summand k F X →ₗ[k] k :=
  TensorProduct.lift
    { toFun := fun φ =>
        { toFun := fun x => φ x
          map_add' := by
            intro x y
            simp
          map_smul' := by
            intro a x
            simp }
      map_add' := by
        intro φ ψ
        ext x
        simp
      map_smul' := by
        intro a φ
        ext x
        simp }






noncomputable def counitRaw
    (F : C ⥤ ModuleCat.{u} k) :
    Raw k F →ₗ[k] k :=
  letI : DecidableEq C := Classical.decEq C
  DirectSum.toModule k C k
    (fun X : C => summandCounit k F X)









theorem counitRaw_vanishes_on_relations
    (F : C ⥤ ModuleCat.{u} k) :
    Relations k F ≤ (counitRaw k F).ker := by
  
  sorry







noncomputable def counit
    (F : C ⥤ ModuleCat.{u} k) :
    Space k F →ₗ[k] k :=
  (Relations k F).liftQ
    (counitRaw k F)
    (counitRaw_vanishes_on_relations k F)






















noncomputable def summandComulFun
    (F : C ⥤ ModuleCat.{u} k) (X : C)
    [FiniteDimensional k (F.obj X)]
    (φ : Module.Dual k (F.obj X)) (x : F.obj X) :
    Space k F ⊗[k] Space k F :=
  ∑ i : Fin (Module.finrank k (F.obj X)),
    (ι k F X (φ ⊗ₜ[k] (Module.finBasis k (F.obj X)) i)) ⊗ₜ[k]
      (ι k F X (((Module.finBasis k (F.obj X)).dualBasis i) ⊗ₜ[k] x))


theorem summandComulFun_add_right
    (F : C ⥤ ModuleCat.{u} k) (X : C)
    [FiniteDimensional k (F.obj X)]
    (φ : Module.Dual k (F.obj X)) (x y : F.obj X) :
    summandComulFun k F X φ (x + y) =
      summandComulFun k F X φ x + summandComulFun k F X φ y := by
  
  sorry


theorem summandComulFun_smul_right
    (F : C ⥤ ModuleCat.{u} k) (X : C)
    [FiniteDimensional k (F.obj X)]
    (φ : Module.Dual k (F.obj X)) (a : k) (x : F.obj X) :
    summandComulFun k F X φ (a • x) = a • summandComulFun k F X φ x := by
  
  sorry






noncomputable def summandComulRight
    (F : C ⥤ ModuleCat.{u} k) (X : C)
    [FiniteDimensional k (F.obj X)]
    (φ : Module.Dual k (F.obj X)) :
    (F.obj X) →ₗ[k] (Space k F ⊗[k] Space k F) where
  toFun := fun x => summandComulFun k F X φ x
  map_add' := summandComulFun_add_right k F X φ
  map_smul' := summandComulFun_smul_right k F X φ


theorem summandComulRight_add_left
    (F : C ⥤ ModuleCat.{u} k) (X : C)
    [FiniteDimensional k (F.obj X)]
    (φ ψ : Module.Dual k (F.obj X)) :
    summandComulRight k F X (φ + ψ) =
      summandComulRight k F X φ + summandComulRight k F X ψ := by
  
  sorry


theorem summandComulRight_smul_left
    (F : C ⥤ ModuleCat.{u} k) (X : C)
    [FiniteDimensional k (F.obj X)]
    (a : k) (φ : Module.Dual k (F.obj X)) :
    summandComulRight k F X (a • φ) = a • summandComulRight k F X φ := by
  
  sorry











noncomputable def summandComul
    (F : C ⥤ ModuleCat.{u} k) (X : C)
    [FiniteDimensional k (F.obj X)] :
    Summand k F X →ₗ[k] (Space k F ⊗[k] Space k F) :=
  TensorProduct.lift
    { toFun := fun φ => summandComulRight k F X φ
      map_add' := summandComulRight_add_left k F X
      map_smul' := summandComulRight_smul_left k F X }






noncomputable def comulRaw
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    Raw k F →ₗ[k] (Space k F ⊗[k] Space k F) :=
  letI : DecidableEq C := Classical.decEq C
  DirectSum.toModule k C (Space k F ⊗[k] Space k F)
    (fun X : C => by
      letI : FiniteDimensional k (F.obj X) := hF_finite X
      exact summandComul k F X)










theorem comulRaw_vanishes_on_relations
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    Relations k F ≤ (comulRaw k F hF_finite).ker := by
  
  
  sorry







noncomputable def comul
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    Space k F →ₗ[k] (Space k F ⊗[k] Space k F) :=
  (Relations k F).liftQ
    (comulRaw k F hF_finite)
    (comulRaw_vanishes_on_relations k F hF_finite)







theorem coalgebra_coassoc
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    (TensorProduct.assoc k (Space k F) (Space k F) (Space k F)).toLinearMap ∘ₗ
        LinearMap.rTensor (Space k F) (comul k F hF_finite) ∘ₗ
          comul k F hF_finite =
      LinearMap.lTensor (Space k F) (comul k F hF_finite) ∘ₗ
        comul k F hF_finite := by
  sorry







theorem coalgebra_rTensor_counit_comp_comul
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    LinearMap.rTensor (Space k F) (counit k F) ∘ₗ comul k F hF_finite =
      TensorProduct.mk k k (Space k F) 1 := by
  sorry







theorem coalgebra_lTensor_counit_comp_comul
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    LinearMap.lTensor (Space k F) (counit k F) ∘ₗ comul k F hF_finite =
      (TensorProduct.mk k (Space k F) k).flip 1 := by
  sorry








@[reducible] noncomputable def coalgebra
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    Coalgebra k (Space k F) where
  comul := comul k F hF_finite
  counit := counit k F
  coassoc := coalgebra_coassoc k F hF_finite
  rTensor_counit_comp_comul := coalgebra_rTensor_counit_comp_comul k F hF_finite
  lTensor_counit_comp_comul := coalgebra_lTensor_counit_comp_comul k F hF_finite

end CoendConstruction







@[reducible] noncomputable def coendCoalgebra
    {C : Type u} [Category.{u} C]
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    Coalgebra k (Coend k F) :=
  coalgebra k F hF_finite
















structure RightComodule
    (H : Type u) [AddCommGroup H] [Module k H]
    (coalg : Coalgebra k H) :
    Type (u + 1) where
  V : ModuleCat.{u} k
  coact : V →ₗ[k] (V ⊗[k] H)
  counit :
    ((TensorProduct.rid k V).toLinearMap ∘ₗ
        (LinearMap.lTensor V coalg.counit) ∘ₗ
        coact) =
      LinearMap.id
  coassoc :
    ((TensorProduct.assoc k V H H).toLinearMap ∘ₗ
        (LinearMap.rTensor H coact) ∘ₗ
        coact) =
      ((LinearMap.lTensor V coalg.comul) ∘ₗ
        coact)

section RightComoduleCat

variable {k}
variable {H : Type u} [AddCommGroup H] [Module k H]
variable {coalg : Coalgebra k H}







structure Hom (M N : RightComodule k H coalg) where
  hom : M.V ⟶ N.V
  comm :
    ((TensorProduct.map hom.hom (LinearMap.id : H →ₗ[k] H)) ∘ₗ M.coact) =
      (N.coact ∘ₗ hom.hom)

@[ext]
theorem hom_ext {M N : RightComodule k H coalg} (f g : Hom M N)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  simp






theorem rightComodule_id_comm (M : RightComodule k H coalg) :
    ((TensorProduct.map (ModuleCat.Hom.hom (𝟙 M.V))
          (LinearMap.id : H →ₗ[k] H)) ∘ₗ M.coact) =
      (M.coact ∘ₗ ModuleCat.Hom.hom (𝟙 M.V)) := by
  
  sorry






theorem rightComodule_comp_comm {M N P : RightComodule k H coalg}
    (f : Hom M N) (g : Hom N P) :
    ((TensorProduct.map (f.hom ≫ g.hom).hom (LinearMap.id : H →ₗ[k] H)) ∘ₗ
        M.coact) =
      (P.coact ∘ₗ (f.hom ≫ g.hom).hom) := by
  
  sorry







instance instCategoryRightComodule : Category (RightComodule k H coalg) where
  Hom M N := Hom M N
  id M :=
    { hom := 𝟙 M.V
      comm := rightComodule_id_comm M }
  comp {M N P} f g :=
    { hom := f.hom ≫ g.hom
      comm := rightComodule_comp_comm f g }
  id_comp := by
    intro M N f
    ext
    simp
  comp_id := by
    intro M N f
    ext
    simp
  assoc := by
    intro M N P Q f g h
    ext
    simp [Category.assoc]






def forgetRightComodule :
    RightComodule k H coalg ⥤ ModuleCat.{u} k where
  obj M := M.V
  map f := f.hom
  map_id := by
    intro M
    rfl
  map_comp := by
    intro M N P f g
    rfl

end RightComoduleCat












structure FiniteRightComodule
    (H : Type u) [AddCommGroup H] [Module k H]
    (coalg : Coalgebra k H) :
    Type (u + 1) where
  toRightComodule : RightComodule k H coalg
  finite : FiniteDimensional k toRightComodule.V

section FiniteRightComoduleCat

variable {k}
variable {H : Type u} [AddCommGroup H] [Module k H]
variable {coalg : Coalgebra k H}






instance instCategoryFiniteRightComodule :
    Category (FiniteRightComodule k H coalg) where
  Hom M N := M.toRightComodule ⟶ N.toRightComodule
  id M := 𝟙 M.toRightComodule
  comp f g := f ≫ g
  id_comp := by
    intro M N f
    simp
  comp_id := by
    intro M N f
    simp
  assoc := by
    intro M N P Q f g h
    simp [Category.assoc]

end FiniteRightComoduleCat














section Reconstruction

variable {C : Type u}
variable [Category.{u} C]








theorem fiberRightComodule_counit
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    (X : C) :
    ((TensorProduct.rid k (F.obj X)).toLinearMap ∘ₗ
        (LinearMap.lTensor (F.obj X) (coendCoalgebra k F hF_finite).counit) ∘ₗ
        fiberCoaction k F hF_finite X) =
      LinearMap.id := by
  sorry







theorem fiberRightComodule_coassoc
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    (X : C) :
    ((TensorProduct.assoc k (F.obj X) (Coend k F) (Coend k F)).toLinearMap ∘ₗ
        (LinearMap.rTensor (Coend k F) (fiberCoaction k F hF_finite X)) ∘ₗ
        fiberCoaction k F hF_finite X) =
      ((LinearMap.lTensor (F.obj X) (coendCoalgebra k F hF_finite).comul) ∘ₗ
        fiberCoaction k F hF_finite X) := by
  sorry








noncomputable def fiberRightComodule
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    (X : C) :
    RightComodule k (Coend k F) (coendCoalgebra k F hF_finite) where
  V := F.obj X
  coact := fiberCoaction k F hF_finite X
  counit := fiberRightComodule_counit k F hF_finite X
  coassoc := fiberRightComodule_coassoc k F hF_finite X








theorem fiberComoduleMap_comm
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    {X Y : C} (f : X ⟶ Y) :
    ((TensorProduct.map (F.map f).hom
          (LinearMap.id : Coend k F →ₗ[k] Coend k F)) ∘ₗ
        (fiberRightComodule k F hF_finite X).coact) =
      ((fiberRightComodule k F hF_finite Y).coact ∘ₗ (F.map f).hom) := by
  sorry









noncomputable def fiberComoduleMap
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    {X Y : C} (f : X ⟶ Y) :
    fiberRightComodule k F hF_finite X ⟶
      fiberRightComodule k F hF_finite Y where
  hom := F.map f
  comm := fiberComoduleMap_comm k F hF_finite f






noncomputable def fiberFiniteRightComodule
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    (X : C) :
    FiniteRightComodule k (Coend k F) (coendCoalgebra k F hF_finite) where
  toRightComodule := fiberRightComodule k F hF_finite X
  finite := hF_finite X






theorem reconstructionFunctor_map_id
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    (X : C) :
    fiberComoduleMap k F hF_finite (𝟙 X) =
      𝟙 (fiberFiniteRightComodule k F hF_finite X) := by
  
  sorry






theorem reconstructionFunctor_map_comp
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X))
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberComoduleMap k F hF_finite (f ≫ g) =
      fiberComoduleMap k F hF_finite f ≫ fiberComoduleMap k F hF_finite g := by
  
  sorry









noncomputable def reconstructionFunctor
    (F : C ⥤ ModuleCat.{u} k)
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    C ⥤ FiniteRightComodule k (Coend k F) (coendCoalgebra k F hF_finite) where
  obj X := fiberFiniteRightComodule k F hF_finite X
  map {X Y} f := fiberComoduleMap k F hF_finite f
  map_id := reconstructionFunctor_map_id k F hF_finite
  map_comp := fun {X Y Z} f g => reconstructionFunctor_map_comp k F hF_finite f g

end Reconstruction










section ReconstructionTheorem

variable {C : Type u}
variable [Category.{u} C] [Preadditive C] [Abelian C] [Linear k C]


























theorem theorem_1_23_1
    (F : C ⥤ ModuleCat.{u} k)
    [F.Additive]
    [Functor.Linear k F]
    [F.Faithful]
    [PreservesFiniteLimits F]
    [PreservesFiniteColimits F]
    (hF_finite : ∀ X : C, FiniteDimensional k (F.obj X)) :
    (reconstructionFunctor k F hF_finite).IsEquivalence := by
  
  sorry

end ReconstructionTheorem

end Autoform_Tensor_Categories_tensor_cat_theorem_1_23_1

end
