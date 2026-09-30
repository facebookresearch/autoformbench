/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/






















import ChallengeDeps
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Sheaves.Functors
import Submission.Helpers


open _root_.Autoform_Algebraic_Geometry_I_alg_geom_affine_qcoh_equiv_modules_over_pushforward_structure_sheaf
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace Autoform_Algebraic_Geometry_I_alg_geom_affine_qcoh_equiv_modules_over_pushforward_structure_sheaf

universe u v w







namespace OAlg







end OAlg

















theorem affineOver_equiv_qcohAlgebra_op (Y : Scheme.{u}) :
    Nonempty (AffineOver Y ≌ (QCohAlgebra Y)ᵒᵖ) := by
  sorry









abbrev pushforwardRingSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf RingCat Y.carrier :=
  (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf











theorem pushforwardStructureSheaf_isQuasiCoherentOAlgebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    IsQuasiCoherentOAlgebra Y (pushforwardStructureSheafAlg f) := by
  sorry















theorem pushforwardModulesOverPushforwardStructureSheaf_forgetToOY
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (pushforwardModulesOverPushforwardStructureSheaf f ⋙
        SheafOfModules.restrictScalars
          (OAlg.algebraMap (pushforwardStructureSheafAlg f)) ≅
      schemePushforwardModules f) := by
  sorry








theorem pushforwardModulesOverPushforwardStructureSheaf_preservesQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : QCoh X) :
    IsQuasiCoherentModuleOverAlgebra (pushforwardStructureSheafAlg f)
      ((pushforwardModulesOverPushforwardStructureSheaf f).obj F.obj) := by
  sorry











def pushforwardQCohAsModule
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    QCoh X ⥤ QCohModulesOverAlgebra (pushforwardStructureSheafAlg f) :=
  (IsQuasiCoherentModuleOverAlgebra (pushforwardStructureSheafAlg f)).lift
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
      pushforwardModulesOverPushforwardStructureSheaf f)
    (pushforwardModulesOverPushforwardStructureSheaf_preservesQuasicoherent f)







theorem pushforwardQCohAsModule_forgetToOY
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    Nonempty (pushforwardQCohAsModule f ⋙
        (IsQuasiCoherentModuleOverAlgebra
          (pushforwardStructureSheafAlg f)).ι ⋙
        SheafOfModules.restrictScalars
          (OAlg.algebraMap (pushforwardStructureSheafAlg f)) ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
        schemePushforwardModules f) := by
  sorry








theorem affine_qcoh_equiv_modules_over_pushforward_structure_sheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (pushforwardQCohAsModule f).IsEquivalence := by
  sorry







def affine_qcoh_equivalence_modules_over_pushforward_structure_sheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    QCoh X ≌ QCohModulesOverAlgebra (pushforwardStructureSheafAlg f) := by
  letI : (pushforwardQCohAsModule f).IsEquivalence :=
    affine_qcoh_equiv_modules_over_pushforward_structure_sheaf f
  exact (pushforwardQCohAsModule f).asEquivalence

end Autoform_Algebraic_Geometry_I_alg_geom_affine_qcoh_equiv_modules_over_pushforward_structure_sheaf


end