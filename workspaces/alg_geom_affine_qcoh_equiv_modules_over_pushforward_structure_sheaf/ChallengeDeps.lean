import Mathlib

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace Autoform_Algebraic_Geometry_I_alg_geom_affine_qcoh_equiv_modules_over_pushforward_structure_sheaf

universe u v w










abbrev AffineOver (Y : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.Over
    (@IsAffineHom)
    (⊤ : MorphismProperty Scheme.{u})
    Y








abbrev OAlg (Y : Scheme.{u}) : Type (u + 1) :=
  Under Y.sheaf








abbrev forgetCommRingToRingSheaf (Y : Scheme.{u}) :
    TopCat.Sheaf CommRingCat Y.carrier ⥤
      TopCat.Sheaf RingCat Y.carrier :=
  CategoryTheory.sheafCompose
    (Opens.grothendieckTopology Y.carrier)
    (forget₂ CommRingCat RingCat)

namespace OAlg


abbrev ringSheaf {Y : Scheme.{u}} (A : OAlg Y) :
    TopCat.Sheaf RingCat Y.carrier :=
  (forgetCommRingToRingSheaf Y).obj A.right


abbrev algebraMap {Y : Scheme.{u}} (A : OAlg Y) :
    Y.ringCatSheaf ⟶ A.ringSheaf :=
  (forgetCommRingToRingSheaf Y).map A.hom







abbrev underlyingModule {Y : Scheme.{u}} (A : OAlg Y) :
    SheafOfModules Y.ringCatSheaf :=
  (SheafOfModules.restrictScalars A.algebraMap).obj
    (SheafOfModules.unit A.ringSheaf)

end OAlg








def IsQuasiCoherentOAlgebra (Y : Scheme.{u}) :
    ObjectProperty (OAlg Y) :=
  fun A => (OAlg.underlyingModule A).IsQuasicoherent


abbrev QCohAlgebra (Y : Scheme.{u}) : Type (u + 1) :=
  (IsQuasiCoherentOAlgebra Y).FullSubcategory






abbrev QCoh (X : Scheme.{u}) : Type (u + 1) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory








abbrev pushforwardCommRingSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TopCat.Sheaf CommRingCat Y.carrier :=
  (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf







def pushforwardStructureSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ pushforwardCommRingSheaf f :=
  CategoryTheory.ObjectProperty.homMk f.c


def pushforwardStructureSheafAlg {X Y : Scheme.{u}} (f : X ⟶ Y) :
    OAlg Y :=
  Under.mk (pushforwardStructureSheafHom f)









abbrev schemePushforwardModules {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules X.ringCatSheaf ⥤ SheafOfModules Y.ringCatSheaf :=
  SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom f)










def IsQuasiCoherentModuleOverAlgebra
    {Y : Scheme.{u}} (A : OAlg Y) :
    ObjectProperty (SheafOfModules A.ringSheaf) :=
  fun M =>
    ((SheafOfModules.restrictScalars A.algebraMap).obj M).IsQuasicoherent


abbrev QCohModulesOverAlgebra
    {Y : Scheme.{u}} (A : OAlg Y) : Type (u + 1) :=
  (IsQuasiCoherentModuleOverAlgebra A).FullSubcategory











abbrev pushforwardModulesOverPushforwardStructureSheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules X.ringCatSheaf ⥤
      SheafOfModules (OAlg.ringSheaf (pushforwardStructureSheafAlg f)) :=
  SheafOfModules.pushforward
    (𝟙 (OAlg.ringSheaf (pushforwardStructureSheafAlg f)))










end Autoform_Algebraic_Geometry_I_alg_geom_affine_qcoh_equiv_modules_over_pushforward_structure_sheaf

end