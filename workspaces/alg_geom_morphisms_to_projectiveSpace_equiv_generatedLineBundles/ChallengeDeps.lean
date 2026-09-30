/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles








abbrev projectiveSpaceGrading
    (k : Type u) [CommRing k] (n : ℕ) :
    ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  fun d => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d






instance projectiveSpaceGradingInstGradedRing
    (k : Type u) [CommRing k] (n : ℕ) :
    GradedRing (projectiveSpaceGrading k n) :=
  MvPolynomial.gradedAlgebra







abbrev projectiveSpace
    (k : Type u) [CommRing k] (n : ℕ) : Scheme :=
  Proj (projectiveSpaceGrading k n)







abbrev projectiveSpaceBase
    (k : Type u) [CommRing k] (n : ℕ) : Scheme :=
  Spec (CommRingCat.of (projectiveSpaceGrading k n 0))




abbrev projectiveSpaceToBase
    (k : Type u) [CommRing k] (n : ℕ) :
    projectiveSpace k n ⟶ projectiveSpaceBase k n :=
  Proj.toSpecZero (projectiveSpaceGrading k n)












def IsInvertibleModule {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ (ι : Type u) (U : ι → TopologicalSpace.Opens (X : Type u)),
    (Opens.grothendieckTopology (X : Type u)).CoversTop U ∧
      ∀ i : ι,
        Nonempty
          (M.over (U i) ≅
            SheafOfModules.free
              (R := CategoryTheory.Sheaf.over X.ringCatSheaf (U i))
              (ULift.{u} (Fin 1)))













def SectionsGenerate {X : Scheme.{u}} (M : X.Modules)
    {I : Type u} (s : I → M.sections) : Prop :=
  Epi (M.freeHomEquiv.symm s)








structure GeneratedLineBundle (X : Scheme.{u}) (I : Type u) where
  module : X.Modules
  invertible : IsInvertibleModule module
  sections : I → module.sections
  generate : SectionsGenerate module sections















def IsEquivalent {X : Scheme.{u}} {I : Type u}
    (A B : GeneratedLineBundle X I) : Prop :=
  ∃ e : A.module ≅ B.module,
    ∀ i : I,
      SheafOfModules.sectionsMap e.hom (A.sections i) = B.sections i





end Autoform_Algebraic_Geometry_I_alg_geom_morphisms_to_projectiveSpace_equiv_generatedLineBundles

end