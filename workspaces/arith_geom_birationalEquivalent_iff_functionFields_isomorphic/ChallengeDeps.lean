/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_birationalEquivalent_iff_functionFields_isomorphic










structure AffineVarietyOver (k : Type*) [Field k] where
  Coord : Type*
  [coordCommRing : CommRing Coord]
  [coordIsDomain : IsDomain Coord]
  [coordAlgebra : Algebra k Coord]
  [coordFiniteType : Algebra.FiniteType k Coord]
  FunctionField : Type*
  [functionFieldField : Field FunctionField]
  [functionFieldAlgebra : Algebra k FunctionField]
  [coordToFunctionFieldAlgebra : Algebra Coord FunctionField]
  [coordFunctionFieldScalarTower : IsScalarTower k Coord FunctionField]
  isFractionRing : IsFractionRing Coord FunctionField

attribute [instance] AffineVarietyOver.coordCommRing
attribute [instance] AffineVarietyOver.coordIsDomain
attribute [instance] AffineVarietyOver.coordAlgebra
attribute [instance] AffineVarietyOver.coordFiniteType
attribute [instance] AffineVarietyOver.functionFieldField
attribute [instance] AffineVarietyOver.functionFieldAlgebra
attribute [instance] AffineVarietyOver.coordToFunctionFieldAlgebra
attribute [instance] AffineVarietyOver.coordFunctionFieldScalarTower
attribute [instance] AffineVarietyOver.isFractionRing

variable {k : Type*} [Field k]


noncomputable abbrev AffineVarietyOver.toScheme (X : AffineVarietyOver k) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of X.Coord)


noncomputable abbrev AffineVarietyOver.structureMap (X : AffineVarietyOver k) :
    X.toScheme ⟶ AlgebraicGeometry.Spec (.of k) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k X.Coord))






def BirationalEquivalent (X Y : AffineVarietyOver k) : Prop :=
  AlgebraicGeometry.Scheme.BirationalOver X.structureMap Y.structureMap


def FunctionFieldsIsomorphic (X Y : AffineVarietyOver k) : Prop :=
  Nonempty (X.FunctionField ≃ₐ[k] Y.FunctionField)



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_birationalEquivalent_iff_functionFields_isomorphic
