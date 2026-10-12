/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Autoform_Elliptic_Curves_elliptic_theorem_4_17













structure ProjectiveCurve (k : Type u) [Field k] where
  toScheme : Scheme
  structureMap : toScheme ⟶ Spec (CommRingCat.of k)
  [isProper : IsProper structureMap]
  [isIntegral : IsIntegral toScheme]
  dim_eq_one : topologicalKrullDim toScheme = 1

attribute [instance] ProjectiveCurve.isProper ProjectiveCurve.isIntegral









structure CurveMorphism {k : Type u} [Field k]
    (C₁ C₂ : ProjectiveCurve k) where
  toSchemeHom : C₁.toScheme ⟶ C₂.toScheme
  over_base : toSchemeHom ≫ C₂.structureMap = C₁.structureMap



end Autoform_Elliptic_Curves_elliptic_theorem_4_17
