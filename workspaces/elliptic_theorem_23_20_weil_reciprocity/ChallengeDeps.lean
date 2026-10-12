/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
















open CategoryTheory AlgebraicGeometry
open scoped BigOperators

noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_theorem_23_20_weil_reciprocity

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : Scheme.{u}) (π : X ⟶ Spec (CommRingCat.of k))
variable [IsIntegral X] [IsProper π] [SmoothOfRelativeDimension 1 π]







def RationalPoint : Type u :=
  { P : Spec (CommRingCat.of k) ⟶ X // P ≫ π = 𝟙 _ }


noncomputable abbrev underlying
    (P : RationalPoint X π) : X :=
  P.1 (IsLocalRing.closedPoint k)













end Autoform_Elliptic_Curves_elliptic_theorem_23_20_weil_reciprocity

end