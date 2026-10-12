/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_23_20_weil_reciprocity
















open CategoryTheory AlgebraicGeometry
open scoped BigOperators

noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_theorem_23_20_weil_reciprocity

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : Scheme.{u}) (π : X ⟶ Spec (CommRingCat.of k))
variable [IsIntegral X]











instance rationalPointStalkIsDVR [IsProper π] [SmoothOfRelativeDimension 1 π]
    (P : RationalPoint X π) :
    IsDiscreteValuationRing (X.presheaf.stalk (underlying X π P)) := by
  sorry


variable [IsProper π] [SmoothOfRelativeDimension 1 π]












noncomputable def orderAt (P : RationalPoint X π)
    (f : (X.functionField)ˣ) : ℤ :=
  - Multiplicative.toAdd
    ((IsDiscreteValuationRing.maximalIdeal
      (X.presheaf.stalk (underlying X π P))).valuationOfNeZero f)







theorem orderAt_finite_support (f : (X.functionField)ˣ) :
    (Function.support (fun P : RationalPoint X π => orderAt X π P f)).Finite := by
  sorry











noncomputable def principalDivisor (f : (X.functionField)ˣ) :
    RationalPoint X π →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun P => orderAt X π P f)
    (orderAt_finite_support X π f)

theorem exists_localUnit_of_orderAt_eq_zero
    (P : RationalPoint X π) (f : (X.functionField)ˣ)
    (hf : orderAt X π P f = 0) :
    ∃ u : (X.presheaf.stalk (underlying X π P))ˣ,
      (algebraMap (X.presheaf.stalk (underlying X π P)) X.functionField)
          (u : X.presheaf.stalk (underlying X π P)) =
        (f : X.functionField) := by
  sorry






noncomputable def localUnitOfOrderZero
    (P : RationalPoint X π) (f : (X.functionField)ˣ)
    (hf : orderAt X π P f = 0) :
    (X.presheaf.stalk (underlying X π P))ˣ :=
  Classical.choose (exists_localUnit_of_orderAt_eq_zero X π P f hf)












noncomputable def evaluateAt (P : RationalPoint X π)
    (f : (X.functionField)ˣ) (hf : orderAt X π P f = 0) : kˣ :=
  Units.map (X.stalkClosedPointTo P.1).hom.toMonoidHom
    (localUnitOfOrderZero X π P f hf)
theorem orderAt_eq_zero_of_mem_support
    (f : (X.functionField)ˣ) (D : RationalPoint X π →₀ ℤ)
    (hdisj : Disjoint (principalDivisor X π f).support D.support)
    {P : RationalPoint X π} (hP : P ∈ D.support) :
    orderAt X π P f = 0 := by
  by_contra hP0
  apply (Finset.disjoint_left.mp hdisj) ?_ hP
  rw [Finsupp.mem_support_iff]
  simpa only [principalDivisor, Finsupp.ofSupportFinite_coe] using hP0











noncomputable def evalOnDivisor (f : (X.functionField)ˣ)
    (D : RationalPoint X π →₀ ℤ)
    (hdisj : Disjoint (principalDivisor X π f).support D.support) : kˣ :=
  ∏ P : D.support,
    (evaluateAt X π P.1 f
      (orderAt_eq_zero_of_mem_support X π f D hdisj P.2)) ^ (D P.1)




theorem theorem_23_20_weil_reciprocity (f g : (X.functionField)ˣ)
    (hfg : Disjoint
      (principalDivisor X π f).support
      (principalDivisor X π g).support) :
    evalOnDivisor X π f (principalDivisor X π g) hfg =
      evalOnDivisor X π g (principalDivisor X π f) hfg.symm := by
  sorry

end Autoform_Elliptic_Curves_elliptic_theorem_23_20_weil_reciprocity

end
