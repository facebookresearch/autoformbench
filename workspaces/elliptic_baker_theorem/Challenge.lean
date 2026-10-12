/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.MetricSpace.Basic
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_baker_theorem











noncomputable section

universe u v

namespace Autoform_Elliptic_Curves_elliptic_baker_theorem





namespace NewtonPolygon











end NewtonPolygon






theorem interiorLatticePoints_finite {k : Type u} [CommSemiring k] (f : PlanePoly k) :
    (NewtonPolygon.interiorLatticePoints f).Finite := by
  sorry

namespace NewtonPolygon



end NewtonPolygon



namespace Place

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]



end Place

namespace NewtonPolygon

def interiorLatticePointCard {k : Type u} [CommSemiring k] (f : PlanePoly k) : ℕ :=
  ((interiorLatticePoints_finite (f := f)).toFinset).card
end NewtonPolygon
theorem v_eq_ord_of_ne_zero {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (P : Place k F) {x : F} (hx : x ≠ 0) :
    P.v x = (P.ord x : WithTop ℤ) := by
  sorry



namespace Divisor

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]


def coeff (D : Divisor k F) (P : Place k F) : ℤ :=
  D P




def Effective (D : Divisor k F) : Prop :=
  ∀ P : Place k F, 0 ≤ D P

end Divisor

open Divisor








noncomputable def principalDivisor
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    [HasFinitePrincipalDivisors k F] (x : Fˣ) : Divisor k F :=
  Finsupp.ofSupportFinite
    (fun P : Place k F => Place.ord P (x : F))
    (HasFinitePrincipalDivisors.finite_support_units (k := k) (F := F) x)









theorem riemannRochSpace_add_mem
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (D : Divisor k F) (x y : F)
    (hx : memRiemannRoch D x) (hy : memRiemannRoch D y) :
    memRiemannRoch D (x + y) := by
  sorry








theorem riemannRochSpace_smul_mem
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (D : Divisor k F) (a : k) (x : F)
    (hx : memRiemannRoch D x) :
    memRiemannRoch D (a • x) := by
  sorry























def riemannRochSpace
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (D : Divisor k F) : Submodule k F where
  carrier := {x : F | memRiemannRoch D x}
  zero_mem' := by
    left
    rfl
  add_mem' := fun {x y} hx hy => riemannRochSpace_add_mem D x y hx hy
  smul_mem' := fun a {x} hx => riemannRochSpace_smul_mem D a x hx


noncomputable def riemannRochDimension
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (D : Divisor k F) : ℕ :=
  Module.finrank k (riemannRochSpace D)






noncomputable def riemannRochDefect
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (D : Divisor k F) : ℤ :=
  Divisor.degree D + 1 - (riemannRochDimension D : ℤ)










class HasRiemannRochTheory
    (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] : Prop
    extends HasFinitePrincipalDivisors k F where
  finite_riemannRoch :
    ∀ D : Divisor k F, FiniteDimensional k (riemannRochSpace D)

  exists_eventual_defect :
    ∃ g : ℕ, ∃ B : ℤ, ∀ D : Divisor k F,
      B ≤ Divisor.degree D → riemannRochDefect D = (g : ℤ)





noncomputable def genus
    (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]
    [HasRiemannRochTheory k F] : ℕ :=
  Classical.choose (HasRiemannRochTheory.exists_eventual_defect (k := k) (F := F))


noncomputable def genusWith
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (hRR : HasRiemannRochTheory k F) : ℕ :=
  @genus k F _ _ _ hRR
theorem genus_spec
    (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]
    [HasRiemannRochTheory k F] :
    ∃ B : ℤ, ∀ D : Divisor k F,
      B ≤ Divisor.degree D →
        riemannRochDefect D = (genus k F : ℤ) := by
  simpa [genus] using
    Classical.choose_spec
      (HasRiemannRochTheory.exists_eventual_defect (k := k) (F := F))












theorem coordinateRing_isDomain_of_geometricallyIrreducible
    {k : Type u} [Field k] {f : PlanePoly k}
    (hf : GeometricallyIrreducible f) :
    IsDomain (CoordinateRing k f) := by
  sorry











theorem functionField_hasRiemannRochTheory
    {k : Type u} [Field k] (f : PlanePoly k)
    [IsDomain (CoordinateRing k f)]
    (hf : GeometricallyIrreducible f) :
    @HasRiemannRochTheory k (FunctionField k f) _ _
      (inferInstance : Algebra k (FunctionField k f)) := by
  sorry









theorem baker_theorem
    {k : Type u} [Field k] (f : PlanePoly k)
    [IsDomain (CoordinateRing k f)]
    (hf : GeometricallyIrreducible f) :
    @genusWith k (FunctionField k f) _ _
        (inferInstance : Algebra k (FunctionField k f))
        (functionField_hasRiemannRochTheory f hf)
      ≤ NewtonPolygon.interiorLatticePointCard f := by
  sorry

end Autoform_Elliptic_Curves_elliptic_baker_theorem

end
