/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib












noncomputable section

universe u v

namespace Autoform_Elliptic_Curves_elliptic_baker_theorem


abbrev XY : Type := Fin 2


abbrev PlanePoly (k : Type u) [CommSemiring k] : Type u :=
  MvPolynomial XY k

namespace NewtonPolygon


abbrev Point : Type := XY → ℝ


def exponentPoint (m : XY →₀ ℕ) : Point :=
  fun i => (m i : ℝ)


def supportExponentSet {k : Type u} [CommSemiring k] (f : PlanePoly k) : Set Point :=
  {p | ∃ m, m ∈ f.support ∧ exponentPoint m = p}


def polygon {k : Type u} [CommSemiring k] (f : PlanePoly k) : Set Point :=
  convexHull ℝ (supportExponentSet f)






def interiorLatticePoints {k : Type u} [CommSemiring k] (f : PlanePoly k) :
    Set (XY → ℤ) :=
  {z | (fun i : XY => (z i : ℝ)) ∈ interior (polygon f)}

end NewtonPolygon



namespace NewtonPolygon


end NewtonPolygon













structure Place (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] where
  v : AddValuation F (WithTop ℤ)

  
  finite_ne_zero' : ∀ {x : F}, x ≠ 0 → ∃ n : ℤ, v x = (n : WithTop ℤ)

  
  exists_uniformizer' : ∃ π : F, π ≠ 0 ∧ v π = ((1 : ℤ) : WithTop ℤ)

  
  trivial_on_base' :
    ∀ {a : k}, a ≠ 0 → v (algebraMap k F a) = ((0 : ℤ) : WithTop ℤ)

namespace Place

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]


@[ext]
theorem ext {P Q : Place k F} (h : P.v = Q.v) : P = Q := by
  cases P
  cases Q
  cases h
  rfl


abbrev valuationRing (P : Place k F) : ValuationSubring F :=
  (AddValuation.toValuation P.v).valuationSubring


def algebraMapValuationRing (P : Place k F) : k →+* (P.valuationRing : Type v) :=
  (algebraMap k F).codRestrict P.valuationRing fun a => by
    rw [Valuation.mem_valuationSubring_iff, AddValuation.toValuation_apply]
    by_cases ha : a = 0
    · subst a
      simp
    · rw [P.trivial_on_base' ha]
      simp


abbrev ResidueField (P : Place k F) : Type v :=
  IsLocalRing.ResidueField (P.valuationRing : Type v)


noncomputable def residueDegree (P : Place k F) : ℕ := by
  letI : Algebra k (P.valuationRing : Type v) := P.algebraMapValuationRing.toAlgebra
  exact Module.finrank k P.ResidueField







noncomputable def ord (P : Place k F) (x : F) : ℤ := by
  classical
  exact
    if hx : x = 0 then
      0
    else
      Classical.choose (P.finite_ne_zero' hx)

end Place








abbrev Divisor (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] :=
  Place k F →₀ ℤ

namespace Divisor

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]








def degree (D : Divisor k F) : ℤ :=
  D.sum fun P n => n * (P.residueDegree : ℤ)

end Divisor








class HasFinitePrincipalDivisors
    (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] : Prop where
  finite_support_units :
    ∀ x : Fˣ,
      (Function.support fun P : Place k F => Place.ord P (x : F)).Finite









def memRiemannRoch
    {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
    (D : Divisor k F) (x : F) : Prop :=
  x = 0 ∨ ∀ P : Place k F, 0 ≤ Place.ord P x + D P












abbrev CoordinateRing (k : Type u) [Field k] (f : PlanePoly k) : Type u :=
  PlanePoly k ⧸ Ideal.span ({f} : Set (PlanePoly k))


def baseChangeToAlgClosure (k : Type u) [Field k] (f : PlanePoly k) :
    PlanePoly (AlgebraicClosure k) :=
  MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f


def GeometricallyIrreducible {k : Type u} [Field k] (f : PlanePoly k) : Prop :=
  Irreducible (baseChangeToAlgClosure k f)




abbrev FunctionField (k : Type u) [Field k] (f : PlanePoly k)
    [IsDomain (CoordinateRing k f)] : Type u :=
  FractionRing (CoordinateRing k f)





end Autoform_Elliptic_Curves_elliptic_baker_theorem

end
