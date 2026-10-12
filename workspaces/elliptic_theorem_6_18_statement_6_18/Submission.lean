/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Group.End
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Submission.Helpers
import ChallengeDeps














































open _root_.Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18
noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18

universe u v

variable {K : Type u} [Field K]




















noncomputable def polynomialFunction (E : WeierstrassCurve K) (p : Polynomial K) :
    FunctionField E :=
  p.eval₂ (algebraMap K (FunctionField E)) (functionFieldX E)





namespace Coords3

















end Coords3



namespace ProjectiveTriple

variable (T : ProjectiveTriple K)


def evalFn (P : Coords3 K) : Fin 3 → K :=
  fun i =>
    if i = (0 : Fin 3) then Coords3.X P
    else if i = (1 : Fin 3) then Coords3.Y P
    else Coords3.Z P


def eval (P : Coords3 K) : Coords3 K :=
  (MvPolynomial.eval (evalFn P) T.X,
   MvPolynomial.eval (evalFn P) T.Y,
   MvPolynomial.eval (evalFn P) T.Z)


def NonzeroAt (P : Coords3 K) : Prop :=
  Coords3.Nonzero (T.eval P)







end ProjectiveTriple







namespace ProjectiveTriple







end ProjectiveTriple









namespace ProjectiveTriple





end ProjectiveTriple



namespace FunctionFieldPullbackData

variable {E₁ E₂ : WeierstrassCurve K} {T : ProjectiveTriple K}






theorem finite_dimensional (D : FunctionFieldPullbackData E₁ E₂ T) :
    FiniteDimensional D.imageField (FunctionField E₁) :=
  D.finite_extension

end FunctionFieldPullbackData













variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
variable {E : WeierstrassCurve K}
variable [hE : (GeometricCurve (K := K) Ω E).IsElliptic]





attribute [coe] EllipticCurveEndomorphism.toEnd












theorem functionField_degree_unique
    (φ : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)
    (D₁ D₂ : AlgebraicEndomorphismData (Ω := Ω) (E := E) φ) :
    D₁.functionField.degree = D₂.functionField.degree := by
  sorry








theorem integer_scalar_endomorphisms_injective :
    Function.Injective
      (fun t : ℤ =>
        t • (1 : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)) := by
  sorry













def IsDual
    (α β : EllipticCurveEndomorphism E Ω) : Prop :=
  (α.toEnd = 0 ∧ β.toEnd = 0) ∨
  (α.toEnd ≠ 0 ∧
    β.toEnd * α.toEnd =
      (degree (E := E) (Ω := Ω) α) •
        (1 : AddMonoid.End (GeometricCurve (K := K) Ω E).Point))

theorem exists_unique_dual
    (α : EllipticCurveEndomorphism E Ω) :
    ∃! β : EllipticCurveEndomorphism E Ω, IsDual (E := E) (Ω := Ω) α β := by
  sorry






theorem exists_dual
    (α : EllipticCurveEndomorphism E Ω) :
    ∃ β : EllipticCurveEndomorphism E Ω, IsDual (E := E) (Ω := Ω) α β := by
  rcases exists_unique_dual (E := E) (Ω := Ω) α with ⟨β, hβ, _⟩
  exact ⟨β, hβ⟩


noncomputable def dual
    (α : EllipticCurveEndomorphism E Ω) :
    EllipticCurveEndomorphism E Ω :=
  Classical.choose (exists_dual (E := E) (Ω := Ω) α)

theorem dual_spec
    (α : EllipticCurveEndomorphism E Ω) :
    IsDual (E := E) (Ω := Ω) α (dual (E := E) (Ω := Ω) α) :=
  Classical.choose_spec (exists_dual (E := E) (Ω := Ω) α)








def HasTrace
    (α : EllipticCurveEndomorphism E Ω) (t : ℤ) : Prop :=
  α.toEnd + (dual (E := E) (Ω := Ω) α).toEnd =
    t • (1 : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)





theorem exists_unique_trace
    (α : EllipticCurveEndomorphism E Ω) :
    ∃! t : ℤ, HasTrace (E := E) (Ω := Ω) α t := by
  sorry






theorem exists_trace
    (α : EllipticCurveEndomorphism E Ω) :
    ∃ t : ℤ, HasTrace (E := E) (Ω := Ω) α t := by
  rcases exists_unique_trace (E := E) (Ω := Ω) α with ⟨t, ht, _⟩
  exact ⟨t, ht⟩


noncomputable def trace
    (α : EllipticCurveEndomorphism E Ω) : ℤ :=
  Classical.choose (exists_trace (E := E) (Ω := Ω) α)

theorem trace_spec
    (α : EllipticCurveEndomorphism E Ω) :
    HasTrace (E := E) (Ω := Ω) α (trace (E := E) (Ω := Ω) α) :=
  Classical.choose_spec (exists_trace (E := E) (Ω := Ω) α)














theorem theorem_6_18_statement
    (α : EllipticCurveEndomorphism E Ω) :
    (α.toEnd * α.toEnd)
        - ((trace (E := E) (Ω := Ω) α) • α.toEnd)
        + ((degree (E := E) (Ω := Ω) α) •
            (1 : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)) = 0
    ∧
    ((dual (E := E) (Ω := Ω) α).toEnd *
        (dual (E := E) (Ω := Ω) α).toEnd)
        - ((trace (E := E) (Ω := Ω) α) •
            (dual (E := E) (Ω := Ω) α).toEnd)
        + ((degree (E := E) (Ω := Ω) α) •
            (1 : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)) = 0 := by
  sorry

end Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18


end