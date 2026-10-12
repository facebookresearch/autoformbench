/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Group.End
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.AlgebraicClosure
import Submission.Helpers
import ChallengeDeps






























open _root_.Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18_shortcurve
noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18_shortcurve

universe u v

variable {K : Type u} [Field K]



instance shortWeierstrass_isShortNF (A B : K) :
    (shortWeierstrass A B).IsShortNF where
  a₁ := rfl
  a₂ := rfl
  a₃ := rfl


abbrev ShortCurve (A B : K) : WeierstrassCurve.Affine K :=
  shortWeierstrass A B







namespace StandardAffineMap

variable (F : StandardAffineMap K)












def yScaleOver {Ω : Type v} [Field Ω] [Algebra K Ω] (x : Ω) : Ω :=
  (F.baseChange Ω).yScale x









end StandardAffineMap







namespace Coords3
















def infinity : Coords3 K :=
  (0, 1, 0)

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















variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
variable {A B : K}
variable [hE : (GeometricShortCurve (K := K) Ω A B).IsElliptic]





attribute [coe] ShortWeierstrassEndomorphism.toEnd














theorem standard_form_degree_unique
    (φ : AddMonoid.End (GeometricShortCurve (K := K) Ω A B).Point)
    (D₁ D₂ : StandardEndomorphismData (Ω := Ω) (A := A) (B := B) φ) :
    D₁.F.degree = D₂.F.degree := by
  sorry










theorem integer_scalar_endomorphisms_injective :
    Function.Injective
      (fun t : ℤ =>
        t • (1 : AddMonoid.End (GeometricShortCurve (K := K) Ω A B).Point)) := by
  sorry













def IsDual
    (α β : ShortWeierstrassEndomorphism A B Ω) : Prop :=
  (α.toEnd = 0 ∧ β.toEnd = 0) ∨
  (α.toEnd ≠ 0 ∧
    β.toEnd * α.toEnd =
      (degree (A := A) (B := B) (Ω := Ω) α) •
        (1 : AddMonoid.End (GeometricShortCurve (K := K) Ω A B).Point))






theorem exists_unique_dual
    (α : ShortWeierstrassEndomorphism A B Ω) :
    ∃! β : ShortWeierstrassEndomorphism A B Ω, IsDual (A := A) (B := B) (Ω := Ω) α β := by
  sorry






theorem exists_dual
    (α : ShortWeierstrassEndomorphism A B Ω) :
    ∃ β : ShortWeierstrassEndomorphism A B Ω, IsDual (A := A) (B := B) (Ω := Ω) α β := by
  rcases exists_unique_dual (A := A) (B := B) (Ω := Ω) α with ⟨β, hβ, _⟩
  exact ⟨β, hβ⟩


noncomputable def dual
    (α : ShortWeierstrassEndomorphism A B Ω) :
    ShortWeierstrassEndomorphism A B Ω :=
  Classical.choose (exists_dual (A := A) (B := B) (Ω := Ω) α)

theorem dual_spec
    (α : ShortWeierstrassEndomorphism A B Ω) :
    IsDual (A := A) (B := B) (Ω := Ω) α (dual (A := A) (B := B) (Ω := Ω) α) :=
  Classical.choose_spec (exists_dual (A := A) (B := B) (Ω := Ω) α)










def HasTrace
    (α : ShortWeierstrassEndomorphism A B Ω) (t : ℤ) : Prop :=
  α.toEnd + (dual (A := A) (B := B) (Ω := Ω) α).toEnd =
    t • (1 : AddMonoid.End (GeometricShortCurve (K := K) Ω A B).Point)







theorem exists_unique_trace
    (α : ShortWeierstrassEndomorphism A B Ω) :
    ∃! t : ℤ, HasTrace (A := A) (B := B) (Ω := Ω) α t := by
  sorry






theorem exists_trace
    (α : ShortWeierstrassEndomorphism A B Ω) :
    ∃ t : ℤ, HasTrace (A := A) (B := B) (Ω := Ω) α t := by
  rcases exists_unique_trace (A := A) (B := B) (Ω := Ω) α with ⟨t, ht, _⟩
  exact ⟨t, ht⟩






noncomputable def trace
    (α : ShortWeierstrassEndomorphism A B Ω) : ℤ :=
  Classical.choose (exists_trace (A := A) (B := B) (Ω := Ω) α)

theorem trace_spec
    (α : ShortWeierstrassEndomorphism A B Ω) :
    HasTrace (A := A) (B := B) (Ω := Ω) α (trace (A := A) (B := B) (Ω := Ω) α) :=
  Classical.choose_spec (exists_trace (A := A) (B := B) (Ω := Ω) α)














theorem theorem_6_18_statement
    (α : ShortWeierstrassEndomorphism A B Ω) :
    (α.toEnd * α.toEnd)
        - ((trace (A := A) (B := B) (Ω := Ω) α) • α.toEnd)
        + ((degree (A := A) (B := B) (Ω := Ω) α) •
            (1 : AddMonoid.End (GeometricShortCurve (K := K) Ω A B).Point)) = 0
    ∧
    ((dual (A := A) (B := B) (Ω := Ω) α).toEnd *
        (dual (A := A) (B := B) (Ω := Ω) α).toEnd)
        - ((trace (A := A) (B := B) (Ω := Ω) α) •
            (dual (A := A) (B := B) (Ω := Ω) α).toEnd)
        + ((degree (A := A) (B := B) (Ω := Ω) α) •
            (1 : AddMonoid.End (GeometricShortCurve (K := K) Ω A B).Point)) = 0 := by
  sorry

end Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18_shortcurve


end