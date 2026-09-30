/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.QExpansion
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Elliptic_Curves_elliptic_eichlerShimuraCarayol
noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Autoform_Elliptic_Curves_elliptic_eichlerShimuraCarayol






theorem exists_gamma0FundamentalRegion (N : ℕ) [NeZero N] :
    ∃ F : Set UpperHalfPlane, IsFundamentalRegion (gamma0Real N) F := by
  sorry


noncomputable def gamma0FundamentalRegion (N : ℕ) [NeZero N] :
    Set UpperHalfPlane :=
  Classical.choose (exists_gamma0FundamentalRegion N)




theorem gamma0FundamentalRegion_spec (N : ℕ) [NeZero N] :
    IsFundamentalRegion (gamma0Real N) (gamma0FundamentalRegion N) :=
  Classical.choose_spec (exists_gamma0FundamentalRegion N)









noncomputable def peterssonInnerProduct (N : ℕ) [NeZero N]
    (f g : UpperHalfPlane → ℂ) : ℂ :=
  ∫ τ in gamma0FundamentalRegion N,
    UpperHalfPlane.petersson (2 : ℤ) g f τ










def IsNewAtLevel (N : ℕ) [NeZero N]
    (f : CuspForm (gamma0Real N) (2 : ℤ)) : Prop :=
  ∀ M : ℕ, M ∣ N → M < N →
    ∀ g : CuspForm (gamma0Real M) (2 : ℤ),
      peterssonInnerProduct N
        ⇑f
        ⇑g = 0











structure WeightTwoNewform (N : ℕ) [NeZero N] where
  toCuspForm : CuspForm (gamma0Real N) (2 : ℤ)
  normalized :
    (PowerSeries.coeff 1)
      (UpperHalfPlane.qExpansion 1
        ⇑toCuspForm) = 1
  heckeEigen :
    let F := UpperHalfPlane.qExpansion 1
      ⇑toCuspForm
    ∀ n : ℕ, 0 < n →
      heckeQExpansion N n F = ((PowerSeries.coeff n) F) • F
  newAtLevel : IsNewAtLevel N toCuspForm





























theorem eichlerShimuraCarayol
    (N : ℕ) [NeZero N]
    (f : WeightTwoNewform N)
    (hf_int : HasIntegralQExpansion f.toCuspForm) :
    ∃ E : WeierstrassCurve ℚ,
      E.IsElliptic ∧
      HasConductor E N ∧
      ∀ n : ℕ, 0 < n →
        ((E.LFunction n : ℤ) : ℂ) =
          (PowerSeries.coeff n)
            (UpperHalfPlane.qExpansion 1
              ⇑f.toCuspForm) := by
  sorry

end Autoform_Elliptic_Curves_elliptic_eichlerShimuraCarayol

