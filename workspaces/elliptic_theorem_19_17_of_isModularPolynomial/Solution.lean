/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Ideal.Basic
import Submission
import ChallengeDeps




















noncomputable section

open scoped UpperHalfPlane

namespace Autoform_Elliptic_Curves_elliptic_theorem_19_17_of_isModularPolynomial























theorem exists_isModularPolynomial
    (N : ℕ) (hN : 0 < N) :
    ∃ Φ : Polynomial (Polynomial ℂ), IsModularPolynomial N hN Φ := Submission.Autoform_Elliptic_Curves_elliptic_theorem_19_17_of_isModularPolynomial.exists_isModularPolynomial N hN




def modularPolynomial (N : ℕ) (hN : 0 < N) :
    Polynomial (Polynomial ℂ) :=
  Classical.choose (exists_isModularPolynomial N hN)




theorem modularPolynomial_spec (N : ℕ) (hN : 0 < N) :
    IsModularPolynomial N hN (modularPolynomial N hN) :=
  Classical.choose_spec (exists_isModularPolynomial N hN)















theorem theorem_19_17_of_isModularPolynomial
    {N : ℕ} (hN : 0 < N)
    {Φ : Polynomial (Polynomial ℂ)}
    (hΦ : IsModularPolynomial N hN Φ) :
    HasIntegerCoefficients Φ := Submission.Autoform_Elliptic_Curves_elliptic_theorem_19_17_of_isModularPolynomial.theorem_19_17_of_isModularPolynomial hN hΦ

end Autoform_Elliptic_Curves_elliptic_theorem_19_17_of_isModularPolynomial

end
