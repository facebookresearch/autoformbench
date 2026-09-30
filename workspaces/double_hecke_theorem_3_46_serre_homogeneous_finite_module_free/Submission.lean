/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_46_serre_homogeneous_finite_module_free
open scoped BigOperators

universe u

namespace Submission

theorem theorem_3_46_serre_homogeneous_finite_module_free (n : ℕ)
    (f : Fin n → PolyRing n)
    (hfhom : ∀ i : Fin n, IsHomogeneousPolynomial (f i))
    (hfinite :
      IsFinitelyGeneratedOverSubalgebra
        (polynomialSubalgebraGeneratedBy f)) :
    IsFreeOverSubalgebra
      (polynomialSubalgebraGeneratedBy f) := by
  sorry

end Submission
