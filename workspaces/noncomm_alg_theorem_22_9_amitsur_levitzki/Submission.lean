/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_22_9_amitsur_levitzki
open scoped BigOperators

universe u v

namespace Submission

theorem theorem_22_9_amitsur_levitzki (R : Type u) [CommRing R]
    {n : ℕ} (hn : 0 < n) :
    IsPolynomialIdentityForMatrices R n (2 * n)
      (standardPolynomial R (2 * n)) ∧
    (Nontrivial R →
      ∀ {vars d : ℕ}
        (p : FreeAlgebra R (Fin vars)),
          d < 2 * n →
            IsHomogeneousNoncommutativePolynomial R (Fin vars) d p →
              IsPolynomialIdentityForMatrices R n vars p →
                p = 0) := by
  sorry

end Submission
