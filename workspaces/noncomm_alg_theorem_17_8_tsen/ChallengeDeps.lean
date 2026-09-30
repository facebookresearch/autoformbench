/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


















universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_8_tsen










def IsC1Field (K : Type u) [Field K] : Prop :=
  ∀ {n d : ℕ},
    0 < d →
      d < n →
        ∀ P : MvPolynomial (Fin n) K,
          MvPolynomial.IsHomogeneous P d →
            ∃ x : Fin n → K,
              x ≠ 0 ∧ MvPolynomial.eval x P = 0



end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_8_tsen
