/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.FiniteLength
import Submission
import ChallengeDeps




















universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt







attribute [instance] FiniteDirectSumDecomposition.finite
attribute [instance] FiniteDirectSumDecomposition.summandAddCommGroup
attribute [instance] FiniteDirectSumDecomposition.summandModule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]






theorem theorem_4_17_exists
    (hM : IsFiniteLength R M) :
    Nonempty (FiniteDirectSumDecomposition R M) := Submission.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt.theorem_4_17_exists hM









theorem theorem_4_17_unique
    (hM : IsFiniteLength R M)
    (D E : FiniteDirectSumDecomposition R M) :
    ∃ σ : D.ι ≃ E.ι,
      ∀ i : D.ι, Nonempty (D.summand i ≃ₗ[R] E.summand (σ i)) := Submission.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt.theorem_4_17_unique hM D E




theorem theorem_4_17_krull_schmidt
    (hM : IsFiniteLength R M) :
    Nonempty (FiniteDirectSumDecomposition R M) ∧
      ∀ D E : FiniteDirectSumDecomposition R M,
        ∃ σ : D.ι ≃ E.ι,
          ∀ i : D.ι, Nonempty (D.summand i ≃ₗ[R] E.summand (σ i)) := Submission.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt.theorem_4_17_krull_schmidt hM

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt
