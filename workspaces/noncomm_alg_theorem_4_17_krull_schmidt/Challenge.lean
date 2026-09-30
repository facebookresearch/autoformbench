import ChallengeDeps




import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.FiniteLength




















universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt







attribute [instance] FiniteDirectSumDecomposition.finite
attribute [instance] FiniteDirectSumDecomposition.summandAddCommGroup
attribute [instance] FiniteDirectSumDecomposition.summandModule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]






theorem theorem_4_17_exists
    (hM : IsFiniteLength R M) :
    Nonempty (FiniteDirectSumDecomposition R M) := by
  sorry









theorem theorem_4_17_unique
    (hM : IsFiniteLength R M)
    (D E : FiniteDirectSumDecomposition R M) :
    ∃ σ : D.ι ≃ E.ι,
      ∀ i : D.ι, Nonempty (D.summand i ≃ₗ[R] E.summand (σ i)) := by
  sorry




theorem theorem_4_17_krull_schmidt
    (hM : IsFiniteLength R M) :
    Nonempty (FiniteDirectSumDecomposition R M) ∧
      ∀ D E : FiniteDirectSumDecomposition R M,
        ∃ σ : D.ι ≃ E.ι,
          ∀ i : D.ι, Nonempty (D.summand i ≃ₗ[R] E.summand (σ i)) := by
  sorry

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_4_17_krull_schmidt
