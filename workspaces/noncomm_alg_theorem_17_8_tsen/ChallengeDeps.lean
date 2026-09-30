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
