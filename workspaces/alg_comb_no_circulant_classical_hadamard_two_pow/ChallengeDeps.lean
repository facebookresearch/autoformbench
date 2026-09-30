import Mathlib

open Matrix

namespace Autoform_Algebraic_Combinatorics_alg_comb_no_circulant_classical_hadamard_two_pow









def IsClassicalHadamard {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j : Fin n, A i j = (1 : ℤ) ∨ A i j = (-1 : ℤ)) ∧
  A * A.transpose = (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)






def HasCirculantClassicalHadamardOrder (n : ℕ) : Prop :=
  ∃ a : Fin n → ℤ,
    IsClassicalHadamard (Matrix.circulant a)



end Autoform_Algebraic_Combinatorics_alg_comb_no_circulant_classical_hadamard_two_pow
