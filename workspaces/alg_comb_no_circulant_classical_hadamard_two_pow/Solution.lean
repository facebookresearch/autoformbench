import ChallengeDeps
import Submission

open Autoform_Algebraic_Combinatorics_alg_comb_no_circulant_classical_hadamard_two_pow
open Matrix

theorem no_circulant_classical_hadamard_two_pow {k : ℕ} (hk : 3 ≤ k) :
    ¬ HasCirculantClassicalHadamardOrder (2 ^ k) := by
  exact Submission.no_circulant_classical_hadamard_two_pow hk
