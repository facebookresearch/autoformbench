import Mathlib
import Submission

theorem theorem_9_0_1_green_tao :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + d * i) := by
  exact Submission.theorem_9_0_1_green_tao
