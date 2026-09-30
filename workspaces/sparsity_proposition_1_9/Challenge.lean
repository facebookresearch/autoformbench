import ChallengeDeps

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_9
open scoped BigOperators

theorem proposition_1_9 {p : ℕ} (Ω : Seminorm ℝ (Vec p))
    (hΩ_definite : ∀ w : Vec p, Ω w = 0 → w = 0) :
    IsSubquadratic Ω ↔ IsHNorm Ω := by
  sorry
