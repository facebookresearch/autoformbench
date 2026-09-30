import ChallengeDeps

open Autoform_Optimizing_with_sparsity_inducing_penalties_sparsity_proposition_1_8
open scoped BigOperators

theorem proposition_1_8 {p : ℕ}
    (H : Set (Fin p → ℝ))
    (hH_compact : IsCompact H)
    (hH_convex : Convex ℝ H)
    (hH_nonnegative :
      ∀ η ∈ H, ∀ i : Fin p, 0 ≤ η i)
    (hH_strictlyPositive :
      ∃ η ∈ H, ∀ i : Fin p, 0 < η i) :
    (∃ N : Seminorm ℝ (Fin p → ℝ),
      (∀ w, N w = hNorm H w) ∧
      (∀ w, N w = 0 ↔ w = 0)) ∧
    ∀ κ : Fin p → ℝ,
      IsGreatest
        (Set.image
          (fun η : Fin p → ℝ =>
            dotProduct η (fun i => (κ i) ^ 2))
          H)
        ((dualNorm (hNorm H) κ) ^ 2) := by
  sorry
