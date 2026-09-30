import ChallengeDeps
import Submission

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_B_3
open scoped BigOperators

theorem proposition_B_3 {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : Finset (α ⊕ β) → ℝ)
    (hG_sub : IsSubmodular G)
    (hG_empty : G ∅ = 0) :
    let F : Finset α → ℝ := partialMinimum (α := α) (β := β) G
    IsSubmodular F ∧
      F ∅ = 0 ∧
      (subsetMinimum
          (fun B : Finset β => G (sumSubset (∅ : Finset α) B)) = 0 →
        ((∀ w : α → ℝ,
            (∀ i : α, 0 ≤ w i) →
              IsLeast
                ((fun v : β → ℝ =>
                    lovaszExtension G (Sum.elim w v)) ''
                  {v : β → ℝ | ∀ j : β, 0 ≤ v j})
                (lovaszExtension F w)) ∧
          (submodularPolyhedron F =
            {s : α → ℝ | ∃ t : β → ℝ,
              (∀ j : β, 0 ≤ t j) ∧
              Sum.elim s t ∈ submodularPolyhedron G}))) := by
  exact Submission.proposition_B_3 G hG_sub hG_empty
