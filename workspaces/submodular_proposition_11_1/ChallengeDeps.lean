import Mathlib























noncomputable section

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_11_1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







def IsSubmodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι,
    F (A ∪ B) + F (A ∩ B) ≤ F A + F B












def marginalGain (F : Finset ι → ℝ) (A : Finset ι) (i : ι) : ℝ :=
  F (insert i A) - F A











def IsCardinalityGreedyRun
    (F : Finset ι → ℝ) (k : ℕ) (G : ℕ → Finset ι) : Prop :=
  G 0 = ∅ ∧
    ∀ t : ℕ, t < k →
      (((Finset.univ \ G t).Nonempty →
          ∃ i : ι,
            i ∈ Finset.univ \ G t ∧
              (∀ j : ι, j ∈ Finset.univ \ G t →
                marginalGain F (G t) j ≤ marginalGain F (G t) i) ∧
              G (t + 1) = insert i (G t)) ∧
        (¬ (Finset.univ \ G t).Nonempty →
          G (t + 1) = G t))







def cardinalityFeasibleSets (k : ℕ) : Finset (Finset ι) :=
  ((Finset.univ : Finset ι).powerset).filter
    (fun B : Finset ι => B.card ≤ k)




theorem cardinalityFeasibleSets_nonempty
    (k : ℕ) : (cardinalityFeasibleSets (ι := ι) k).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [cardinalityFeasibleSets]






noncomputable def cardinalityConstrainedMaxValue
    (F : Finset ι → ℝ) (k : ℕ) : ℝ := by
  classical
  exact
    ((cardinalityFeasibleSets (ι := ι) k).image F).max'
      ((cardinalityFeasibleSets_nonempty (ι := ι) k).image F)



end Autoform_Learning_with_Submodular_Functions_submodular_proposition_11_1
