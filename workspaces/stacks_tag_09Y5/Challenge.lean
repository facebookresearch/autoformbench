import ChallengeDeps

open Autoform_Stacks_Project_stacks_tag_09Y5

universe u

variable {X : Type u} [TopologicalSpace X]

theorem tag_09Y5 [TopologicalSpace.NoetherianSpace X] {P : Set (Set X)} :
    IsFinitePartition P →
      ∃ S : Set (Set X),
        IsFiniteGoodStratification S ∧ Refines S P := by
  sorry
