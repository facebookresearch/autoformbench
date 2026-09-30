import Mathlib

universe u

namespace Autoform_Stacks_Project_stacks_tag_09Y5


variable {X : Type u} [TopologicalSpace X]

def IsFinitePartition (P : Set (Set X)) : Prop :=
  P.Finite ∧
    (∀ U ∈ P, U.Nonempty ∧ IsLocallyClosed U) ∧
    (∀ U ∈ P, ∀ V ∈ P, U ≠ V → Disjoint U V) ∧
    ⋃₀ P = Set.univ

def Refines (finer coarser : Set (Set X)) : Prop :=
  ∀ V ∈ coarser, ∃ A : Set (Set X), A ⊆ finer ∧ V = ⋃₀ A

def IsFiniteGoodStratification (S : Set (Set X)) : Prop :=
  IsFinitePartition S ∧
    ∀ U ∈ S, ∀ V ∈ S,
      (U ∩ closure V).Nonempty → U ⊆ closure V



end Autoform_Stacks_Project_stacks_tag_09Y5
