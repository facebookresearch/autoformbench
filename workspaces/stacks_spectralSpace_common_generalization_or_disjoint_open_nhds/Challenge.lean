import Mathlib

open scoped Topology

theorem spectralSpace_common_generalization_or_disjoint_open_nhds {X : Type*} [TopologicalSpace X] [SpectralSpace X] (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨
      ∃ U V : Set X, IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ y ∈ V ∧ Disjoint U V := by
  sorry
