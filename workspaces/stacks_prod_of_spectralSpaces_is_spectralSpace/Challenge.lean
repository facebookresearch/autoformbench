import Mathlib

open scoped Topology

theorem prod_of_spectralSpaces_is_spectralSpace (X Y : Type*)
  [TopologicalSpace X] [SpectralSpace X]
  [TopologicalSpace Y] [SpectralSpace Y] :
    SpectralSpace (X × Y) := by
  sorry
