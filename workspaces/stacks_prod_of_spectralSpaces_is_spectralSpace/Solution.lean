import Mathlib
import Submission

open scoped Topology

theorem prod_of_spectralSpaces_is_spectralSpace (X Y : Type*)
  [TopologicalSpace X] [SpectralSpace X]
  [TopologicalSpace Y] [SpectralSpace Y] :
    SpectralSpace (X × Y) := by
  exact Submission.prod_of_spectralSpaces_is_spectralSpace X Y
