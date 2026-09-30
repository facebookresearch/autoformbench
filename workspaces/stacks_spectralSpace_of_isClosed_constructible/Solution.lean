import Mathlib
import Submission

open scoped Topology

theorem spectralSpace_of_isClosed_constructible {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) :
    SpectralSpace E := by
  exact Submission.spectralSpace_of_isClosed_constructible hE
