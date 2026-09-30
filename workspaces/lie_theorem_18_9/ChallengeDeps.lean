import Mathlib

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_18_9

universe u v w











def CompletelyReducibleLieModule
    (k : Type u) (L : Type v) (V : Type w)
    [Field k]
    [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V]
    [LieRingModule L V] [LieModule k L V] : Prop :=
  ∃ (ι : Type*) (_ : Fintype ι) (W : ι → LieSubmodule k L V),
    (∀ i : ι, LieModule.IsIrreducible k L (W i)) ∧
    iSupIndep W ∧
    (⨆ i : ι, W i) = ⊤



end Autoform_Lie_groups_lie_algebras_lie_theorem_18_9
