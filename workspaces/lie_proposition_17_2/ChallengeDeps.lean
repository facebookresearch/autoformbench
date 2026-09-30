import Mathlib

open scoped TensorProduct

universe u v

namespace Autoform_Lie_groups_lie_algebras_lie_proposition_17_2











abbrev TextSemisimple (𝕜 : Type u) (𝔤 : Type v)
    [CommRing 𝕜] [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] : Prop :=
  LieAlgebra.HasTrivialRadical 𝕜 𝔤



end Autoform_Lie_groups_lie_algebras_lie_proposition_17_2
