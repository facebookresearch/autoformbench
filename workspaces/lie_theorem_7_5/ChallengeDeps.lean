import Mathlib

noncomputable section

open scoped Manifold

universe u𝕜 uH uE uG uH' uF uK

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_7_5

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}

variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]






noncomputable def modelToLieAlg
    (I : ModelWithCorners 𝕜 E H)
    (G : Type uG) [TopologicalSpace G] [ChartedSpace H G] [Group G]
    (v : E) : GroupLieAlgebra I G := by
  unfold GroupLieAlgebra
  unfold TangentSpace
  exact v







structure OneParameterSubgroup
    (I : ModelWithCorners 𝕜 E H)
    (G : Type uG) [TopologicalSpace G] [ChartedSpace H G] [Group G] where
  toFun : 𝕜 → G
  map_zero : toFun 0 = 1
  map_add : ∀ s t : 𝕜, toFun (s + t) = toFun s * toFun t
  contMDiff_toFun :
    ContMDiff (modelWithCornersSelf 𝕜 𝕜) I ⊤ toFun

namespace OneParameterSubgroup

instance :
    CoeFun (OneParameterSubgroup I G) (fun _ => 𝕜 → G) where
  coe γ := γ.toFun


noncomputable def tangentOneAtZero :
    TangentSpace (modelWithCornersSelf 𝕜 𝕜) (0 : 𝕜) := by
  unfold TangentSpace
  exact (1 : 𝕜)








noncomputable def velocityAtZero (γ : OneParameterSubgroup I G) :
    GroupLieAlgebra I G :=
  (mfderiv (modelWithCornersSelf 𝕜 𝕜) I
    (fun t : 𝕜 => γ t) (0 : 𝕜))
    (tangentOneAtZero (𝕜 := 𝕜))

end OneParameterSubgroup





structure LieGroupHom
    (I : ModelWithCorners 𝕜 E H)
    {H' : Type uH'} [TopologicalSpace H']
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (J : ModelWithCorners 𝕜 F H')
    (G : Type uG) [TopologicalSpace G] [ChartedSpace H G] [Group G]
    (K : Type uK) [TopologicalSpace K] [ChartedSpace H' K] [Group K] where
  toMonoidHom : G →* K
  contMDiff_toFun :
    ContMDiff I J ⊤ (fun g : G => toMonoidHom g)

namespace LieGroupHom

variable {H' : Type uH'} [TopologicalSpace H']
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {J : ModelWithCorners 𝕜 F H'}
variable {K : Type uK} [TopologicalSpace K] [ChartedSpace H' K] [Group K]

instance :
    CoeFun (LieGroupHom I J G K) (fun _ => G → K) where
  coe φ := fun g => φ.toMonoidHom g








noncomputable def lieMap (φ : LieGroupHom I J G K) :
    GroupLieAlgebra I G →L[𝕜] GroupLieAlgebra J K :=
  mfderiv I J (fun g : G => φ g) (1 : G)

end LieGroupHom






noncomputable def adjointMap (g : G) :
    GroupLieAlgebra I G →L[𝕜] GroupLieAlgebra I G :=
  mfderiv I I (fun h : G => g * h * g⁻¹) (1 : G)






