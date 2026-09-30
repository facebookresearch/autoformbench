import Mathlib

noncomputable section

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_8_8_lieHom_exists_agrees_derivative

universe uκ uHG uHK uEG uEK uG uK

variable {𝕜 : Type uκ} [RCLike 𝕜]

variable {HG : Type uHG} [TopologicalSpace HG]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable (IG : ModelWithCorners 𝕜 EG HG)

variable {HK : Type uHK} [TopologicalSpace HK]
variable {EK : Type uEK} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK]
variable (IK : ModelWithCorners 𝕜 EK HK)

variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {K : Type uK} [Group K] [TopologicalSpace K] [ChartedSpace HK K]







noncomputable def lieGroupHomDerivative (φ : G →* K) :
    GroupLieAlgebra IG G →L[𝕜] GroupLieAlgebra IK K :=
  mfderiv IG IK (φ : G → K) (1 : G)



end Autoform_Lie_groups_lie_algebras_lie_theorem_8_8_lieHom_exists_agrees_derivative
