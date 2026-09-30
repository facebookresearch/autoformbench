



import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Lie_groups_lie_algebras_lie_theorem_7_5
noncomputable section

open scoped Manifold

universe u𝕜 uH uE uG uH' uF uK

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_7_5

variable {𝕜 : Type u𝕜} [RCLike 𝕜]

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}

variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]



namespace OneParameterSubgroup



@[simp]
theorem map_zero_apply (γ : OneParameterSubgroup I G) :
    γ (0 : 𝕜) = (1 : G) :=
  γ.map_zero

@[simp]
theorem map_add_apply (γ : OneParameterSubgroup I G) (s t : 𝕜) :
    γ (s + t) = γ s * γ t :=
  γ.map_add s t


end OneParameterSubgroup



namespace LieGroupHom

variable {H' : Type uH'} [TopologicalSpace H']
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {J : ModelWithCorners 𝕜 F H'}
variable {K : Type uK} [TopologicalSpace K] [ChartedSpace H' K] [Group K]



@[simp]
theorem map_one (φ : LieGroupHom I J G K) :
    φ (1 : G) = (1 : K) :=
  φ.toMonoidHom.map_one

@[simp]
theorem map_mul (φ : LieGroupHom I J G K) (a b : G) :
    φ (a * b) = φ a * φ b :=
  φ.toMonoidHom.map_mul a b



end LieGroupHom










theorem existsUnique_oneParameterSubgroup
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (x : GroupLieAlgebra I G) :
    ∃! γ : OneParameterSubgroup I G,
      γ.velocityAtZero = x := by
  sorry






noncomputable def lieExp
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (x : GroupLieAlgebra I G) : G :=
  (Classical.choose
    (existsUnique_oneParameterSubgroup x)) (1 : 𝕜)







noncomputable def lieExpModel
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (v : E) : G :=
  lieExp (modelToLieAlg (I := I) (G := G) v)





noncomputable def expDerivAtZeroModel
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E] :
    TangentSpace (modelWithCornersSelf 𝕜 E) (0 : E) →L[𝕜]
      TangentSpace I (lieExpModel (I := I) (G := G) (0 : E)) := by
  unfold TangentSpace
  exact ContinuousLinearMap.id 𝕜 E



















structure Theorem75Statement
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E] :
    Prop where

  regular :
    ContMDiff
      (modelWithCornersSelf 𝕜 E)
      I
      ⊤
      (fun v : E =>
        lieExpModel (I := I) (G := G) v)

  local_diffeomorph_at_zero :
    IsLocalDiffeomorphAt
      (modelWithCornersSelf 𝕜 E)
      I
      ⊤
      (fun v : E =>
        lieExpModel (I := I) (G := G) v)
      (0 : E)

  exp_zero :
    lieExp (0 : GroupLieAlgebra I G) = (1 : G)

  exp_zero_model :
    lieExpModel (I := I) (G := G) (0 : E) = (1 : G)

  exp_deriv_zero :
    (mfderiv
      (modelWithCornersSelf 𝕜 E)
      I
      (fun v : E =>
        lieExpModel (I := I) (G := G) v)
      (0 : E))
      =
    expDerivAtZeroModel

  add_parameter :
    ∀ (x : GroupLieAlgebra I G) (s t : 𝕜),
      lieExp ((s + t) • x)
        =
      lieExp (s • x) *
      lieExp (t • x)

  naturality :
    ∀ {H' : Type uH'} [TopologicalSpace H']
      {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
      {J : ModelWithCorners 𝕜 F H'}
      {K : Type uK} [TopologicalSpace K] [ChartedSpace H' K] [Group K]
      [LieGroup J ⊤ K] [CompleteSpace F] [FiniteDimensional 𝕜 F]
      (φ : LieGroupHom I J G K) (x : GroupLieAlgebra I G),
        φ (lieExp x)
          =
        lieExp (I := J) (G := K) (φ.lieMap x)

  adjoint :
    ∀ (g : G) (x : GroupLieAlgebra I G),
      g * (lieExp x) * g⁻¹
        =
      lieExp (adjointMap g x)








theorem theorem_7_5
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E] :
    Theorem75Statement (I := I) (G := G) := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_theorem_7_5

