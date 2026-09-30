



import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Lie.Free
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Submission.Helpers
import ChallengeDeps

namespace Submission

open _root_.Autoform_Lie_groups_lie_algebras_lie_theorem14_6
noncomputable section

open scoped Manifold

universe u𝕜 uH uE uG

namespace Autoform_Lie_groups_lie_algebras_lie_theorem14_6

variable {𝕜 : Type u𝕜} [RCLike 𝕜]

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}

variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]



namespace OneParameterSubgroup




end OneParameterSubgroup









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
    (existsUnique_oneParameterSubgroup (I := I) (G := G) x)) (1 : 𝕜)







noncomputable def lieExpModel
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (v : E) : G :=
  lieExp (I := I) (G := G) (modelToLieAlg (I := I) (G := G) v)










theorem theorem_7_5_i_local_diffeomorph_at_zero
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E] :
    IsLocalDiffeomorphAt
      (modelWithCornersSelf 𝕜 E)
      I
      ⊤
      (fun v : E =>
        lieExpModel (I := I) (G := G) v)
      (0 : E) := by
  sorry











noncomputable def lieLogModel
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (g : G) : E :=
  ((theorem_7_5_i_local_diffeomorph_at_zero
      (I := I) (G := G)).localInverse.toPartialEquiv.toFun g)















noncomputable def lieLog
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (g : G) : GroupLieAlgebra I G :=
  modelToLieAlg (I := I) (G := G)
    (lieLogModel (I := I) (G := G) g)








noncomputable def lieGroupBCHModel
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (uv : E × E) : E :=
  lieLogModel (I := I) (G := G)
    (lieExpModel (I := I) (G := G) uv.1 *
     lieExpModel (I := I) (G := G) uv.2)







noncomputable def lieGroupBCH
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (xy : GroupLieAlgebra I G × GroupLieAlgebra I G) :
    GroupLieAlgebra I G :=
  modelToLieAlg (I := I) (G := G)
    (lieGroupBCHModel (I := I) (G := G)
      (lieAlgToModel (I := I) (G := G) xy.1,
       lieAlgToModel (I := I) (G := G) xy.2))







noncomputable def bchMuModelCoeff
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (n : ℕ) (x y : GroupLieAlgebra I G) : E :=
  (iteratedFDeriv 𝕜 n
      (fun uv : E × E =>
        lieGroupBCHModel (I := I) (G := G) uv)
      (0 : E × E))
    (fun _ : Fin n =>
      (lieAlgToModel (I := I) (G := G) x,
       lieAlgToModel (I := I) (G := G) y))








noncomputable def bchMuCoeff
    [LieGroup I ⊤ G] [CompleteSpace E] [FiniteDimensional 𝕜 E]
    (n : ℕ) (x y : GroupLieAlgebra I G) :
    GroupLieAlgebra I G :=
  modelToLieAlg (I := I) (G := G)
    (bchMuModelCoeff (I := I) (G := G) n x y)














theorem theorem14_6
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ Pn : UniversalBCHLiePolynomial,
      ∀ {𝕜 : Type u𝕜} [RCLike 𝕜] [CharZero 𝕜]
        [Algebra ℚ 𝕜]
        {H : Type uH} [TopologicalSpace H]
        {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
        {I : ModelWithCorners 𝕜 E H}
        {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
        [LieGroup I ⊤ G] [LieGroup I (minSmoothness 𝕜 3) G]
        [CompleteSpace E] [FiniteDimensional 𝕜 E]
        [LieAlgebra ℚ (GroupLieAlgebra I G)]
        [IsScalarTower ℚ 𝕜 (GroupLieAlgebra I G)]
        (x y : GroupLieAlgebra I G),
          evalUniversalBCHLiePolynomial Pn x y
            =
          bchMuCoeff (𝕜 := 𝕜) (I := I) (G := G) n x y := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_theorem14_6
