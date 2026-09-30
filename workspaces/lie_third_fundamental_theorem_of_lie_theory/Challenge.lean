import ChallengeDeps

open Autoform_Lie_groups_lie_algebras_lie_third_fundamental_theorem_of_lie_theory
open scoped Manifold

universe u v w

theorem third_fundamental_theorem_of_lie_theory (𝕜 : Type u) [RCLike 𝕜]
    (L : Type v)
    [LieRing L] [LieAlgebra 𝕜 L]
    [FiniteDimensional 𝕜 L] :
    ∃ G : BundledFiniteDimensionalLieGroup 𝕜,
      Nonempty (G.LieAlg ≃ₗ⁅𝕜⁆ L) := by
  sorry
