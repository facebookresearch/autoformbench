import ChallengeDeps
import Submission.Helpers

open Autoform_Lie_groups_lie_algebras_lie_theorem_25_17

universe u_g u_v u_i

variable {𝔤 : Type u_g} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

namespace Submission

theorem theorem_25_17 [LieAlgebra.IsSemisimple ℂ 𝔤]
    [LieAlgebra.IsKilling ℂ 𝔤]
    [FiniteDimensional ℂ 𝔤]
    (H : LieSubalgebra ℂ 𝔤)
    [H.IsCartanSubalgebra]
    [LieRing.IsNilpotent H]
    [LieModule.IsTriangularizable ℂ H 𝔤]
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    finiteDimensionalHighestWeights H b =
        dominantIntegralWeights (LieAlgebra.IsKilling.rootSystem H) b ∧

      (∀ (V : Type u_v) [AddCommGroup V] [Module ℂ V]
          [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V],
          FiniteDimensional ℂ V →
          LieModule.IsIrreducible ℂ 𝔤 V →
            ∃! χ : Module.Dual ℂ H,
              χ ∈ dominantIntegralWeights
                    (LieAlgebra.IsKilling.rootSystem H) b ∧
                Nonempty (V ≃ₗ⁅ℂ, 𝔤⁆ (L H b χ))) ∧

      (∀ χ : Module.Dual ℂ H,
          χ ∈ dominantIntegralWeights
                (LieAlgebra.IsKilling.rootSystem H) b →
          ∀ μ : Module.Dual ℂ H,
            μ ∈ integralWeights (LieAlgebra.IsKilling.rootSystem H) →
            ∀ w : (LieAlgebra.IsKilling.rootSystem H).weylGroup,
              Module.finrank ℂ
                  (LieModule.weightSpace (L H b χ)
                    (fun h : H => μ h)) =
                Module.finrank ℂ
                  (LieModule.weightSpace (L H b χ)
                    (fun h : H => (w • μ) h))) := by
  sorry

end Submission
