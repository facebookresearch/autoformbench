import Mathlib




























noncomputable section

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_25_17




attribute [scoped instance 100] LieRing.ofAssociativeRing

universe u_g u_v u_i

variable {𝔤 : Type u_g} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]










def integralWeights
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H) :
    Set (Module.Dual ℂ H) :=
  {χ | ∀ α : ι, ∃ n : ℤ, χ (Φ.coroot α) = (n : ℂ)}











def dominantIntegralWeights
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    (b : Φ.Base) :
    Set (Module.Dual ℂ H) :=
  {χ | χ ∈ integralWeights Φ ∧
    ∀ i : b.support, ∃ n : ℕ, χ (Φ.coroot i.1) = (n : ℂ)}

section Verma

variable [LieAlgebra.IsKilling ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable (H : LieSubalgebra ℂ 𝔤)
variable [H.IsCartanSubalgebra]
variable [LieRing.IsNilpotent H]
variable [LieModule.IsTriangularizable ℂ H 𝔤]














def vermaRelations
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) :
    Submodule (UniversalEnvelopingAlgebra ℂ 𝔤)
      (UniversalEnvelopingAlgebra ℂ 𝔤) :=
  Submodule.span (UniversalEnvelopingAlgebra ℂ 𝔤)
    {u : UniversalEnvelopingAlgebra ℂ 𝔤 |
      (∃ h : H,
        u =
          UniversalEnvelopingAlgebra.ι ℂ (h : 𝔤) -
            algebraMap ℂ (UniversalEnvelopingAlgebra ℂ 𝔤) (χ h)) ∨
      (∃ i : b.support, ∃ x : 𝔤,
        x ∈ LieAlgebra.rootSpace H
          (fun h : H =>
            ((LieAlgebra.IsKilling.rootSystem H).root i.1) h) ∧
        u = UniversalEnvelopingAlgebra.ι ℂ x)}







abbrev VermaModule
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) : Type u_g :=
  UniversalEnvelopingAlgebra ℂ 𝔤 ⧸ vermaRelations H b χ

namespace VermaModule







instance instLieRingModuleUniversalEnveloping
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) :
    LieRingModule (UniversalEnvelopingAlgebra ℂ 𝔤)
      (VermaModule H b χ) :=
  LieRingModule.ofAssociativeModule







instance instLieModuleUniversalEnveloping
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) :
    LieModule ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)
      (VermaModule H b χ) :=
  LieModule.ofAssociativeModule







instance instLieRingModule
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) :
    LieRingModule 𝔤 (VermaModule H b χ) :=
  LieRingModule.compLieHom (R := ℂ)
    (VermaModule H b χ)
    (UniversalEnvelopingAlgebra.ι ℂ :
      𝔤 →ₗ⁅ℂ⁆ UniversalEnvelopingAlgebra ℂ 𝔤)




instance instLieModule
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) :
    LieModule ℂ 𝔤 (VermaModule H b χ) :=
  LieModule.compLieHom (R := ℂ)
    (VermaModule H b χ)
    (UniversalEnvelopingAlgebra.ι ℂ :
      𝔤 →ₗ⁅ℂ⁆ UniversalEnvelopingAlgebra ℂ 𝔤)

end VermaModule










def maximalProperVermaSubmodule
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) :
    LieSubmodule ℂ 𝔤 (VermaModule H b χ) :=
  sSup {N : LieSubmodule ℂ 𝔤 (VermaModule H b χ) | N ≠ ⊤}







abbrev L
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) : Type u_g :=
  VermaModule H b χ ⧸ maximalProperVermaSubmodule H b χ







def finiteDimensionalHighestWeights
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    Set (Module.Dual ℂ H) :=
  {χ | FiniteDimensional ℂ (L H b χ)}

end Verma



end Autoform_Lie_groups_lie_algebras_lie_theorem_25_17

end
