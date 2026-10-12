/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





























open scoped BigOperators

noncomputable section

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_26_4_weyl_character_formula




attribute [scoped instance 100] LieRing.ofAssociativeRing

universe u_g u_v u_i

variable {𝔤 : Type u_g} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]













def integralWeights
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H) :
    Set (Module.Dual ℂ H) :=
  {χ | ∀ α : ι, ∃ n : ℤ, Φ.toLinearMap χ (Φ.coroot α) = (n : ℂ)}











def dominantIntegralWeights
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    (b : Φ.Base) :
    Set (Module.Dual ℂ H) :=
  {χ | χ ∈ integralWeights Φ ∧
    ∀ i : b.support, ∃ n : ℕ,
      Φ.toLinearMap χ (Φ.coroot i.1) = (n : ℂ)}

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










def maximalProperVermaSubmodule
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) :
    LieSubmodule ℂ 𝔤 (VermaModule H b χ) :=
  sSup {N : LieSubmodule ℂ 𝔤 (VermaModule H b χ) | N ≠ ⊤}







abbrev L
    (b : (LieAlgebra.IsKilling.rootSystem H).Base)
    (χ : Module.Dual ℂ H) : Type u_g :=
  VermaModule H b χ ⧸ maximalProperVermaSubmodule H b χ







def integralWeightLattice
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H) :
    AddSubgroup (Module.Dual ℂ H) where
  carrier := integralWeights Φ
  zero_mem' := by
    intro α
    exact ⟨0, by simp⟩
  add_mem' := by
    intro χ ψ hχ hψ α
    rcases hχ α with ⟨m, hm⟩
    rcases hψ α with ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    simp [hm, hn]
  neg_mem' := by
    intro χ hχ α
    rcases hχ α with ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    simp [hm]


abbrev WeightLattice
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H) : Type _ :=
  integralWeightLattice Φ






abbrev FormalCharacter
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H) : Type _ :=
  AddMonoidAlgebra ℤ (WeightLattice Φ)


def expChar
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    {Φ : RootPairing ι ℂ (Module.Dual ℂ H) H}
    (μ : WeightLattice Φ) : FormalCharacter Φ :=
  AddMonoidAlgebra.single μ (1 : ℤ)



open Classical in






def positiveRootIndices
    {ι : Type u_i} [Fintype ι] {H : LieSubalgebra ℂ 𝔤}
    {Φ : RootPairing ι ℂ (Module.Dual ℂ H) H}
    (b : Φ.Base) : Finset ι :=
  Finset.univ.filter (fun i : ι => b.IsPos i)


















end Verma
end Autoform_Lie_groups_lie_algebras_lie_theorem_26_4_weyl_character_formula
end
