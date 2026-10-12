/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/





import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Submission.Helpers
import ChallengeDeps






























open _root_.Autoform_Lie_groups_lie_algebras_lie_theorem_26_4_weyl_character_formula
open scoped BigOperators

noncomputable section

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_26_4_weyl_character_formula




attribute [scoped instance 100] LieRing.ofAssociativeRing

universe u_g u_v u_i

variable {𝔤 : Type u_g} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]





section Verma

variable [LieAlgebra.IsKilling ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable (H : LieSubalgebra ℂ 𝔤)
variable [H.IsCartanSubalgebra]
variable [LieRing.IsNilpotent H]
variable [LieModule.IsTriangularizable ℂ H 𝔤]

















def finiteDimensionalHighestWeights
    (b : (LieAlgebra.IsKilling.rootSystem H).Base) :
    Set (Module.Dual ℂ H) :=
  {χ | FiniteDimensional ℂ (L H b χ)}

end Verma

















theorem rootAsIntegralWeight_mem
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    [Φ.IsCrystallographic]
    (α : ι) : Φ.root α ∈ integralWeights Φ := by
  intro β
  refine ⟨Φ.pairingIn ℤ α β, ?_⟩
  simpa [RootPairing.root_coroot_eq_pairing] using
    (Φ.algebraMap_pairingIn ℤ α β).symm



open Classical in












def rootAsIntegralWeight
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    [Φ.IsCrystallographic]
    (α : ι) : WeightLattice Φ :=
  ⟨Φ.root α, rootAsIntegralWeight_mem Φ α⟩

open Classical in








structure WeylCharacterContext
    {ι : Type u_i} [Fintype ι] {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    [Φ.IsCrystallographic] where
  base : Φ.Base
  rho : WeightLattice Φ
  rho_spec :
    (2 : ℤ) • rho =
      ∑ i ∈ positiveRootIndices (Φ := Φ) base, rootAsIntegralWeight Φ i





theorem weylActionOnIntegralWeight_mem
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    (w : Φ.weylGroup) (μ : WeightLattice Φ) :
    w • (μ : Module.Dual ℂ H) ∈ integralWeights Φ := by
  intro α
  rcases μ.property ((w : Φ.Aut).indexEquiv.symm α) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  change Φ.toLinearMap ((w : Φ.Aut).toHom.weightMap (μ : Module.Dual ℂ H))
      (Φ.coroot α) = (n : ℂ)
  rw [← hn]
  have h := LinearMap.congr_fun
    (RootPairing.Hom.weight_coweight_transpose_apply
      Φ Φ (Φ.coroot α) (w : Φ.Aut).toHom)
    (μ : Module.Dual ℂ H)
  simpa [RootPairing.Hom.coroot_coweightMap_apply] using h



open Classical in















def weylActionOnIntegralWeight
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    (w : Φ.weylGroup) (μ : WeightLattice Φ) : WeightLattice Φ :=
  ⟨w • (μ : Module.Dual ℂ H), weylActionOnIntegralWeight_mem Φ w μ⟩

open Classical in








def weylLength
    {ι : Type u_i} [Fintype ι] {H : LieSubalgebra ℂ 𝔤}
    {Φ : RootPairing ι ℂ (Module.Dual ℂ H) H}
    [Φ.IsCrystallographic]
    (C : WeylCharacterContext Φ) (w : Φ.weylGroup) : ℕ :=
  ((positiveRootIndices (Φ := Φ) C.base).filter
    (fun i : ι => ¬ C.base.IsPos ((Φ.weylGroupToPerm w) i))).card






def weylSign
    {ι : Type u_i} [Fintype ι] {H : LieSubalgebra ℂ 𝔤}
    {Φ : RootPairing ι ℂ (Module.Dual ℂ H) H}
    [Φ.IsCrystallographic]
    (C : WeylCharacterContext Φ) (w : Φ.weylGroup) : ℤ :=
  (-1 : ℤ) ^ weylLength C w









def weylDenominator
    {ι : Type u_i} [Fintype ι] {H : LieSubalgebra ℂ 𝔤}
    {Φ : RootPairing ι ℂ (Module.Dual ℂ H) H}
    [Φ.IsCrystallographic]
    (C : WeylCharacterContext Φ) : FormalCharacter Φ :=
  expChar C.rho *
    ∏ i ∈ positiveRootIndices (Φ := Φ) C.base,
      (1 - expChar (-(rootAsIntegralWeight Φ i)))





def weylNumerator
    {ι : Type u_i} [Fintype ι] {H : LieSubalgebra ℂ 𝔤}
    {Φ : RootPairing ι ℂ (Module.Dual ℂ H) H}
    [Φ.IsCrystallographic]
    [Fintype Φ.weylGroup]
    (C : WeylCharacterContext Φ) (Χ : WeightLattice Φ) : FormalCharacter Φ :=
  ∑ w : Φ.weylGroup,
    AddMonoidAlgebra.single
      (weylActionOnIntegralWeight Φ w (Χ + C.rho))
      (weylSign C w)








theorem existsFiniteIntegralWeightSupport
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    (V : Type u_v) [AddCommGroup V] [Module ℂ V]
    [LieRingModule H V] [LieModule ℂ H V]
    [FiniteDimensional ℂ V] :
    ∃ S : Finset (WeightLattice Φ),
      ∀ μ : WeightLattice Φ,
        LieModule.weightSpace V
            (fun h : H => (μ : Module.Dual ℂ H) h) ≠ ⊥ →
          μ ∈ S := by
  sorry












def finiteIntegralWeightSupport
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    (V : Type u_v) [AddCommGroup V] [Module ℂ V]
    [LieRingModule H V] [LieModule ℂ H V]
    [FiniteDimensional ℂ V] : Finset (WeightLattice Φ) :=
  Classical.choose (existsFiniteIntegralWeightSupport Φ V)






def formalCharacterOfFiniteDimensionalModule
    {ι : Type u_i} {H : LieSubalgebra ℂ 𝔤}
    (Φ : RootPairing ι ℂ (Module.Dual ℂ H) H)
    (V : Type u_v) [AddCommGroup V] [Module ℂ V]
    [LieRingModule H V] [LieModule ℂ H V]
    [FiniteDimensional ℂ V] : FormalCharacter Φ :=
  ∑ μ ∈ finiteIntegralWeightSupport Φ V,
    AddMonoidAlgebra.single μ
      ((Module.finrank ℂ
        (LieModule.weightSpace V
          (fun h : H => (μ : Module.Dual ℂ H) h)) : ℕ) : ℤ)






theorem LCharacterOfDominant_finiteDimensional
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    [LieAlgebra.IsKilling ℂ 𝔤]
    [FiniteDimensional ℂ 𝔤]
    (H : LieSubalgebra ℂ 𝔤)
    [H.IsCartanSubalgebra]
    [LieRing.IsNilpotent H]
    [LieModule.IsTriangularizable ℂ H 𝔤]
    (C : WeylCharacterContext (LieAlgebra.IsKilling.rootSystem H))
    (χ : WeightLattice (LieAlgebra.IsKilling.rootSystem H))
    (hχ :
      (χ : Module.Dual ℂ H) ∈
        dominantIntegralWeights (LieAlgebra.IsKilling.rootSystem H) C.base) :
    FiniteDimensional ℂ (L H C.base (χ : Module.Dual ℂ H)) := by
  sorry











def LCharacterOfDominant
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    [LieAlgebra.IsKilling ℂ 𝔤]
    [FiniteDimensional ℂ 𝔤]
    (H : LieSubalgebra ℂ 𝔤)
    [H.IsCartanSubalgebra]
    [LieRing.IsNilpotent H]
    [LieModule.IsTriangularizable ℂ H 𝔤]
    (C : WeylCharacterContext (LieAlgebra.IsKilling.rootSystem H))
    (χ : WeightLattice (LieAlgebra.IsKilling.rootSystem H))
    (hχ :
      (χ : Module.Dual ℂ H) ∈
        dominantIntegralWeights (LieAlgebra.IsKilling.rootSystem H) C.base) :
    FormalCharacter (LieAlgebra.IsKilling.rootSystem H) := by
  classical
  letI : FiniteDimensional ℂ (L H C.base (χ : Module.Dual ℂ H)) :=
    LCharacterOfDominant_finiteDimensional H C χ hχ
  exact formalCharacterOfFiniteDimensionalModule
    (LieAlgebra.IsKilling.rootSystem H)
    (L H C.base (χ : Module.Dual ℂ H))









theorem theorem_26_4_weyl_character_formula
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    [LieAlgebra.IsKilling ℂ 𝔤]
    [FiniteDimensional ℂ 𝔤]
    (H : LieSubalgebra ℂ 𝔤)
    [H.IsCartanSubalgebra]
    [LieRing.IsNilpotent H]
    [LieModule.IsTriangularizable ℂ H 𝔤]
    (C : WeylCharacterContext (LieAlgebra.IsKilling.rootSystem H))
    [Fintype (LieAlgebra.IsKilling.rootSystem H).weylGroup]
    (χ : WeightLattice (LieAlgebra.IsKilling.rootSystem H))
    (hχ :
      (χ : Module.Dual ℂ H) ∈
        dominantIntegralWeights (LieAlgebra.IsKilling.rootSystem H) C.base) :
    weylDenominator C * LCharacterOfDominant H C χ hχ =
      weylNumerator C χ := by
  sorry

end Autoform_Lie_groups_lie_algebras_lie_theorem_26_4_weyl_character_formula


end
