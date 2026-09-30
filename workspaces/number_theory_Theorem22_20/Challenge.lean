/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs

open Autoform_Number_Theory_I_number_theory_Theorem22_20
noncomputable section

open scoped BigOperators NumberField Topology
open Filter

namespace Autoform_Number_Theory_I_number_theory_Theorem22_20















namespace Modulus



end Modulus





theorem toNonzeroDivisors_mem
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    (I : Ideal (𝓞 K)) ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  sorry

namespace NonzeroIntegralIdeal



end NonzeroIntegralIdeal




namespace NonzeroIntegralIdeal

def toNonzeroDivisors
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    nonZeroDivisors (Ideal (𝓞 K)) :=
  ⟨I.1, toNonzeroDivisors_mem I⟩
end NonzeroIntegralIdeal


def fractionalIdealOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : FracIdeal K :=
  FractionalIdeal.mk0 K I.toNonzeroDivisors

theorem fractionalIdealOfNonzeroIntegralIdeal_isUnit
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    IsUnit (fractionalIdealOfNonzeroIntegralIdeal I) := by
  sorry













def idealGroupElementOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : IdealGroup K :=
  Classical.choose (fractionalIdealOfNonzeroIntegralIdeal_isUnit I)


def InIdealGroupPrimeToModulus
    {K : Type*} [Field K] [NumberField K]
    (m : Modulus K) (I : IdealGroup K) : Prop :=
  ∃ a b : NonzeroIntegralIdeal K,
    IsCoprime a.1 m.finitePart.1 ∧
      IsCoprime b.1 m.finitePart.1 ∧
        I = idealGroupElementOfNonzeroIntegralIdeal a *
              (idealGroupElementOfNonzeroIntegralIdeal b)⁻¹

theorem IdealGroupPrimeToModulus_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    InIdealGroupPrimeToModulus m (1 : IdealGroup K) := by
  sorry


theorem IdealGroupPrimeToModulus_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) (a b : IdealGroup K)
    (ha : InIdealGroupPrimeToModulus m a) (hb : InIdealGroupPrimeToModulus m b) :
    InIdealGroupPrimeToModulus m (a * b) := by
  sorry


theorem IdealGroupPrimeToModulus_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) (x : IdealGroup K)
    (hx : InIdealGroupPrimeToModulus m x) :
    InIdealGroupPrimeToModulus m x⁻¹ := by
  sorry





def IdealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | InIdealGroupPrimeToModulus m I}
  one_mem' := IdealGroupPrimeToModulus_one_mem K m
  mul_mem' := fun {a b} ha hb => IdealGroupPrimeToModulus_mul_mem K m a b ha hb
  inv_mem' := fun {x} hx => IdealGroupPrimeToModulus_inv_mem K m x hx

theorem subgroupRestrict_one_mem
    {G : Type*} [Group G] (H J : Subgroup G) (h : H ≤ J) :
    ((1 : J) : G) ∈ H := by
  sorry


theorem subgroupRestrict_mul_mem
    {G : Type*} [Group G] (H J : Subgroup G) (h : H ≤ J) (a b : J)
    (ha : (a : G) ∈ H) (hb : (b : G) ∈ H) :
    ((a * b : J) : G) ∈ H := by
  sorry


theorem subgroupRestrict_inv_mem
    {G : Type*} [Group G] (H J : Subgroup G) (h : H ≤ J) (x : J)
    (hx : (x : G) ∈ H) :
    ((x⁻¹ : J) : G) ∈ H := by
  sorry





def subgroupRestrict
    {G : Type*} [Group G] (H J : Subgroup G) (_h : H ≤ J) : Subgroup J where
  carrier := {x : J | (x : G) ∈ H}
  one_mem' := subgroupRestrict_one_mem H J _h
  mul_mem' := fun {a b} ha hb => subgroupRestrict_mul_mem H J _h a b ha hb
  inv_mem' := fun {x} hx => subgroupRestrict_inv_mem H J _h x hx

theorem RayIdealGroup_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ (1 : IdealGroup K) = PrincipalIdealOfUnit x := by
  sorry


theorem RayIdealGroup_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) (a b : IdealGroup K)
    (ha : ∃ x : Kˣ, InKPowModulusOne m x ∧ a = PrincipalIdealOfUnit x)
    (hb : ∃ x : Kˣ, InKPowModulusOne m x ∧ b = PrincipalIdealOfUnit x) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ a * b = PrincipalIdealOfUnit x := by
  sorry


theorem RayIdealGroup_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) (y : IdealGroup K)
    (hy : ∃ x : Kˣ, InKPowModulusOne m x ∧ y = PrincipalIdealOfUnit x) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ y⁻¹ = PrincipalIdealOfUnit x := by
  sorry





def RayIdealGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x}
  one_mem' := RayIdealGroup_one_mem K m
  mul_mem' := fun {a b} ha hb => RayIdealGroup_mul_mem K m a b ha hb
  inv_mem' := fun {x} hx => RayIdealGroup_inv_mem K m x hx

theorem RayIdealGroup_le_IdealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    RayIdealGroup K m ≤ IdealGroupPrimeToModulus K m := by
  sorry







namespace CongruenceSubgroup







end CongruenceSubgroup



def RayIdealGroupInPrimeTo
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroupPrimeToModulus K m) :=
  subgroupRestrict (RayIdealGroup K m) (IdealGroupPrimeToModulus K m)
    (RayIdealGroup_le_IdealGroupPrimeToModulus K m)


abbrev RayClassGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :=
  IdealGroupPrimeToModulus K m ⧸ RayIdealGroupInPrimeTo K m


structure CongruenceSubgroup
    (K : Type*) [Field K] [NumberField K] where
  modulus : Modulus K
  carrier : Subgroup (IdealGroup K)
  carrier_le : carrier ≤ IdealGroupPrimeToModulus K modulus
  ray_le : RayIdealGroup K modulus ≤ carrier

namespace CongruenceSubgroup

def carrierInPrimeTo
    {K : Type*} [Field K] [NumberField K] (C : CongruenceSubgroup K) :
    Subgroup (IdealGroupPrimeToModulus K C.modulus) :=
  subgroupRestrict C.carrier (IdealGroupPrimeToModulus K C.modulus) C.carrier_le
end CongruenceSubgroup

namespace CongruenceSubgroup

abbrev quotient
    {K : Type*} [Field K] [NumberField K] (C : CongruenceSubgroup K) : Type _ :=
  IdealGroupPrimeToModulus K C.modulus ⧸ C.carrierInPrimeTo
end CongruenceSubgroup

namespace CongruenceSubgroup

def index
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) [Finite C.quotient] : ℕ :=
  Nat.card C.quotient
end CongruenceSubgroup

structure CongruenceSubgroupCharacter
    {K : Type*} [Field K] [NumberField K] (C : CongruenceSubgroup K) where
  toUnitHom : C.quotient →* Units ℂ
  finiteRange : (Set.range toUnitHom).Finite
  unitary_values :
    ∀ γ : C.quotient, ‖((toUnitHom γ : Units ℂ) : ℂ)‖ = 1


theorem rayClassToCongruenceQuotient_existsUnique
    {K : Type*} [Field K] [NumberField K] (C : CongruenceSubgroup K) :
    ∃! f : RayClassGroup K C.modulus →* C.quotient,
      ∀ I : IdealGroupPrimeToModulus K C.modulus,
        f (QuotientGroup.mk' (RayIdealGroupInPrimeTo K C.modulus) I) =
          QuotientGroup.mk' C.carrierInPrimeTo I := by
  sorry


def rayClassToCongruenceQuotient
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) : RayClassGroup K C.modulus →* C.quotient :=
  Classical.choose (rayClassToCongruenceQuotient_existsUnique C)





structure RayClassCharacter
    (K : Type*) [Field K] [NumberField K] where
  modulus : Modulus K
  toUnitHom : RayClassGroup K modulus →* Units ℂ
  finiteRange : (Set.range toUnitHom).Finite
  unitary_values :
    ∀ γ : RayClassGroup K modulus,
      ‖((toUnitHom γ : Units ℂ) : ℂ)‖ = 1

theorem primeToMonotone_mem
    {K : Type*} [Field K] [NumberField K]
    (m₁ m₂ : Modulus K)
    (h : Modulus.Dvd m₁ m₂)
    (I : IdealGroupPrimeToModulus K m₂) :
    (I : IdealGroup K) ∈ IdealGroupPrimeToModulus K m₁ := by
  sorry

namespace RayClassCharacter







































end RayClassCharacter












namespace RayClassCharacter

def valueOnPrimeTo
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K)
    (I : IdealGroupPrimeToModulus K χ.modulus) : Units ℂ :=
  χ.toUnitHom (QuotientGroup.mk' (RayIdealGroupInPrimeTo K χ.modulus) I)
end RayClassCharacter

namespace RayClassCharacter

def evalIdeal
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) (I : IdealGroup K) : ℂ := by
  classical
  exact if hI : I ∈ IdealGroupPrimeToModulus K χ.modulus then
    ((χ.valueOnPrimeTo ⟨I, hI⟩ : Units ℂ) : ℂ)
  else
    0
end RayClassCharacter

namespace RayClassCharacter

def evalIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) (I : NonzeroIntegralIdeal K) : ℂ :=
  χ.evalIdeal (idealGroupElementOfNonzeroIntegralIdeal I)
end RayClassCharacter

namespace RayClassCharacter

def IsPrincipal
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Prop :=
  ∀ γ : RayClassGroup K χ.modulus, χ.toUnitHom γ = 1
end RayClassCharacter

namespace RayClassCharacter

def primeToMonotone
    {K : Type*} [Field K] [NumberField K]
    {m₁ m₂ : Modulus K}
    (h : Modulus.Dvd m₁ m₂)
    (I : IdealGroupPrimeToModulus K m₂) : IdealGroupPrimeToModulus K m₁ :=
  ⟨I.1, primeToMonotone_mem m₁ m₂ h I⟩
end RayClassCharacter

namespace RayClassCharacter

def Induces
    {K : Type*} [Field K] [NumberField K]
    (χ₁ χ₂ : RayClassCharacter K) : Prop :=
  ∃ hmod : Modulus.Dvd χ₁.modulus χ₂.modulus,
    ∀ I : IdealGroupPrimeToModulus K χ₂.modulus,
      χ₁.valueOnPrimeTo (primeToMonotone hmod I) = χ₂.valueOnPrimeTo I
end RayClassCharacter

namespace RayClassCharacter

def Equivalent
    {K : Type*} [Field K] [NumberField K]
    (χ₁ χ₂ : RayClassCharacter K) : Prop :=
  χ₁.Induces χ₂ ∧ χ₂.Induces χ₁
end RayClassCharacter

namespace RayClassCharacter

def IsPrimitive
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Prop :=
  ∀ ψ : RayClassCharacter K, ψ.Induces χ → ψ.Equivalent χ
end RayClassCharacter

namespace RayClassCharacter

def KernelContainsCongruenceSubgroup
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) (χ : RayClassCharacter K) : Prop :=
  ∃ hmod : Modulus.Dvd χ.modulus C.modulus,
    ∀ I : IdealGroupPrimeToModulus K C.modulus,
      (I : IdealGroup K) ∈ C.carrier →
        χ.valueOnPrimeTo (primeToMonotone hmod I) = 1
end RayClassCharacter

namespace RayClassCharacter

def PrimitiveCharactersContaining
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) : Set (RayClassCharacter K) :=
  {χ | χ.IsPrimitive ∧ KernelContainsCongruenceSubgroup C χ}
end RayClassCharacter

namespace RayClassCharacter

def WeberLSeriesTerm
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) (I : NonzeroIntegralIdeal K) (s : ℂ) : ℂ :=
  χ.evalIntegralIdeal I *
    Complex.exp (-s * Complex.ofReal (Real.log (Ideal.absNorm I.1 : ℝ)))
end RayClassCharacter

namespace RayClassCharacter

def WeberLFunctionConverges
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Prop :=
  ∀ s : ℂ, 1 < s.re → Summable fun I : NonzeroIntegralIdeal K => WeberLSeriesTerm χ I s
end RayClassCharacter

namespace RayClassCharacter

def WeberLFunction
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : ℂ → ℂ :=
  fun s => ∑' I : NonzeroIntegralIdeal K, WeberLSeriesTerm χ I s
end RayClassCharacter

namespace RayClassCharacter

def IsWeberLContinuation
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) (F : ℂ → ℂ) : Prop :=
  WeberLFunctionConverges χ ∧
    (∀ s : ℂ, 1 < s.re → F s = WeberLFunction χ s) ∧
      MeromorphicOn F (classNumberStrip K) ∧
        (∀ z : ℂ, z ∈ classNumberStrip K → z ≠ 1 → AnalyticAt ℂ F z) ∧
          AtMostSimplePoleAt F 1 ∧
            (¬ χ.IsPrincipal → AnalyticAt ℂ F 1)
end RayClassCharacter

namespace RayClassCharacter

def WeberLValueAtOne
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) (z : ℂ) : Prop :=
  ∃ F : ℂ → ℂ,
    IsWeberLContinuation χ F ∧ AnalyticAt ℂ F 1 ∧ F 1 = z
end RayClassCharacter

namespace RayClassCharacter

def WeberLNonzeroAtOne
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Prop :=
  ∃ z : ℂ, WeberLValueAtOne χ z ∧ z ≠ 0
end RayClassCharacter

namespace RayClassCharacter

def WeberLZeroAtOne
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Prop :=
  WeberLValueAtOne χ 0
end RayClassCharacter


def PrimesInCongruenceSubgroup
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) : Set (PrimeOfNumberField K) :=
  {P | ∃ hP : idealGroupElementOfNonzeroIntegralIdeal (primeToNonzeroIntegralIdeal P) ∈
        IdealGroupPrimeToModulus K C.modulus,
      idealGroupElementOfNonzeroIntegralIdeal (primeToNonzeroIntegralIdeal P) ∈ C.carrier}







theorem Theorem22_20
    (K : Type*) [Field K] [NumberField K]
    (C : CongruenceSubgroup K) [Finite C.quotient] :
    ((∀ χ : RayClassCharacter K,
      χ ∈ RayClassCharacter.PrimitiveCharactersContaining C →
        ¬ χ.IsPrincipal → RayClassCharacter.WeberLNonzeroAtOne χ) →
      HasDirichletDensity (PrimesInCongruenceSubgroup C)
        ((1 : ℝ) / (C.index : ℝ))) ∧
    ((∃ χ : RayClassCharacter K,
      χ ∈ RayClassCharacter.PrimitiveCharactersContaining C ∧
        ¬ χ.IsPrincipal ∧ RayClassCharacter.WeberLZeroAtOne χ) →
      HasDirichletDensity (PrimesInCongruenceSubgroup C) 0) := by
  sorry

end Autoform_Number_Theory_I_number_theory_Theorem22_20

end
