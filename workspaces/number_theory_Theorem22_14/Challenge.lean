/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

open Autoform_Number_Theory_I_number_theory_Theorem22_14
noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem22_14










theorem toNonzeroDivisors_mem
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    (I : Ideal (𝓞 K)) ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  sorry

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


abbrev quotient
    {K : Type*} [Field K] [NumberField K] (C : CongruenceSubgroup K) : Type _ :=
  IdealGroupPrimeToModulus K C.modulus ⧸ C.carrierInPrimeTo


def index
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) [Finite C.quotient] : ℕ :=
  Nat.card C.quotient


def Equivalent
    {K : Type*} [Field K] [NumberField K]
    (C₁ C₂ : CongruenceSubgroup K) : Prop :=
  IdealGroupPrimeToModulus K C₁.modulus ⊓ C₂.carrier =
    IdealGroupPrimeToModulus K C₂.modulus ⊓ C₁.carrier


def IsConductorRepresentative
    {K : Type*} [Field K] [NumberField K]
    (C Cc : CongruenceSubgroup K) : Prop :=
  CongruenceSubgroup.Equivalent C Cc ∧
    ∀ D : CongruenceSubgroup K,
      CongruenceSubgroup.Equivalent C D → Modulus.Dvd Cc.modulus D.modulus

end CongruenceSubgroup


theorem conductorSubgroup_existsUnique
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) :
    ∃! Cc : CongruenceSubgroup K,
      CongruenceSubgroup.IsConductorRepresentative C Cc := by
  sorry

namespace CongruenceSubgroup


def conductorSubgroup
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) : CongruenceSubgroup K :=
  Classical.choose (conductorSubgroup_existsUnique C)


def conductor
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) : Modulus K :=
  C.conductorSubgroup.modulus


def IsPrimitive
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) : Prop :=
  CongruenceSubgroup.IsConductorRepresentative C C

end CongruenceSubgroup


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


def valueOnPrimeTo
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K)
    (I : IdealGroupPrimeToModulus K χ.modulus) : Units ℂ :=
  χ.toUnitHom (QuotientGroup.mk' (RayIdealGroupInPrimeTo K χ.modulus) I)


def evalIdeal
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) (I : IdealGroup K) : ℂ := by
  classical
  exact if hI : I ∈ IdealGroupPrimeToModulus K χ.modulus then
    ((χ.valueOnPrimeTo ⟨I, hI⟩ : Units ℂ) : ℂ)
  else
    0


def IsPrincipal
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Prop :=
  ∀ γ : RayClassGroup K χ.modulus, χ.toUnitHom γ = 1


def primeToMonotone
    {K : Type*} [Field K] [NumberField K]
    {m₁ m₂ : Modulus K}
    (h : Modulus.Dvd m₁ m₂)
    (I : IdealGroupPrimeToModulus K m₂) : IdealGroupPrimeToModulus K m₁ :=
  ⟨I.1, primeToMonotone_mem m₁ m₂ h I⟩

end RayClassCharacter


theorem kernelCongruenceSubgroup_one_mem
    {K : Type*} [Field K] [NumberField K] (χ : RayClassCharacter K) :
    ∃ hI : (1 : IdealGroup K) ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨1, hI⟩ = 1 := by
  sorry


theorem kernelCongruenceSubgroup_mul_mem
    {K : Type*} [Field K] [NumberField K] (χ : RayClassCharacter K)
    (a b : IdealGroup K)
    (ha : ∃ hI : a ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨a, hI⟩ = 1)
    (hb : ∃ hI : b ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨b, hI⟩ = 1) :
    ∃ hI : a * b ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨a * b, hI⟩ = 1 := by
  sorry


theorem kernelCongruenceSubgroup_inv_mem
    {K : Type*} [Field K] [NumberField K] (χ : RayClassCharacter K)
    (x : IdealGroup K)
    (hx : ∃ hI : x ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨x, hI⟩ = 1) :
    ∃ hI : x⁻¹ ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨x⁻¹, hI⟩ = 1 := by
  sorry


theorem kernelCongruenceSubgroup_carrier_le
    {K : Type*} [Field K] [NumberField K] (χ : RayClassCharacter K)
    (I : IdealGroup K)
    (hI : ∃ h : I ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨I, h⟩ = 1) :
    I ∈ IdealGroupPrimeToModulus K χ.modulus := by
  sorry


theorem kernelCongruenceSubgroup_ray_le
    {K : Type*} [Field K] [NumberField K] (χ : RayClassCharacter K)
    (I : IdealGroup K)
    (hI : I ∈ RayIdealGroup K χ.modulus) :
    ∃ h : I ∈ IdealGroupPrimeToModulus K χ.modulus,
      χ.valueOnPrimeTo ⟨I, h⟩ = 1 := by
  sorry

namespace RayClassCharacter


def kernelCongruenceSubgroup
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : CongruenceSubgroup K where
  modulus := χ.modulus
  carrier :=
    { carrier := {I | ∃ hI : I ∈ IdealGroupPrimeToModulus K χ.modulus,
        χ.valueOnPrimeTo ⟨I, hI⟩ = 1}
      one_mem' := kernelCongruenceSubgroup_one_mem χ
      mul_mem' := fun {a b} ha hb => kernelCongruenceSubgroup_mul_mem χ a b ha hb
      inv_mem' := fun {x} hx => kernelCongruenceSubgroup_inv_mem χ x hx }
  carrier_le := fun {I} hI => kernelCongruenceSubgroup_carrier_le χ I hI
  ray_le := fun {I} hI => kernelCongruenceSubgroup_ray_le χ I hI


def conductor
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Modulus K :=
  (χ.kernelCongruenceSubgroup).conductor


def Induces
    {K : Type*} [Field K] [NumberField K]
    (χ₁ χ₂ : RayClassCharacter K) : Prop :=
  ∃ hmod : Modulus.Dvd χ₁.modulus χ₂.modulus,
    ∀ I : IdealGroupPrimeToModulus K χ₂.modulus,
      χ₁.valueOnPrimeTo (primeToMonotone hmod I) = χ₂.valueOnPrimeTo I


def Equivalent
    {K : Type*} [Field K] [NumberField K]
    (χ₁ χ₂ : RayClassCharacter K) : Prop :=
  χ₁.Induces χ₂ ∧ χ₂.Induces χ₁


def IsPrimitive
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : Prop :=
  ∀ ψ : RayClassCharacter K, ψ.Induces χ → ψ.Equivalent χ


def IsUniquePrimitiveInducingCharacter
    {K : Type*} [Field K] [NumberField K]
    (χ χprim : RayClassCharacter K) : Prop :=
  χprim.IsPrimitive ∧ χprim.Induces χ ∧
    ∀ ψ : RayClassCharacter K,
      ψ.IsPrimitive → ψ.Induces χ → ψ.Equivalent χprim

end RayClassCharacter








theorem Theorem22_14
    (K : Type*) [Field K] [NumberField K] :
    (∀ χ : RayClassCharacter K,
      χ.IsPrimitive ↔ CongruenceSubgroup.IsPrimitive χ.kernelCongruenceSubgroup) ∧
    ∀ χ : RayClassCharacter K,
      ∃ χprim : RayClassCharacter K,
        RayClassCharacter.IsUniquePrimitiveInducingCharacter χ χprim := by
  sorry

end Autoform_Number_Theory_I_number_theory_Theorem22_14

end
