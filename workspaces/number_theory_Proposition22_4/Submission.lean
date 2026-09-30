


import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Number_Theory_I_number_theory_Proposition22_4
noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Proposition22_4





















abbrev NonzeroIntegralIdeal (K : Type*) [Field K] [NumberField K] :=
  {I : Ideal (𝓞 K) // I ≠ ⊥}


structure Modulus (K : Type*) [Field K] [NumberField K] where
  finitePart : NonzeroIntegralIdeal K
  infinitePart : Finset (RealInfinitePlace K)

theorem mem_nonZeroDivisors_of_nonzeroIntegralIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    (I : Ideal (𝓞 K)) ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  sorry







def NonzeroIntegralIdeal.toNonzeroDivisors
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    nonZeroDivisors (Ideal (𝓞 K)) :=
  ⟨I.1, mem_nonZeroDivisors_of_nonzeroIntegralIdeal K I⟩


def fractionalIdealOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : FracIdeal K :=
  FractionalIdeal.mk0 K I.toNonzeroDivisors

theorem isUnit_fractionalIdealOfNonzeroIntegralIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    IsUnit (fractionalIdealOfNonzeroIntegralIdeal I) := by
  sorry








def idealGroupElementOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : IdealGroup K :=
  Classical.choose (isUnit_fractionalIdealOfNonzeroIntegralIdeal K I)


def InIdealGroupPrimeToModulus
    {K : Type*} [Field K] [NumberField K]
    (m : Modulus K) (I : IdealGroup K) : Prop :=
  ∃ a b : NonzeroIntegralIdeal K,
    IsCoprime a.1 m.finitePart.1 ∧
      IsCoprime b.1 m.finitePart.1 ∧
        I = idealGroupElementOfNonzeroIntegralIdeal a *
              (idealGroupElementOfNonzeroIntegralIdeal b)⁻¹

theorem one_mem_idealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    InIdealGroupPrimeToModulus m (1 : IdealGroup K) := by
  sorry


theorem mul_mem_idealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (a b : IdealGroup K) :
    InIdealGroupPrimeToModulus m a → InIdealGroupPrimeToModulus m b →
      InIdealGroupPrimeToModulus m (a * b) := by
  sorry


theorem inv_mem_idealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (x : IdealGroup K) :
    InIdealGroupPrimeToModulus m x → InIdealGroupPrimeToModulus m x⁻¹ := by
  sorry










def IdealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | InIdealGroupPrimeToModulus m I}
  one_mem' := one_mem_idealGroupPrimeToModulus K m
  mul_mem' := fun {a b} ha hb => mul_mem_idealGroupPrimeToModulus K m a b ha hb
  inv_mem' := fun {x} hx => inv_mem_idealGroupPrimeToModulus K m x hx


def InKPowModulus
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) (x : Kˣ) : Prop :=
  ∃ a b : 𝓞 K,
    a ≠ 0 ∧ b ≠ 0 ∧
      IsCoprime (Ideal.span ({a} : Set (𝓞 K))) m.finitePart.1 ∧
        IsCoprime (Ideal.span ({b} : Set (𝓞 K))) m.finitePart.1 ∧
          ((a : 𝓞 K) : K) = (x : K) * (b : K)


def InKPowModulusOneBookValuation
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) (x : Kˣ) : Prop :=
  InKPowModulus m x ∧
    (∀ a b : 𝓞 K,
      a ≠ 0 → b ≠ 0 →
        IsCoprime (Ideal.span ({a} : Set (𝓞 K))) m.finitePart.1 →
          IsCoprime (Ideal.span ({b} : Set (𝓞 K))) m.finitePart.1 →
            ((a : 𝓞 K) : K) = (x : K) * (b : K) →
              a - b ∈ m.finitePart.1) ∧
      ∀ w ∈ m.infinitePart, 0 < NumberField.InfinitePlace.embedding_of_isReal w.2 x


abbrev InKPowModulusOne
    {K : Type*} [Field K] [NumberField K] (m : Modulus K) (x : Kˣ) : Prop :=
  InKPowModulusOneBookValuation m x

theorem one_mem_rayIdealGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ (1 : IdealGroup K) = PrincipalIdealOfUnit x := by
  sorry


theorem mul_mem_rayIdealGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (a b : IdealGroup K) :
    (∃ x : Kˣ, InKPowModulusOne m x ∧ a = PrincipalIdealOfUnit x) →
      (∃ x : Kˣ, InKPowModulusOne m x ∧ b = PrincipalIdealOfUnit x) →
        ∃ x : Kˣ, InKPowModulusOne m x ∧ a * b = PrincipalIdealOfUnit x := by
  sorry


theorem inv_mem_rayIdealGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (y : IdealGroup K) :
    (∃ x : Kˣ, InKPowModulusOne m x ∧ y = PrincipalIdealOfUnit x) →
      ∃ x : Kˣ, InKPowModulusOne m x ∧ y⁻¹ = PrincipalIdealOfUnit x := by
  sorry





def RayIdealGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x}
  one_mem' := one_mem_rayIdealGroup K m
  mul_mem' := fun {a b} ha hb => mul_mem_rayIdealGroup K m a b ha hb
  inv_mem' := fun {x} hx => inv_mem_rayIdealGroup K m x hx

theorem one_mem_subgroupRestrict
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J) :
    ((1 : J) : G) ∈ H := by
  sorry


theorem mul_mem_subgroupRestrict
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J) (a b : J) :
    (a : G) ∈ H → (b : G) ∈ H → ((a * b : J) : G) ∈ H := by
  sorry


theorem inv_mem_subgroupRestrict
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J) (x : J) :
    (x : G) ∈ H → ((x⁻¹ : J) : G) ∈ H := by
  sorry

















def subgroupRestrict
    {G : Type*} [Group G] (H J : Subgroup G) (_h : H ≤ J) :
    Subgroup J where
  carrier := {x : J | (x : G) ∈ H}
  one_mem' := one_mem_subgroupRestrict G H J _h
  mul_mem' := fun {a b} ha hb => mul_mem_subgroupRestrict G H J _h a b ha hb
  inv_mem' := fun {x} hx => inv_mem_subgroupRestrict G H J _h x hx


structure CongruenceSubgroup
    (K : Type*) [Field K] [NumberField K] where
  modulus : Modulus K
  carrier : Subgroup (IdealGroup K)
  carrier_le : carrier ≤ IdealGroupPrimeToModulus K modulus
  ray_le : RayIdealGroup K modulus ≤ carrier


def CongruenceSubgroup.carrierInPrimeTo
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) :
    Subgroup (IdealGroupPrimeToModulus K C.modulus) :=
  subgroupRestrict C.carrier (IdealGroupPrimeToModulus K C.modulus) C.carrier_le


abbrev CongruenceSubgroup.quotient
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) : Type _ :=
  IdealGroupPrimeToModulus K C.modulus ⧸ C.carrierInPrimeTo


def CongruenceSubgroup.Equivalent
    {K : Type*} [Field K] [NumberField K]
    (C₁ C₂ : CongruenceSubgroup K) : Prop :=
  IdealGroupPrimeToModulus K C₁.modulus ⊓ C₂.carrier =
    IdealGroupPrimeToModulus K C₂.modulus ⊓ C₁.carrier


def CongruenceSubgroup.classOf
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K)
    (I : IdealGroup K) (hI : I ∈ IdealGroupPrimeToModulus K C.modulus) :
    C.quotient :=
  QuotientGroup.mk' C.carrierInPrimeTo ⟨I, hI⟩


def PreservesCommonIdealCosets
    {K : Type*} [Field K] [NumberField K]
    {C₁ C₂ : CongruenceSubgroup K}
    (e : C₁.quotient ≃* C₂.quotient) : Prop :=
  ∀ I : IdealGroup K,
    ∀ h₁ : I ∈ IdealGroupPrimeToModulus K C₁.modulus,
      ∀ h₂ : I ∈ IdealGroupPrimeToModulus K C₂.modulus,
        e (C₁.classOf I h₁) = C₂.classOf I h₂







theorem Proposition22_4
    (K : Type*) [Field K] [NumberField K] :
    Equivalence
        (fun C₁ C₂ : CongruenceSubgroup K =>
          CongruenceSubgroup.Equivalent C₁ C₂) ∧
      ∀ C₁ C₂ : CongruenceSubgroup K,
        CongruenceSubgroup.Equivalent C₁ C₂ →
          ∃! e : C₁.quotient ≃* C₂.quotient,
            PreservesCommonIdealCosets e := by
  sorry

end Autoform_Number_Theory_I_number_theory_Proposition22_4


end