


import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Submission.Helpers
import ChallengeDeps


open _root_.Autoform_Number_Theory_I_number_theory_Proposition22_19
noncomputable section

open scoped BigOperators NumberField Topology
open Filter

namespace Autoform_Number_Theory_I_number_theory_Proposition22_19



































theorem mem_nonZeroDivisors_of_nonzeroIntegralIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    I.1 ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  sorry







def toNonzeroDivisors
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    nonZeroDivisors (Ideal (𝓞 K)) :=
  ⟨I.1, mem_nonZeroDivisors_of_nonzeroIntegralIdeal K I⟩


def fractionalIdealOfNonzeroIntegralIdeal
    {K : Type*} [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) : FracIdeal K :=
  FractionalIdeal.mk0 K (toNonzeroDivisors I)

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

theorem idealGroupPrimeToModulus_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    InIdealGroupPrimeToModulus m (1 : IdealGroup K) := by
  sorry


theorem idealGroupPrimeToModulus_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I J : IdealGroup K)
    (hI : InIdealGroupPrimeToModulus m I)
    (hJ : InIdealGroupPrimeToModulus m J) :
    InIdealGroupPrimeToModulus m (I * J) := by
  sorry


theorem idealGroupPrimeToModulus_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I : IdealGroup K)
    (hI : InIdealGroupPrimeToModulus m I) :
    InIdealGroupPrimeToModulus m I⁻¹ := by
  sorry










def IdealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | InIdealGroupPrimeToModulus m I}
  one_mem' := idealGroupPrimeToModulus_one_mem K m
  mul_mem' := fun {I J} hI hJ => idealGroupPrimeToModulus_mul_mem K m I J hI hJ
  inv_mem' := fun {I} hI => idealGroupPrimeToModulus_inv_mem K m I hI

theorem rayIdealGroup_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ (1 : IdealGroup K) = PrincipalIdealOfUnit x := by
  sorry


theorem rayIdealGroup_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I J : IdealGroup K)
    (hI : ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x)
    (hJ : ∃ x : Kˣ, InKPowModulusOne m x ∧ J = PrincipalIdealOfUnit x) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ I * J = PrincipalIdealOfUnit x := by
  sorry


theorem rayIdealGroup_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I : IdealGroup K)
    (hI : ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ I⁻¹ = PrincipalIdealOfUnit x := by
  sorry





def RayIdealGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x}
  one_mem' := rayIdealGroup_one_mem K m
  mul_mem' := fun {I J} hI hJ => rayIdealGroup_mul_mem K m I J hI hJ
  inv_mem' := fun {I} hI => rayIdealGroup_inv_mem K m I hI

theorem subgroupRestrict_one_mem
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J) :
    ((1 : J) : G) ∈ H := by
  sorry


theorem subgroupRestrict_mul_mem
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J)
    (a b : J) (ha : (a : G) ∈ H) (hb : (b : G) ∈ H) :
    ((a * b : J) : G) ∈ H := by
  sorry


theorem subgroupRestrict_inv_mem
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J)
    (a : J) (ha : (a : G) ∈ H) :
    ((a⁻¹ : J) : G) ∈ H := by
  sorry





def subgroupRestrict
    {G : Type*} [Group G] (H J : Subgroup G) (_h : H ≤ J) : Subgroup J where
  carrier := {x : J | (x : G) ∈ H}
  one_mem' := subgroupRestrict_one_mem G H J _h
  mul_mem' := fun {a b} ha hb => subgroupRestrict_mul_mem G H J _h a b ha hb
  inv_mem' := fun {a} ha => subgroupRestrict_inv_mem G H J _h a ha

theorem rayIdealGroup_le_idealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    RayIdealGroup K m ≤ IdealGroupPrimeToModulus K m := by
  sorry







namespace RayClassCharacter

















end RayClassCharacter



def RayIdealGroupInPrimeTo
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroupPrimeToModulus K m) :=
  subgroupRestrict
    (RayIdealGroup K m)
    (IdealGroupPrimeToModulus K m)
    (rayIdealGroup_le_idealGroupPrimeToModulus K m)


abbrev RayClassGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :=
  IdealGroupPrimeToModulus K m ⧸ RayIdealGroupInPrimeTo K m


structure RayClassCharacter
    (K : Type*) [Field K] [NumberField K] where
  modulus : Modulus K
  toUnitHom : RayClassGroup K modulus →* Units ℂ
  finiteRange : (Set.range toUnitHom).Finite
  unitary_values :
    ∀ γ : RayClassGroup K modulus,
      ‖((toUnitHom γ : Units ℂ) : ℂ)‖ = 1

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

def WeberLSeriesTerm
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) (I : NonzeroIntegralIdeal K) (s : ℂ) : ℂ :=
  χ.evalIntegralIdeal I *
    Complex.exp (-s * Complex.ofReal (Real.log (Ideal.absNorm I.1 : ℝ)))
end RayClassCharacter

namespace RayClassCharacter

def WeberLFunction
    {K : Type*} [Field K] [NumberField K]
    (χ : RayClassCharacter K) : ℂ → ℂ :=
  fun s => ∑' I : NonzeroIntegralIdeal K, WeberLSeriesTerm χ I s
end RayClassCharacter







theorem Proposition22_19
    (K : Type*) [Field K] [NumberField K]
    (χ : RayClassCharacter K) :
    ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → F s = RayClassCharacter.WeberLFunction χ s) ∧
        MeromorphicOn F (RayClassCharacter.weberContinuationDomain K) ∧
          (∀ z : ℂ,
            z ∈ RayClassCharacter.weberContinuationDomain K → z ≠ 1 →
              AnalyticAt ℂ F z) ∧
            RayClassCharacter.AtMostSimplePoleAt F 1 ∧
              (¬ χ.IsPrincipal → AnalyticAt ℂ F 1) := by
  sorry

end Autoform_Number_Theory_I_number_theory_Proposition22_19


end