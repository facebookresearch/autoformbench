


import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Submission
import ChallengeDeps

open Autoform_Number_Theory_I_number_theory_Theorem21_8
noncomputable section

open scoped NumberField

namespace Autoform_Number_Theory_I_number_theory_Theorem21_8



















def ModulusDvd
    {K : Type*} [Field K] [NumberField K] (m₁ m₂ : Modulus K) : Prop :=
  m₁.finitePart.1 ∣ m₂.finitePart.1 ∧
    ∀ w ∈ m₁.infinitePart, w ∈ m₂.infinitePart







theorem mem_nonZeroDivisors_of_nonzeroIntegralIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : NonzeroIntegralIdeal K) :
    I.1 ∈ nonZeroDivisors (Ideal (𝓞 K)) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.mem_nonZeroDivisors_of_nonzeroIntegralIdeal <;> assumption







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
    IsUnit (fractionalIdealOfNonzeroIntegralIdeal I) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.isUnit_fractionalIdealOfNonzeroIntegralIdeal <;> assumption











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
    InIdealGroupPrimeToModulus m (1 : IdealGroup K) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.idealGroupPrimeToModulus_one_mem <;> assumption




theorem idealGroupPrimeToModulus_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I J : IdealGroup K)
    (hI : InIdealGroupPrimeToModulus m I)
    (hJ : InIdealGroupPrimeToModulus m J) :
    InIdealGroupPrimeToModulus m (I * J) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.idealGroupPrimeToModulus_mul_mem <;> assumption




theorem idealGroupPrimeToModulus_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I : IdealGroup K)
    (hI : InIdealGroupPrimeToModulus m I) :
    InIdealGroupPrimeToModulus m I⁻¹ := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.idealGroupPrimeToModulus_inv_mem <;> assumption





def IdealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | InIdealGroupPrimeToModulus m I}
  one_mem' := idealGroupPrimeToModulus_one_mem K m
  mul_mem' := fun {I J} hI hJ => idealGroupPrimeToModulus_mul_mem K m I J hI hJ
  inv_mem' := fun {I} hI => idealGroupPrimeToModulus_inv_mem K m I hI



theorem subgroupRestrict_one_mem
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J) :
    ((1 : J) : G) ∈ H := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.subgroupRestrict_one_mem <;> assumption




theorem subgroupRestrict_mul_mem
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J)
    (a b : J) (ha : (a : G) ∈ H) (hb : (b : G) ∈ H) :
    ((a * b : J) : G) ∈ H := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.subgroupRestrict_mul_mem <;> assumption




theorem subgroupRestrict_inv_mem
    (G : Type*) [Group G] (H J : Subgroup G) (h : H ≤ J)
    (a : J) (ha : (a : G) ∈ H) :
    ((a⁻¹ : J) : G) ∈ H := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.subgroupRestrict_inv_mem <;> assumption





def subgroupRestrict
    {G : Type*} [Group G] (H J : Subgroup G) (_h : H ≤ J) : Subgroup J where
  carrier := {x : J | (x : G) ∈ H}
  one_mem' := subgroupRestrict_one_mem G H J _h
  mul_mem' := fun {a b} ha hb => subgroupRestrict_mul_mem G H J _h a b ha hb
  inv_mem' := fun {a} ha => subgroupRestrict_inv_mem G H J _h a ha



theorem rayIdealGroup_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ (1 : IdealGroup K) = PrincipalIdealOfUnit x := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.rayIdealGroup_one_mem <;> assumption




theorem rayIdealGroup_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I J : IdealGroup K)
    (hI : ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x)
    (hJ : ∃ x : Kˣ, InKPowModulusOne m x ∧ J = PrincipalIdealOfUnit x) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ I * J = PrincipalIdealOfUnit x := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.rayIdealGroup_mul_mem <;> assumption




theorem rayIdealGroup_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (I : IdealGroup K)
    (hI : ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x) :
    ∃ x : Kˣ, InKPowModulusOne m x ∧ I⁻¹ = PrincipalIdealOfUnit x := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.rayIdealGroup_inv_mem <;> assumption





def RayIdealGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroup K) where
  carrier := {I | ∃ x : Kˣ, InKPowModulusOne m x ∧ I = PrincipalIdealOfUnit x}
  one_mem' := rayIdealGroup_one_mem K m
  mul_mem' := fun {I J} hI hJ => rayIdealGroup_mul_mem K m I J hI hJ
  inv_mem' := fun {I} hI => rayIdealGroup_inv_mem K m I hI



theorem rayIdealGroup_le_idealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    RayIdealGroup K m ≤ IdealGroupPrimeToModulus K m := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.rayIdealGroup_le_idealGroupPrimeToModulus <;> assumption







def RayIdealGroupInPrimeTo
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (IdealGroupPrimeToModulus K m) :=
  subgroupRestrict (RayIdealGroup K m) (IdealGroupPrimeToModulus K m)
    (rayIdealGroup_le_idealGroupPrimeToModulus K m)


abbrev RayClassGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :=
  IdealGroupPrimeToModulus K m ⧸ RayIdealGroupInPrimeTo K m

structure CongruenceSubgroup
    (K : Type*) [Field K] [NumberField K] where
  modulus : Modulus K
  carrier : Subgroup (IdealGroup K)
  carrier_le : carrier ≤ IdealGroupPrimeToModulus K modulus
  ray_le : RayIdealGroup K modulus ≤ carrier


def carrierInPrimeTo
    {K : Type*} [Field K] [NumberField K] (C : CongruenceSubgroup K) :
    Subgroup (IdealGroupPrimeToModulus K C.modulus) :=
  subgroupRestrict C.carrier (IdealGroupPrimeToModulus K C.modulus) C.carrier_le


abbrev congruenceSubgroupQuotient
    {K : Type*} [Field K] [NumberField K] (C : CongruenceSubgroup K) : Type _ :=
  IdealGroupPrimeToModulus K C.modulus ⧸ carrierInPrimeTo C


def congruenceSubgroupIndex
    {K : Type*} [Field K] [NumberField K]
    (C : CongruenceSubgroup K) [Finite (congruenceSubgroupQuotient C)] : ℕ :=
  Nat.card (congruenceSubgroupQuotient C)




theorem kPowModulus_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    InKPowModulus m (1 : Kˣ) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulus_one_mem <;> assumption




theorem kPowModulus_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (x y : Kˣ) (hx : InKPowModulus m x) (hy : InKPowModulus m y) :
    InKPowModulus m (x * y) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulus_mul_mem <;> assumption




theorem kPowModulus_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (x : Kˣ) (hx : InKPowModulus m x) :
    InKPowModulus m x⁻¹ := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulus_inv_mem <;> assumption





def KPowModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) : Subgroup Kˣ where
  carrier := {x | InKPowModulus m x}
  one_mem' := kPowModulus_one_mem K m
  mul_mem' := fun {x y} hx hy => kPowModulus_mul_mem K m x y hx hy
  inv_mem' := fun {x} hx => kPowModulus_inv_mem K m x hx



theorem kPowModulusOne_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    InKPowModulusOne m ((1 : ↥(KPowModulus K m)) : Kˣ) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulusOne_one_mem <;> assumption




theorem kPowModulusOne_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (x y : ↥(KPowModulus K m))
    (hx : InKPowModulusOne m (x : Kˣ)) (hy : InKPowModulusOne m (y : Kˣ)) :
    InKPowModulusOne m (↑(x * y) : Kˣ) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulusOne_mul_mem <;> assumption




theorem kPowModulusOne_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (x : ↥(KPowModulus K m)) (hx : InKPowModulusOne m (x : Kˣ)) :
    InKPowModulusOne m (↑x⁻¹ : Kˣ) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulusOne_inv_mem <;> assumption









def KPowModulusOne
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (KPowModulus K m) where
  carrier := {x | InKPowModulusOne m x.1}
  one_mem' := kPowModulusOne_one_mem K m
  mul_mem' := fun {x y} hx hy => kPowModulusOne_mul_mem K m x y hx hy
  inv_mem' := fun {x} hx => kPowModulusOne_inv_mem K m x hx


abbrev KPowModulusQuotient
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :=
  KPowModulus K m ⧸ KPowModulusOne K m



theorem unitInKPowModulusOne_one_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    InKPowModulusOne m (unitToFieldUnit K (1 : (𝓞 K)ˣ)) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.unitInKPowModulusOne_one_mem <;> assumption




theorem unitInKPowModulusOne_mul_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (u v : (𝓞 K)ˣ)
    (hu : InKPowModulusOne m (unitToFieldUnit K u))
    (hv : InKPowModulusOne m (unitToFieldUnit K v)) :
    InKPowModulusOne m (unitToFieldUnit K (u * v)) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.unitInKPowModulusOne_mul_mem <;> assumption




theorem unitInKPowModulusOne_inv_mem
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (u : (𝓞 K)ˣ) (hu : InKPowModulusOne m (unitToFieldUnit K u)) :
    InKPowModulusOne m (unitToFieldUnit K u⁻¹) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.unitInKPowModulusOne_inv_mem <;> assumption







def UnitInKPowModulusOne
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    Subgroup (𝓞 K)ˣ where
  carrier := {u | InKPowModulusOne m (unitToFieldUnit K u)}
  one_mem' := unitInKPowModulusOne_one_mem K m
  mul_mem' := fun {u v} hu hv => unitInKPowModulusOne_mul_mem K m u v hu hv
  inv_mem' := fun {u} hu => unitInKPowModulusOne_inv_mem K m u hu


def unitIntersectionInclusion
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    UnitInKPowModulusOne K m →* (𝓞 K)ˣ :=
  (UnitInKPowModulusOne K m).subtype



theorem unitToFieldUnit_mem_kPowModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) (u : (𝓞 K)ˣ) :
    unitToFieldUnit K u ∈ KPowModulus K m := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.unitToFieldUnit_mem_kPowModulus <;> assumption




theorem unitToKPowModulus_map_one
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    unitToFieldUnit K (1 : (𝓞 K)ˣ) = (1 : Kˣ) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.unitToKPowModulus_map_one <;> assumption




theorem unitToKPowModulus_map_mul
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) (u v : (𝓞 K)ˣ) :
    unitToFieldUnit K (u * v) = unitToFieldUnit K u * unitToFieldUnit K v := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.unitToKPowModulus_map_mul <;> assumption







def unitToKPowModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    (𝓞 K)ˣ →* KPowModulus K m where
  toFun u := ⟨unitToFieldUnit K u, unitToFieldUnit_mem_kPowModulus K m u⟩
  map_one' := Subtype.ext (unitToKPowModulus_map_one K m)
  map_mul' := fun u v => Subtype.ext (unitToKPowModulus_map_mul K m u v)


def unitToKPowModulusQuotient
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    (𝓞 K)ˣ →* KPowModulusQuotient K m :=
  (QuotientGroup.mk' (KPowModulusOne K m)).comp (unitToKPowModulus K m)



theorem principalIdealOfUnit_mem_idealGroupPrimeToModulus
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (x : ↥(KPowModulus K m)) :
    PrincipalIdealOfUnit (x : Kˣ) ∈ IdealGroupPrimeToModulus K m := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.principalIdealOfUnit_mem_idealGroupPrimeToModulus <;> assumption




theorem principalIdealMap_map_one
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    PrincipalIdealOfUnit ((1 : ↥(KPowModulus K m)) : Kˣ) = (1 : IdealGroup K) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.principalIdealMap_map_one <;> assumption




theorem principalIdealMap_map_mul
    (K : Type*) [Field K] [NumberField K] (m : Modulus K)
    (x y : ↥(KPowModulus K m)) :
    PrincipalIdealOfUnit (↑(x * y) : Kˣ) =
      PrincipalIdealOfUnit (x : Kˣ) * PrincipalIdealOfUnit (y : Kˣ) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.principalIdealMap_map_mul <;> assumption





def principalIdealMap
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    KPowModulus K m →* IdealGroupPrimeToModulus K m where
  toFun x :=
    ⟨PrincipalIdealOfUnit x.1, principalIdealOfUnit_mem_idealGroupPrimeToModulus K m x⟩
  map_one' := Subtype.ext (principalIdealMap_map_one K m)
  map_mul' := fun x y => Subtype.ext (principalIdealMap_map_mul K m x y)



theorem kPowModulusOne_le_ker_rayClassComp
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    KPowModulusOne K m ≤
      ((QuotientGroup.mk' (RayIdealGroupInPrimeTo K m)).comp
        (principalIdealMap K m)).ker := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulusOne_le_ker_rayClassComp <;> assumption





def kPowModulusQuotientToRayClass
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    KPowModulusQuotient K m →* RayClassGroup K m :=
  QuotientGroup.lift (KPowModulusOne K m)
    ((QuotientGroup.mk' (RayIdealGroupInPrimeTo K m)).comp (principalIdealMap K m))
    (kPowModulusOne_le_ker_rayClassComp K m)




theorem exists_idealGroupToClassGroup
    (K : Type*) [Field K] [NumberField K] :
    ∃ φ : IdealGroup K →* OrdinaryClassGroup K,
      ∀ x : Kˣ, φ (PrincipalIdealOfUnit x) = 1 := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.exists_idealGroupToClassGroup <;> assumption







def idealGroupToClassGroup
    (K : Type*) [Field K] [NumberField K] : IdealGroup K →* OrdinaryClassGroup K :=
  ClassGroup.mk K


def idealGroupPrimeToModulusToClassGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    IdealGroupPrimeToModulus K m →* OrdinaryClassGroup K :=
  (idealGroupToClassGroup K).comp (IdealGroupPrimeToModulus K m).subtype



theorem rayIdealGroupInPrimeTo_le_ker_classGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    RayIdealGroupInPrimeTo K m ≤ (idealGroupPrimeToModulusToClassGroup K m).ker := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.rayIdealGroupInPrimeTo_le_ker_classGroup <;> assumption










def rayClassToClassGroup
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    RayClassGroup K m →* OrdinaryClassGroup K :=
  QuotientGroup.lift (RayIdealGroupInPrimeTo K m)
    (idealGroupPrimeToModulusToClassGroup K m)
    (rayIdealGroupInPrimeTo_le_ker_classGroup K m)


def SignResidueCompatible
    {K : Type*} [Field K] [NumberField K]
    (m : Modulus K) (x : KPowModulus K m) (y : SignResidueGroup K m) : Prop :=
  ∃ a b : 𝓞 K,
    a ≠ 0 ∧ b ≠ 0 ∧
      IsCoprime (Ideal.span ({a} : Set (𝓞 K))) m.finitePart.1 ∧
        IsCoprime (Ideal.span ({b} : Set (𝓞 K))) m.finitePart.1 ∧
          ((a : 𝓞 K) : K) = (x.1 : K) * (b : K) ∧
            (∀ w : {w : RealInfinitePlace K // w ∈ m.infinitePart},
            y.1 w = if 0 < NumberField.InfinitePlace.embedding_of_isReal w.1.2 x.1 then 1 else -1) ∧
              ∃ ua ub : ((𝓞 K) ⧸ m.finitePart.1)ˣ,
                (ua : (𝓞 K) ⧸ m.finitePart.1) = Ideal.Quotient.mk m.finitePart.1 a ∧
                  (ub : (𝓞 K) ⧸ m.finitePart.1) = Ideal.Quotient.mk m.finitePart.1 b ∧
                    y.2 = ua * ub⁻¹



theorem exists_signResidueMap
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    ∃ φ : KPowModulus K m →* SignResidueGroup K m,
      ∀ x : KPowModulus K m, SignResidueCompatible m x (φ x) := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.exists_signResidueMap <;> assumption





def signResidueMap
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    KPowModulus K m →* SignResidueGroup K m :=
  Classical.choose (exists_signResidueMap K m)



theorem kPowModulusOne_le_ker_signResidueMap
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    KPowModulusOne K m ≤ (signResidueMap K m).ker := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.kPowModulusOne_le_ker_signResidueMap <;> assumption


def signResidueQuotientMap
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    KPowModulusQuotient K m →* SignResidueGroup K m :=
  QuotientGroup.lift (KPowModulusOne K m) (signResidueMap K m)
    (kPowModulusOne_le_ker_signResidueMap K m)







def IsCanonicalSignResidueEquiv
    {K : Type*} [Field K] [NumberField K] (m : Modulus K)
    (e : KPowModulusQuotient K m ≃* SignResidueGroup K m) : Prop :=
  ∀ x : KPowModulus K m,
    e (QuotientGroup.mk' (KPowModulusOne K m) x) = signResidueMap K m x


def ExactSequence21_8
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) : Prop :=
  (unitIntersectionInclusion K m).ker = ⊥ ∧
    (unitIntersectionInclusion K m).range = (unitToKPowModulusQuotient K m).ker ∧
      (unitToKPowModulusQuotient K m).range = (kPowModulusQuotientToRayClass K m).ker ∧
        (kPowModulusQuotientToRayClass K m).range = (rayClassToClassGroup K m).ker ∧
          (rayClassToClassGroup K m).range = (classGroupToUnit K).ker ∧
            (classGroupToUnit K).range = ⊤






theorem Theorem21_8
    (K : Type*) [Field K] [NumberField K] (m : Modulus K) :
    ExactSequence21_8 K m ∧
      ∃ e : KPowModulusQuotient K m ≃* SignResidueGroup K m,
        IsCanonicalSignResidueEquiv m e := by apply Submission.Autoform_Number_Theory_I_number_theory_Theorem21_8.Theorem21_8 <;> assumption

end Autoform_Number_Theory_I_number_theory_Theorem21_8

end
