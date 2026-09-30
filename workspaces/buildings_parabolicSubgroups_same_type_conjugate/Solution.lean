


import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Basic
import Submission
import ChallengeDeps

open Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate
set_option warningAsError false
















universe uK uZ uD uV uI

namespace Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate

















namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]











end EpsilonHermitianForm








theorem isometryGroup_one_mem
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    {S : FormedScalarData k Z D} {ε : D}
    {V : Type uV} [AddCommGroup V] [Module D V]
    (F : EpsilonHermitianForm S ε V) :
    F.IsIsometry (1 : V ≃ₗ[D] V) := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.isometryGroup_one_mem <;> assumption



theorem isometryGroup_mul_mem
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    {S : FormedScalarData k Z D} {ε : D}
    {V : Type uV} [AddCommGroup V] [Module D V]
    (F : EpsilonHermitianForm S ε V) (a b : V ≃ₗ[D] V)
    (ha : F.IsIsometry a) (hb : F.IsIsometry b) :
    F.IsIsometry (a * b) := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.isometryGroup_mul_mem <;> assumption



theorem isometryGroup_inv_mem
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    {S : FormedScalarData k Z D} {ε : D}
    {V : Type uV} [AddCommGroup V] [Module D V]
    (F : EpsilonHermitianForm S ε V) (x : V ≃ₗ[D] V)
    (hx : F.IsIsometry x) :
    F.IsIsometry x⁻¹ := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.isometryGroup_inv_mem <;> assumption

namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]







end EpsilonHermitianForm








theorem conjugateSubgroupBy_one_mem
    {D : Type uD} [DivisionRing D]
    {V : Type uV} [AddCommGroup V] [Module D V]
    (g : V ≃ₗ[D] V) (H : Subgroup (V ≃ₗ[D] V)) :
    ∃ h : V ≃ₗ[D] V, h ∈ H ∧ g * h * g⁻¹ = 1 := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.conjugateSubgroupBy_one_mem <;> assumption



theorem conjugateSubgroupBy_mul_mem
    {D : Type uD} [DivisionRing D]
    {V : Type uV} [AddCommGroup V] [Module D V]
    (g : V ≃ₗ[D] V) (H : Subgroup (V ≃ₗ[D] V)) (a b : V ≃ₗ[D] V)
    (ha : ∃ h : V ≃ₗ[D] V, h ∈ H ∧ g * h * g⁻¹ = a)
    (hb : ∃ h : V ≃ₗ[D] V, h ∈ H ∧ g * h * g⁻¹ = b) :
    ∃ h : V ≃ₗ[D] V, h ∈ H ∧ g * h * g⁻¹ = a * b := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.conjugateSubgroupBy_mul_mem <;> assumption



theorem conjugateSubgroupBy_inv_mem
    {D : Type uD} [DivisionRing D]
    {V : Type uV} [AddCommGroup V] [Module D V]
    (g : V ≃ₗ[D] V) (H : Subgroup (V ≃ₗ[D] V)) (x : V ≃ₗ[D] V)
    (hx : ∃ h : V ≃ₗ[D] V, h ∈ H ∧ g * h * g⁻¹ = x) :
    ∃ h : V ≃ₗ[D] V, h ∈ H ∧ g * h * g⁻¹ = x⁻¹ := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.conjugateSubgroupBy_inv_mem <;> assumption

namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]









namespace IsotropicFlag

variable {ι : Type uI} [Preorder ι]

end IsotropicFlag

end EpsilonHermitianForm








theorem flagStabilizerParabolic_one_mem
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    {S : FormedScalarData k Z D} {ε : D}
    {V : Type uV} [AddCommGroup V] [Module D V]
    {ι : Type uI} [Preorder ι]
    (F : EpsilonHermitianForm S ε V)
    (𝓕 : EpsilonHermitianForm.IsotropicFlag F ι) :
    F.IsIsometry (1 : V ≃ₗ[D] V) ∧
      ∀ i : ι,
        EpsilonHermitianForm.StabilizesSubspace (1 : V ≃ₗ[D] V) (𝓕.subspace i) := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.flagStabilizerParabolic_one_mem <;> assumption



theorem flagStabilizerParabolic_mul_mem
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    {S : FormedScalarData k Z D} {ε : D}
    {V : Type uV} [AddCommGroup V] [Module D V]
    {ι : Type uI} [Preorder ι]
    (F : EpsilonHermitianForm S ε V)
    (𝓕 : EpsilonHermitianForm.IsotropicFlag F ι)
    (a b : V ≃ₗ[D] V)
    (ha : F.IsIsometry a ∧
      ∀ i : ι, EpsilonHermitianForm.StabilizesSubspace a (𝓕.subspace i))
    (hb : F.IsIsometry b ∧
      ∀ i : ι, EpsilonHermitianForm.StabilizesSubspace b (𝓕.subspace i)) :
    F.IsIsometry (a * b) ∧
      ∀ i : ι, EpsilonHermitianForm.StabilizesSubspace (a * b) (𝓕.subspace i) := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.flagStabilizerParabolic_mul_mem <;> assumption



theorem flagStabilizerParabolic_inv_mem
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    {S : FormedScalarData k Z D} {ε : D}
    {V : Type uV} [AddCommGroup V] [Module D V]
    {ι : Type uI} [Preorder ι]
    (F : EpsilonHermitianForm S ε V)
    (𝓕 : EpsilonHermitianForm.IsotropicFlag F ι)
    (x : V ≃ₗ[D] V)
    (hx : F.IsIsometry x ∧
      ∀ i : ι, EpsilonHermitianForm.StabilizesSubspace x (𝓕.subspace i)) :
    F.IsIsometry x⁻¹ ∧
      ∀ i : ι, EpsilonHermitianForm.StabilizesSubspace x⁻¹ (𝓕.subspace i) := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.flagStabilizerParabolic_inv_mem <;> assumption

namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]



def conjugateSubgroupBy (g : V ≃ₗ[D] V)
    (H : Subgroup (V ≃ₗ[D] V)) : Subgroup (V ≃ₗ[D] V) where
  carrier := {x : V ≃ₗ[D] V | ∃ h : V ≃ₗ[D] V, h ∈ H ∧ g * h * g⁻¹ = x}
  one_mem' := conjugateSubgroupBy_one_mem g H
  mul_mem' := fun {a b} ha hb => conjugateSubgroupBy_mul_mem g H a b ha hb
  inv_mem' := fun {x} hx => conjugateSubgroupBy_inv_mem g H x hx



def isometryGroup (F : EpsilonHermitianForm S ε V) : Subgroup (V ≃ₗ[D] V) where
  carrier := {g : V ≃ₗ[D] V | F.IsIsometry g}
  one_mem' := isometryGroup_one_mem F
  mul_mem' := fun {a b} ha hb => isometryGroup_mul_mem F a b ha hb
  inv_mem' := fun {x} hx => isometryGroup_inv_mem F x hx



def flagStabilizerParabolic {ι : Type uI} [Preorder ι]
    (F : EpsilonHermitianForm S ε V) (𝓕 : IsotropicFlag F ι) :
    Subgroup (V ≃ₗ[D] V) where
  carrier :=
    {g : V ≃ₗ[D] V | F.IsIsometry g ∧ ∀ i : ι, StabilizesSubspace g (𝓕.subspace i)}
  one_mem' := flagStabilizerParabolic_one_mem F 𝓕
  mul_mem' := fun {a b} ha hb => flagStabilizerParabolic_mul_mem F 𝓕 a b ha hb
  inv_mem' := fun {x} hx => flagStabilizerParabolic_inv_mem F 𝓕 x hx

namespace ParabolicSubgroup

variable {ι : Type uI} [Preorder ι]



def toSubgroup {F : EpsilonHermitianForm S ε V} (P : ParabolicSubgroup F ι) :
    Subgroup (V ≃ₗ[D] V) :=
  flagStabilizerParabolic F P.flag


end ParabolicSubgroup

end EpsilonHermitianForm












theorem parabolicSubgroups_same_type_conjugate
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    {S : FormedScalarData k Z D} {ε : D}
    {V : Type uV} [AddCommGroup V] [Module D V]
    [FiniteDimensional D V]
    (F : EpsilonHermitianForm S ε V)
    (_h_char_ne_two : (2 : k) ≠ 0)
    (_hV : F.IsNondegenerate)
    {ι : Type uI} [Fintype ι] [LinearOrder ι]
    (P Q : EpsilonHermitianForm.ParabolicSubgroup F ι)
    (_h_type : EpsilonHermitianForm.ParabolicSubgroup.SameType P Q) :
    ∃ g : EpsilonHermitianForm.isometryGroup F,
      EpsilonHermitianForm.conjugateSubgroupBy (g : V ≃ₗ[D] V)
          (EpsilonHermitianForm.ParabolicSubgroup.toSubgroup P) =
        EpsilonHermitianForm.ParabolicSubgroup.toSubgroup Q := by apply Submission.Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate.parabolicSubgroups_same_type_conjugate <;> assumption

end Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate
