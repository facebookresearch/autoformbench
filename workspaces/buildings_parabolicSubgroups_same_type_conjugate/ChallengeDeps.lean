import Mathlib

set_option warningAsError false
















universe uK uZ uD uV uI

namespace Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate





structure RingInvolution (D : Type uD) [DivisionRing D] where
  star : D → D
  map_zero : star 0 = 0
  map_one : star 1 = 1
  map_add : ∀ a b : D, star (a + b) = star a + star b
  map_mul : ∀ a b : D, star (a * b) = star b * star a
  involutive : ∀ a : D, star (star a) = a


def IsCentralElement {D : Type uD} [Mul D] (z : D) : Prop :=
  ∀ x : D, z * x = x * z



def IsCenterAlgebra (Z : Type uZ) (D : Type uD)
    [Field Z] [DivisionRing D] [Algebra Z D] : Prop :=
  ∀ z : D, IsCentralElement z ↔ ∃ c : Z, algebraMap Z D c = z



def IsFixedFieldOfCenter {D : Type uD} [DivisionRing D]
    (σ : RingInvolution D) (k : Type uK) [Field k] [Algebra k D] : Prop :=
  (∀ c : k, σ.star (algebraMap k D c) = algebraMap k D c) ∧
    ∀ z : D, IsCentralElement z →
      (σ.star z = z ↔ ∃ c : k, algebraMap k D c = z)




structure FormedScalarData (k : Type uK) (Z : Type uZ) (D : Type uD)
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D] where
  involution : RingInvolution D
  center_is_center : IsCenterAlgebra Z D
  fixed_field : IsFixedFieldOfCenter involution k
  finite_over_center : FiniteDimensional Z D












structure EpsilonHermitianForm
    {k : Type uK} {Z : Type uZ} {D : Type uD}
    [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
    (S : FormedScalarData k Z D) (ε : D)
    (V : Type uV) [AddCommGroup V] [Module D V] where
  epsilon_eq_one_or_neg_one : ε = 1 ∨ ε = -1
  B : V → V → D
  zero_left : ∀ y : V, B 0 y = 0
  add_left : ∀ x y z : V, B (x + y) z = B x z + B y z
  smul_left : ∀ (a : D) (x y : V), B (a • x) y = a * B x y
  zero_right : ∀ x : V, B x 0 = 0
  add_right : ∀ x y z : V, B x (y + z) = B x y + B x z
  smul_right : ∀ (a : D) (x y : V), B x (a • y) = B x y * S.involution.star a
  hermitian : ∀ x y : V, B y x = ε * S.involution.star (B x y)

namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]



def orthogonal (F : EpsilonHermitianForm S ε V) (U : Submodule D V) : Submodule D V where
  carrier := {v : V | ∀ u : V, u ∈ U → F.B v u = 0}
  zero_mem' := by
    intro u _hu
    simpa using F.zero_left u
  add_mem' := by
    intro x y hx hy u hu
    rw [F.add_left, hx u hu, hy u hu, zero_add]
  smul_mem' := by
    intro a x hx u hu
    rw [F.smul_left, hx u hu, mul_zero]


def kernel (F : EpsilonHermitianForm S ε V) : Submodule D V :=
  F.orthogonal (⊤ : Submodule D V)


def IsNondegenerate (F : EpsilonHermitianForm S ε V) : Prop :=
  F.kernel = ⊥



def IsTotallyIsotropic (F : EpsilonHermitianForm S ε V) (U : Submodule D V) : Prop :=
  ∀ u : V, u ∈ U → ∀ v : V, v ∈ U → F.B u v = 0



def IsIsometry (F : EpsilonHermitianForm S ε V) (g : V ≃ₗ[D] V) : Prop :=
  ∀ x y : V, F.B (g x) (g y) = F.B x y

end EpsilonHermitianForm












namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]



def linearImageSet (g : V ≃ₗ[D] V) (U : Submodule D V) : Set V :=
  {v : V | ∃ u : V, u ∈ U ∧ g u = v}



def StabilizesSubspace (g : V ≃ₗ[D] V) (U : Submodule D V) : Prop :=
  linearImageSet g U = (U : Set V)

end EpsilonHermitianForm












namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]







def SameDDimension (U W : Submodule D V) : Prop :=
  Nonempty (U ≃ₗ[D] W)



structure IsotropicFlag (F : EpsilonHermitianForm S ε V)
    (ι : Type uI) [Preorder ι] where
  subspace : ι → Submodule D V
  strictly_increasing : ∀ ⦃i j : ι⦄, i < j → subspace i < subspace j
  totally_isotropic : ∀ i : ι, F.IsTotallyIsotropic (subspace i)

namespace IsotropicFlag

variable {ι : Type uI} [Preorder ι]



def SameType {F : EpsilonHermitianForm S ε V} (𝓕 𝓖 : IsotropicFlag F ι) : Prop :=
  ∀ i : ι, SameDDimension (𝓕.subspace i) (𝓖.subspace i)

end IsotropicFlag

end EpsilonHermitianForm












namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}
variable {V : Type uV} [AddCommGroup V] [Module D V]




structure ParabolicSubgroup (F : EpsilonHermitianForm S ε V)
    (ι : Type uI) [Preorder ι] where
  flag : IsotropicFlag F ι

namespace ParabolicSubgroup

variable {ι : Type uI} [Preorder ι]




def SameType {F : EpsilonHermitianForm S ε V}
    (P Q : ParabolicSubgroup F ι) : Prop :=
  IsotropicFlag.SameType P.flag Q.flag

end ParabolicSubgroup


end EpsilonHermitianForm



end Autoform_Buildings_and_Classical_Groups_buildings_parabolicSubgroups_same_type_conjugate
