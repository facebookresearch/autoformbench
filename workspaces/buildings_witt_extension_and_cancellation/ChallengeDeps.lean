import Mathlib

set_option warningAsError false



















universe uK uZ uD uV uU uX uY

namespace Autoform_Buildings_and_Classical_Groups_buildings_witt_extension_and_cancellation





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



structure SpaceIsometry
    {V₁ : Type uV} [AddCommGroup V₁] [Module D V₁]
    {V₂ : Type uU} [AddCommGroup V₂] [Module D V₂]
    (F₁ : EpsilonHermitianForm S ε V₁) (F₂ : EpsilonHermitianForm S ε V₂) where
  toLinearEquiv : V₁ ≃ₗ[D] V₂
  preserves_form : ∀ x y : V₁, F₂.B (toLinearEquiv x) (toLinearEquiv y) = F₁.B x y



abbrev AmbientIsometry
    {V : Type uV} [AddCommGroup V] [Module D V]
    (F : EpsilonHermitianForm S ε V) : Type uV :=
  SpaceIsometry F F


structure SubspaceIsometry
    {V : Type uV} [AddCommGroup V] [Module D V]
    (F : EpsilonHermitianForm S ε V) (U W : Submodule D V) where
  toLinearEquiv : U ≃ₗ[D] W
  preserves_form : ∀ x y : U,
    F.B ((toLinearEquiv x : W) : V) ((toLinearEquiv y : W) : V) =
      F.B (x : V) (y : V)




def orthogonalSumValue
    {V₁ : Type uV} [AddCommGroup V₁] [Module D V₁]
    {V₂ : Type uU} [AddCommGroup V₂] [Module D V₂]
    (F₁ : EpsilonHermitianForm S ε V₁) (F₂ : EpsilonHermitianForm S ε V₂)
    (x y : V₁ × V₂) : D :=
  F₁.B x.1 y.1 + F₂.B x.2 y.2


structure OrthogonalSumIsometry
    {U₁ : Type uU} [AddCommGroup U₁] [Module D U₁]
    {V₁ : Type uV} [AddCommGroup V₁] [Module D V₁]
    {U₂ : Type uX} [AddCommGroup U₂] [Module D U₂]
    {V₂ : Type uY} [AddCommGroup V₂] [Module D V₂]
    (FU₁ : EpsilonHermitianForm S ε U₁) (FV₁ : EpsilonHermitianForm S ε V₁)
    (FU₂ : EpsilonHermitianForm S ε U₂) (FV₂ : EpsilonHermitianForm S ε V₂) where
  toLinearEquiv : (U₁ × V₁) ≃ₗ[D] (U₂ × V₂)
  preserves_form : ∀ x y : U₁ × V₁,
    orthogonalSumValue FU₂ FV₂ (toLinearEquiv x) (toLinearEquiv y) =
      orthogonalSumValue FU₁ FV₁ x y

end EpsilonHermitianForm

section WittExtension

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D} {ε : D}

open EpsilonHermitianForm



end WittExtension

end Autoform_Buildings_and_Classical_Groups_buildings_witt_extension_and_cancellation
