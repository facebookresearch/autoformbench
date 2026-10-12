/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option warningAsError false
















universe uK uZ uD uV uI

namespace Autoform_Buildings_and_Classical_Groups_buildings_exists_nondegenerate_complement_and_hyperbolic_completion





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
    (S : FormedScalarData k Z D)
    (V : Type uV) [AddCommGroup V] [Module D V] where
  epsilon : D
  epsilon_eq_one_or_neg_one : epsilon = 1 ∨ epsilon = -1
  B : V → V → D
  zero_left : ∀ y : V, B 0 y = 0
  add_left : ∀ x y z : V, B (x + y) z = B x z + B y z
  smul_left : ∀ (a : D) (x y : V), B (a • x) y = a * B x y
  zero_right : ∀ x : V, B x 0 = 0
  add_right : ∀ x y z : V, B x (y + z) = B x y + B x z
  smul_right : ∀ (a : D) (x y : V), B x (a • y) = B x y * S.involution.star a
  hermitian : ∀ x y : V, B y x = epsilon * S.involution.star (B x y)

namespace EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D}
variable {V : Type uV} [AddCommGroup V] [Module D V]



def orthogonal (F : EpsilonHermitianForm S V) (U : Submodule D V) : Submodule D V where
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



def subspaceKernel (F : EpsilonHermitianForm S V) (U : Submodule D V) : Submodule D V :=
  U ⊓ F.orthogonal U


def IsNondegenerate (F : EpsilonHermitianForm S V) : Prop :=
  F.subspaceKernel (⊤ : Submodule D V) = ⊥


def IsNondegenerateOn (F : EpsilonHermitianForm S V) (U : Submodule D V) : Prop :=
  F.subspaceKernel U = ⊥


def line (_ : EpsilonHermitianForm S V) (x : V) : Submodule D V :=
  Submodule.span D ({x} : Set V)


def plane (F : EpsilonHermitianForm S V) (x y : V) : Submodule D V :=
  F.line x ⊔ F.line y



def AreOrthogonal (F : EpsilonHermitianForm S V) (U W : Submodule D V) : Prop :=
  ∀ u : V, u ∈ U → ∀ w : V, w ∈ W → F.B u w = 0



def IsHyperbolicPair (F : EpsilonHermitianForm S V) (x y : V) : Prop :=
  Disjoint (F.line x) (F.line y) ∧
    F.B x x = 0 ∧ F.B y y = 0 ∧ F.B x y = 1


def IsInternalDirectSum₂ (A B C : Submodule D V) : Prop :=
  A ⊔ B = C ∧ Disjoint A B


def spanFamily {κ : Type uI} (F : EpsilonHermitianForm S V) (v : κ → V) :
    Submodule D V :=
  ⨆ k : κ, F.line (v k)



def IndependentSubmoduleFamily {κ : Type uI} (A : κ → Submodule D V) : Prop :=
  ∀ k : κ, Disjoint (A k) (⨆ l : {l : κ // l ≠ k}, A l.1)


def IsInternalDirectSumFamily {κ : Type uI} (A : κ → Submodule D V)
    (U : Submodule D V) : Prop :=
  (⨆ k : κ, A k) = U ∧ IndependentSubmoduleFamily A


def familyWithBase {κ : Type uI} (F : EpsilonHermitianForm S V)
    (W : Submodule D V) (y : κ → V) : Option κ → Submodule D V
  | none => W
  | some k => F.line (y k)


def IsDirectSumOfSubmoduleAndLines {κ : Type uI} (F : EpsilonHermitianForm S V)
    (W : Submodule D V) (y : κ → V) : Prop :=
  IsInternalDirectSumFamily (F.familyWithBase W y) (W ⊔ F.spanFamily y)



def IsOrthogonalHyperbolicDecomposition {κ : Type uI}
    (F : EpsilonHermitianForm S V) (U : Submodule D V) (x y : κ → V) : Prop :=
  U = (⨆ k : κ, F.plane (x k) (y k)) ∧
    IndependentSubmoduleFamily (fun k : κ => F.plane (x k) (y k)) ∧
    (∀ k : κ, F.IsHyperbolicPair (x k) (y k)) ∧
    (∀ k l : κ, k ≠ l →
      F.AreOrthogonal (F.plane (x k) (y k)) (F.plane (x l) (y l)))

end EpsilonHermitianForm

open EpsilonHermitianForm

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D}
variable {V : Type uV} [AddCommGroup V] [Module D V]



end Autoform_Buildings_and_Classical_Groups_buildings_exists_nondegenerate_complement_and_hyperbolic_completion
