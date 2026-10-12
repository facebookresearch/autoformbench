/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Autoform_Lie_groups_lie_algebras_lie_lemma_15_18




attribute [scoped instance 100] LieRing.ofAssociativeRing

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}

variable [Field K]
variable [LieRing L] [LieAlgebra K L]
variable [AddCommGroup V] [Module K V]
variable [LieRingModule L V] [LieModule K L V]










def IsDirectSumWithSpan (x : L) (H : LieIdeal K L) : Prop :=
  IsCompl (Submodule.span K ({x} : Set L)) (H : Submodule K L)








def actionEnd (x : L) : Module.End K V :=
  (LieModule.toEnd K L V) x







def shiftedActionEnd (a : L) (μ : K) : Module.End K V :=
  actionEnd (K := K) (L := L) (V := V) a
    - μ • (LinearMap.id : Module.End K V)







def cyclicSubmodule (x : L) (v : V) : Submodule K V :=
  Submodule.span K
    (Set.range
      (fun n : ℕ =>
        ((actionEnd (K := K) (L := L) (V := V) x) ^ n) v))





def IsNilpotentOn (f : Module.End K V) (W : Submodule K V) : Prop :=
  ∃ hf : Set.MapsTo f W W, IsNilpotent (LinearMap.restrict f hf)









def VanishesOnBracket (H : LieIdeal K L) (χ : H →ₗ⁅K⁆ K) : Prop :=
  ∀ (a : H) (y : L),
    χ ⟨⁅(a : L), y⁆, lie_mem_left K L H (a : L) y a.property⟩ = 0






def commonEigenSpace (H : LieIdeal K L) (χ : H →ₗ⁅K⁆ K) :
    Submodule K V where
  carrier := {m : V | ∀ a : H, ⁅(a : L), m⁆ = χ a • m}
  zero_mem' := by
    intro a
    simp
  add_mem' := by
    intro m n hm hn a
    rw [lie_add, hm a, hn a, smul_add]
  smul_mem' := by
    intro c m hm a
    calc
      ⁅(a : L), c • m⁆ = c • ⁅(a : L), m⁆ := by
        rw [lie_smul]
      _ = c • (χ a • m) := by
        rw [hm a]
      _ = (c * χ a) • m := by
        rw [smul_smul]
      _ = (χ a * c) • m := by
        rw [mul_comm]
      _ = χ a • (c • m) := by
        rw [← smul_smul]



end Autoform_Lie_groups_lie_algebras_lie_lemma_15_18
