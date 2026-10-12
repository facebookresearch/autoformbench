/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





















open scoped BigOperators
open Module

universe u v

namespace Autoform_Tensor_Categories_tensor_cat_proposition_1_45_5







def IsNonnegativeReal (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re







def IsPositiveReal (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 < z.re

lemma intCast_isNonnegativeReal {n : ℤ} (hn : 0 ≤ n) :
    IsNonnegativeReal ((n : ℂ)) := by
  constructor
  · simp
  · simpa using (Int.cast_nonneg hn : (0 : ℝ) ≤ (n : ℝ))

section PerronRoot

variable {ι : Type u} [Fintype ι]








abbrev matrixEnd (M : Matrix ι ι ℂ) : Module.End ℂ (ι → ℂ) :=
  M.mulVecLin








def IsEigenvalue (M : Matrix ι ι ℂ) (μ : ℂ) : Prop :=
  Module.End.HasEigenvalue (matrixEnd M) μ







def MatrixNonnegative (M : Matrix ι ι ℂ) : Prop :=
  ∀ i j : ι, IsNonnegativeReal (M i j)









def IsPerronRoot (M : Matrix ι ι ℂ) (ρ : ℂ) : Prop :=
  IsNonnegativeReal ρ ∧
  IsEigenvalue M ρ ∧
  ∀ μ : ℂ, IsEigenvalue M μ → ‖μ‖ ≤ ρ.re



end PerronRoot















structure TransitiveZPlusRing (ι : Type u) (A : Type v)
    [Fintype ι] [DecidableEq ι] [Ring A] where
  basis : Basis ι ℤ A
  oneIndex : ι
  basis_one : basis oneIndex = (1 : A)

  



  mul_nonneg :
    ∀ i j k : ι, 0 ≤ basis.repr (basis i * basis j) k

  




  transitive :
    ∀ i k : ι,
      (∃ j : ι, 0 < basis.repr (basis i * basis j) k) ∧
      (∃ j : ι, 0 < basis.repr (basis j * basis i) k)

namespace TransitiveZPlusRing

variable {ι : Type u} {A : Type v}
variable [Fintype ι] [DecidableEq ι] [Ring A]








abbrev AC (_ : TransitiveZPlusRing ι A) : Type _ :=
  ι → ℂ








noncomputable def toAC (T : TransitiveZPlusRing ι A) (x : A) : T.AC :=
  fun i => (T.basis.repr x i : ℂ)








noncomputable def mulC (T : TransitiveZPlusRing ι A) (x y : T.AC) : T.AC :=
  fun k =>
    ∑ i : ι, ∑ j : ι,
      x i * y j * (T.basis.repr (T.basis i * T.basis j) k : ℂ)












def IsNonnegativeElement (T : TransitiveZPlusRing ι A) (x : A) : Prop :=
  ∀ i : ι, 0 ≤ T.basis.repr x i







def PositiveCoefficients (T : TransitiveZPlusRing ι A) (R : T.AC) : Prop :=
  ∀ i : ι, IsPositiveReal (R i)










def CharacterNonnegativeOnBasis
    (T : TransitiveZPlusRing ι A) (χ : A →+* ℂ) : Prop :=
  ∀ i : ι, IsNonnegativeReal (χ (T.basis i))



end TransitiveZPlusRing

end Autoform_Tensor_Categories_tensor_cat_proposition_1_45_5
