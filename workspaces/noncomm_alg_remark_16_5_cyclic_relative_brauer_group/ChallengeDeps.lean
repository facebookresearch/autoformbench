/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





























open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_remark_16_5_cyclic_relative_brauer_group

noncomputable section







def csaToBrauerClass
    {F : Type u} [Field F]
    (A : CSA.{u, u} F) :
    BrauerGroup.{u, u} F :=
  Quotient.mk (Brauer.CSA_Setoid F) A









def CSAIsSplitBy
    {F : Type u} [Field F]
    (A : CSA.{u, u} F)
    (E : Type u) [Field E] [Algebra F E] : Prop :=
  ∃ n : ℕ,
    n ≠ 0 ∧
      Nonempty
        ((E ⊗[F] A) ≃ₐ[E]
          Matrix (Fin n) (Fin n) E)

namespace BrauerClass







def IsSplitBy
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    (x : BrauerGroup.{u, u} F) : Prop :=
  ∃ A : CSA.{u, u} F,
    csaToBrauerClass A = x ∧ CSAIsSplitBy A E






def IsTensorProduct
    (F : Type u) [Field F]
    (x y z : BrauerGroup.{u, u} F) : Prop :=
  ∃ A B C : CSA.{u, u} F,
    csaToBrauerClass A = x ∧
      csaToBrauerClass B = y ∧
        csaToBrauerClass C = z ∧
          Nonempty ((A ⊗[F] B) ≃ₐ[F] C)

end BrauerClass






abbrev RelativeBrauerGroup
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Type (u + 1) :=
  {x : BrauerGroup.{u, u} F // BrauerClass.IsSplitBy F E x}








structure RelativeBrauerGroupLaw
    (F E : Type u) [Field F] [Field E] [Algebra F E] where
  group : CommGroup (RelativeBrauerGroup F E)
  multiplication_is_tensorProduct :
    letI := group
    ∀ x y : RelativeBrauerGroup F E,
      BrauerClass.IsTensorProduct F x.1 y.1 (x * y).1










def normUnitsHom
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    Eˣ →* Fˣ :=
  Units.map (Algebra.norm F)




def normUnitsSubgroup
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    Subgroup Fˣ :=
  (normUnitsHom F E).range




abbrev NormUnitsQuotient
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    Type u :=
  Fˣ ⧸ normUnitsSubgroup F E



end

end Autoform_Noncommutative_Algebra_noncomm_alg_remark_16_5_cyclic_relative_brauer_group
