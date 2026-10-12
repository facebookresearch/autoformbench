/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib




















open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField

noncomputable section






abbrev RatModInt : Type :=
  ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)









abbrev FpLaurentSeriesField (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  LaurentSeries.RatFuncAdicCompl (ZMod p)




def csaToBrauerClass
    {F : Type u} [Field F]
    (A : CSA.{u, u} F) :
    BrauerGroup.{u, u} F :=
  Quotient.mk (Brauer.CSA_Setoid F) A

namespace BrauerClass








def IsTensorProduct
    (F : Type u) [Field F]
    (x y z : BrauerGroup.{u, u} F) : Prop :=
  ∃ A B C : CSA.{u, u} F,
    csaToBrauerClass A = x ∧
      csaToBrauerClass B = y ∧
        csaToBrauerClass C = z ∧
          Nonempty ((A ⊗[F] B) ≃ₐ[F] C)

end BrauerClass






structure BrauerGroupAdditiveLaw
    (F : Type u) [Field F] where
  addCommGroup : AddCommGroup (BrauerGroup.{u, u} F)
  addition_is_tensorProduct :
    letI := addCommGroup
    ∀ x y : BrauerGroup.{u, u} F,
      BrauerClass.IsTensorProduct F x y (x + y)













def IsBookNonarchimedeanLocalField
    (F : Type u) [Field F] : Prop :=
  (∃ p : ℕ, ∃ hp : Fact (Nat.Prime p),
    letI : Fact (Nat.Prime p) := hp
    ∃ alg : Algebra (Padic p) F,
      letI : Algebra (Padic p) F := alg
      FiniteDimensional (Padic p) F) ∨
  (∃ p : ℕ, ∃ hp : Fact (Nat.Prime p),
    letI : Fact (Nat.Prime p) := hp
    ∃ alg : Algebra (FpLaurentSeriesField p) F,
      letI : Algebra (FpLaurentSeriesField p) F := alg
      FiniteDimensional (FpLaurentSeriesField p) F)



end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField
