/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

































open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_15_1

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





structure BrauerGroupLaw (F : Type u) [Field F] where
  commGroup : CommGroup (BrauerGroup.{u, u} F)
  multiplication_is_tensorProduct :
    letI := commGroup
    ∀ x y : BrauerGroup.{u, u} F,
      BrauerClass.IsTensorProduct F x y (x * y)




































structure FiniteGaloisExtensionHom
    (F E K : Type u)
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K] where
  toAlgHom : E →ₐ[F] K
  restriction : Gal(K/F) →* Gal(E/F)
  restriction_surjective : Function.Surjective restriction
  equivariant :
    ∀ (σ : Gal(K/F)) (x : E),
      toAlgHom (restriction σ x) = σ (toAlgHom x)









namespace FiniteGaloisExtensionHom




def mapUnits
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K) :
    Eˣ →* Kˣ :=
  Units.map f.toAlgHom.toRingHom.toMonoidHom





def mapTwoCochain
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K)
    (c : Gal(E/F) × Gal(E/F) → Eˣ) :
    Gal(K/F) × Gal(K/F) → Kˣ :=
  fun στ =>
    f.mapUnits (c (f.restriction στ.1, f.restriction στ.2))

end FiniteGaloisExtensionHom



























end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_15_1
