/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

























open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_19_5_brauer_injective_to_fractionField

noncomputable section






structure AzumayaAlgebra
    (R : Type u) [CommRing R] where
  carrier : Type u
  [ring : Ring carrier]
  [algebra : Algebra R carrier]
  [azumaya : IsAzumaya R carrier]

attribute [instance] AzumayaAlgebra.ring
attribute [instance] AzumayaAlgebra.algebra
attribute [instance] AzumayaAlgebra.azumaya








structure FiniteProjectiveFaithfulModule
    (R : Type u) [CommRing R] where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]
  [finite : Module.Finite R carrier]
  [projective : Module.Projective R carrier]
  [faithful : FaithfulSMul R carrier]

attribute [instance] FiniteProjectiveFaithfulModule.addCommGroup
attribute [instance] FiniteProjectiveFaithfulModule.module
attribute [instance] FiniteProjectiveFaithfulModule.finite
attribute [instance] FiniteProjectiveFaithfulModule.projective
attribute [instance] FiniteProjectiveFaithfulModule.faithful







def AzumayaBrauerEquivalent
    (R : Type u) [CommRing R]
    (A B : AzumayaAlgebra R) : Prop :=
  ∃ P Q : FiniteProjectiveFaithfulModule R,
    Nonempty
      ((A.carrier ⊗[R] Module.End R P.carrier) ≃ₐ[R]
        (B.carrier ⊗[R] Module.End R Q.carrier))














def csaToBrauerClass
    {K : Type u} [Field K]
    (A : CSA.{u, u} K) :
    BrauerGroup.{u, u} K :=
  Quotient.mk (Brauer.CSA_Setoid K) A

namespace AzumayaBrauerClass


end AzumayaBrauerClass

namespace FieldBrauerClass

end FieldBrauerClass











def IsGenericFiberRepresentative
    {R F : Type u}
    [CommRing R] [Field F] [Algebra R F]
    (A : AzumayaAlgebra R)
    (B : CSA.{u, u} F) : Prop :=
  Nonempty ((F ⊗[R] A.carrier) ≃ₐ[F] B)





end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_19_5_brauer_injective_to_fractionField
