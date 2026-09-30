


import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Projective
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic
import Submission.Helpers
import ChallengeDeps


























open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_19_5_brauer_injective_to_fractionField
open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_19_5_brauer_injective_to_fractionField

noncomputable section



attribute [instance] AzumayaAlgebra.ring
attribute [instance] AzumayaAlgebra.algebra
attribute [instance] AzumayaAlgebra.azumaya



attribute [instance] FiniteProjectiveFaithfulModule.addCommGroup
attribute [instance] FiniteProjectiveFaithfulModule.module
attribute [instance] FiniteProjectiveFaithfulModule.finite
attribute [instance] FiniteProjectiveFaithfulModule.projective
attribute [instance] FiniteProjectiveFaithfulModule.faithful










theorem azumayaBrauerEquivalent_refl
    (R : Type u) [CommRing R] (A : AzumayaAlgebra R) :
    AzumayaBrauerEquivalent R A A := by
  sorry







theorem azumayaBrauerEquivalent_symm
    (R : Type u) [CommRing R] (A B : AzumayaAlgebra R)
    (hAB : AzumayaBrauerEquivalent R A B) :
    AzumayaBrauerEquivalent R B A := by
  sorry







theorem azumayaBrauerEquivalent_trans
    (R : Type u) [CommRing R] (A B C : AzumayaAlgebra R)
    (hAB : AzumayaBrauerEquivalent R A B)
    (hBC : AzumayaBrauerEquivalent R B C) :
    AzumayaBrauerEquivalent R A C := by
  sorry























def azumayaBrauerSetoid
    (R : Type u) [CommRing R] :
    Setoid (AzumayaAlgebra R) where
  r := AzumayaBrauerEquivalent R
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro A
      exact azumayaBrauerEquivalent_refl R A
    · intro A B hAB
      exact azumayaBrauerEquivalent_symm R A B hAB
    · intro A B C hAB hBC
      exact azumayaBrauerEquivalent_trans R A B C hAB hBC








abbrev AzumayaBrauerGroup
    (R : Type u) [CommRing R] : Type (u + 1) :=
  Quotient (azumayaBrauerSetoid R)

namespace AzumayaBrauerClass








def IsTensorProduct
    (R : Type u) [CommRing R]
    (x y z : AzumayaBrauerGroup R) : Prop :=
  ∃ A B C : AzumayaAlgebra R,
    Quotient.mk (azumayaBrauerSetoid R) A = x ∧
      Quotient.mk (azumayaBrauerSetoid R) B = y ∧
        Quotient.mk (azumayaBrauerSetoid R) C = z ∧
          Nonempty ((A.carrier ⊗[R] B.carrier) ≃ₐ[R] C.carrier)

end AzumayaBrauerClass

namespace FieldBrauerClass








def IsTensorProduct
    (K : Type u) [Field K]
    (x y z : BrauerGroup.{u, u} K) : Prop :=
  ∃ A B C : CSA.{u, u} K,
    csaToBrauerClass A = x ∧
      csaToBrauerClass B = y ∧
        csaToBrauerClass C = z ∧
          Nonempty ((A ⊗[K] B) ≃ₐ[K] C)

end FieldBrauerClass





structure AzumayaBrauerGroupAdditiveLaw
    (R : Type u) [CommRing R] where
  addCommGroup : AddCommGroup (AzumayaBrauerGroup R)
  addition_is_tensorProduct :
    letI := addCommGroup
    ∀ x y : AzumayaBrauerGroup R,
      AzumayaBrauerClass.IsTensorProduct R x y (x + y)





structure FieldBrauerGroupAdditiveLaw
    (K : Type u) [Field K] where
  addCommGroup : AddCommGroup (BrauerGroup.{u, u} K)
  addition_is_tensorProduct :
    letI := addCommGroup
    ∀ x y : BrauerGroup.{u, u} K,
      FieldBrauerClass.IsTensorProduct K x y (x + y)






def IsGenericFiberMap
    (R F : Type u)
    [CommRing R] [Field F] [Algebra R F]
    (f : AzumayaBrauerGroup R → BrauerGroup.{u, u} F) : Prop :=
  ∀ A : AzumayaAlgebra R,
    ∃ B : CSA.{u, u} F,
      csaToBrauerClass B =
          f (Quotient.mk (azumayaBrauerSetoid R) A) ∧
        IsGenericFiberRepresentative A B











structure BrauerGenericFiberInjection
    (R F : Type u)
    [CommRing R] [Field F] [Algebra R F] where
  domainLaw : AzumayaBrauerGroupAdditiveLaw R
  codomainLaw : FieldBrauerGroupAdditiveLaw F
  genericFiberHom :
    letI := domainLaw.addCommGroup
    letI := codomainLaw.addCommGroup
    AzumayaBrauerGroup R →+ BrauerGroup.{u, u} F
  genericFiber_map :
    letI := domainLaw.addCommGroup
    letI := codomainLaw.addCommGroup
    IsGenericFiberMap R F genericFiberHom.toFun
  injective :
    letI := domainLaw.addCommGroup
    letI := codomainLaw.addCommGroup
    Function.Injective genericFiberHom.toFun











theorem theorem_19_5_brauer_injective_to_fractionField
    (k R F : Type u)
    [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [Algebra k R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Algebra.FiniteType k R]
    (h_smooth : Algebra.FormallySmooth k R) :
    Nonempty (BrauerGenericFiberInjection R F) := by
  sorry

end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_19_5_brauer_injective_to_fractionField

