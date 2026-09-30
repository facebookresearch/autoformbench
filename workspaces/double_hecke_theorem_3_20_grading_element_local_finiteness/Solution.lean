


import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.RingQuot
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Submission
import ChallengeDeps
noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness






























attribute [instance] FiniteLinearGroup.instGroup
attribute [instance] FiniteLinearGroup.instFintype



















attribute [instance] ReflectionSystem.instFintype













































noncomputable def H1cModuleAction.xOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (x : Vec n →ₗ[ℂ] ℂ) : Module.End ℂ M :=
  A.rep (h1cX (RS := RS) x)





























theorem gradingElement_commutator_x {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ)
    (x : Vec n →ₗ[ℂ] ℂ) :
    commutator (gradingElement Γ RS) (h1cX (RS := RS) x) =
      h1cX (RS := RS) x := Submission.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.gradingElement_commutator_x Γ RS x





theorem gradingElement_commutator_y {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ)
    (y : Vec n) :
    commutator (gradingElement Γ RS) (h1cY (RS := RS) y) =
      -h1cY (RS := RS) y := Submission.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.gradingElement_commutator_y Γ RS y





theorem theorem_3_20_grading_element_local_finiteness {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ)
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) :
    (LieHActsLocallyNilpotently A →
      LinearOperatorLocallyFinite A.gradingOp) ∧
    (FinitelyGeneratedOverSymHStar A →
      (InCategoryOZero A ↔
        LinearOperatorLocallyFinite A.gradingOp)) := Submission.Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness.theorem_3_20_grading_element_local_finiteness Γ RS A

end Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness

end
