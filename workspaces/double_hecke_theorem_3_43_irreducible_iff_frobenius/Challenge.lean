/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.RingQuot
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.BigOperators

open Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_43_irreducible_iff_frobenius
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_43_irreducible_iff_frobenius

universe u v






























attribute [instance] FiniteOrthogonalLinearGroup.instGroup
attribute [instance] FiniteOrthogonalLinearGroup.instFintype











theorem mulByPolynomial_map_smul {n : ℕ} (p : PolyH n) (a : ℂ) (q : PolyH n) :
    p * a • q = (RingHom.id ℂ) a • (p * q) := by
  sorry















noncomputable def mulByPolynomial {n : ℕ}
    (p : PolyH n) : Module.End ℂ (PolyH n) where
  toFun := fun q => p * q
  map_add' := by
    intro q r
    simp [mul_add]
  map_smul' := mulByPolynomial_map_smul p





noncomputable def polynomialXAction {n : ℕ}
    (x : Vec n →ₗ[ℂ] ℂ) : Module.End ℂ (PolyH n) :=
  mulByPolynomial (linearFormPolynomial x)




theorem directionalDerivative_map_add {n : ℕ} (y : Vec n) (p q : PolyH n) :
    ∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.pderiv i (p + q) =
      (∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.pderiv i p) +
        ∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.pderiv i q := by
  sorry





theorem directionalDerivative_map_smul {n : ℕ} (y : Vec n) (a : ℂ) (p : PolyH n) :
    ∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.pderiv i (a • p) =
      (RingHom.id ℂ) a • ∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.pderiv i p := by
  sorry









attribute [instance] ReflectionSystem.instFintype









noncomputable def directionalDerivative {n : ℕ}
    (y : Vec n) : Module.End ℂ (PolyH n) where
  toFun := fun p =>
    ∑ i : Fin n,
      MvPolynomial.C (y i) * MvPolynomial.pderiv i p
  map_add' := directionalDerivative_map_add y
  map_smul' := directionalDerivative_map_smul y






theorem exists_reflectionDifferenceQuotient {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (s : RS.S)
    (p : PolyH n) :
    ∃ q : PolyH n,
      alphaPolynomial RS s * q =
        p - polynomialGActionAlgHom Γ (RS.refl s).elt p := by
  sorry








noncomputable def reflectionDifferenceQuotient {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (s : RS.S)
    (p : PolyH n) : PolyH n :=
  Classical.choose (exists_reflectionDifferenceQuotient Γ RS s p)

theorem alphaPolynomial_mul_reflectionDifferenceQuotient {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (s : RS.S)
    (p : PolyH n) :
    alphaPolynomial RS s *
        reflectionDifferenceQuotient Γ RS s p =
      p - polynomialGActionAlgHom Γ (RS.refl s).elt p := by
  exact Classical.choose_spec
    (exists_reflectionDifferenceQuotient Γ RS s p)





theorem polynomialYAction_map_add {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (y : Vec n) (p q : PolyH n) :
    directionalDerivative y (p + q) -
        ∑ s : RS.S,
          MvPolynomial.C
              ((2 * RS.param s * ((RS.refl s).alpha y)) /
                ((1 : ℂ) - (RS.refl s).eig)) *
            reflectionDifferenceQuotient Γ RS s (p + q) =
      (directionalDerivative y p -
          ∑ s : RS.S,
            MvPolynomial.C
                ((2 * RS.param s * ((RS.refl s).alpha y)) /
                  ((1 : ℂ) - (RS.refl s).eig)) *
              reflectionDifferenceQuotient Γ RS s p) +
        (directionalDerivative y q -
          ∑ s : RS.S,
            MvPolynomial.C
                ((2 * RS.param s * ((RS.refl s).alpha y)) /
                  ((1 : ℂ) - (RS.refl s).eig)) *
              reflectionDifferenceQuotient Γ RS s q) := by
  sorry





theorem polynomialYAction_map_smul {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (y : Vec n) (a : ℂ) (p : PolyH n) :
    directionalDerivative y (a • p) -
        ∑ s : RS.S,
          MvPolynomial.C
              ((2 * RS.param s * ((RS.refl s).alpha y)) /
                ((1 : ℂ) - (RS.refl s).eig)) *
            reflectionDifferenceQuotient Γ RS s (a • p) =
      (RingHom.id ℂ) a •
        (directionalDerivative y p -
          ∑ s : RS.S,
            MvPolynomial.C
                ((2 * RS.param s * ((RS.refl s).alpha y)) /
                  ((1 : ℂ) - (RS.refl s).eig)) *
              reflectionDifferenceQuotient Γ RS s p) := by
  sorry










































noncomputable def polynomialYAction {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (y : Vec n) : Module.End ℂ (PolyH n) where
  toFun := fun p =>
    directionalDerivative y p -
      ∑ s : RS.S,
        MvPolynomial.C
            ((2 * RS.param s * ((RS.refl s).alpha y)) /
              ((1 : ℂ) - (RS.refl s).eig)) *
          reflectionDifferenceQuotient Γ RS s p
  map_add' := polynomialYAction_map_add Γ RS y
  map_smul' := polynomialYAction_map_smul Γ RS y






theorem exists_polynomialRepresentation {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ) :
    ∃ Rep : H1cCherednikAlgebra Γ RS →ₐ[ℂ] Module.End ℂ (PolyH n),
      (∀ x : Vec n →ₗ[ℂ] ℂ,
        Rep (h1cX (RS := RS) x) = polynomialXAction x) ∧
      (∀ y : Vec n,
        Rep (h1cY (RS := RS) y) = polynomialYAction Γ RS y) ∧
      (∀ g : Γ.G,
        Rep (h1cG (RS := RS) g) = polynomialGAction Γ g) := by
  sorry



































noncomputable def polynomialRepresentation {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ) :
    H1cCherednikAlgebra Γ RS →ₐ[ℂ] Module.End ℂ (PolyH n) :=
  Classical.choose (exists_polynomialRepresentation Γ RS)







structure PolynomialIdeal (n : ℕ) where
  carrier : PolyH n → Prop
  zero_mem : carrier 0
  add_mem :
    ∀ {p q : PolyH n}, carrier p → carrier q → carrier (p + q)
  neg_mem :
    ∀ {p : PolyH n}, carrier p → carrier (-p)
  mul_left_mem :
    ∀ (r : PolyH n) {p : PolyH n}, carrier p → carrier (r * p)
  mul_right_mem :
    ∀ (r : PolyH n) {p : PolyH n}, carrier p → carrier (p * r)





def PolynomialIdeal.rel {n : ℕ}
    (J : PolynomialIdeal n) (p q : PolyH n) : Prop :=
  J.carrier (p - q)





abbrev PolynomialQuotient {n : ℕ}
    (J : PolynomialIdeal n) : Type :=
  RingQuot (PolynomialIdeal.rel J)





noncomputable def polynomialQuotientMap {n : ℕ}
    (J : PolynomialIdeal n) : PolyH n →ₐ[ℂ] PolynomialQuotient J :=
  RingQuot.mkAlgHom ℂ (PolynomialIdeal.rel J)







def QuotientHomogeneous {n : ℕ}
    (J : PolynomialIdeal n) (d : ℕ) (a : PolynomialQuotient J) : Prop :=
  ∃ p : PolyH n,
    polynomialQuotientMap J p = a ∧ IsHomogeneousPolynomial d p





def QuotientHasHomogeneousDecomposition {n : ℕ}
    (J : PolynomialIdeal n) : Prop :=
  ∀ a : PolynomialQuotient J,
    ∃ ι : Type, ∃ hι : Fintype ι,
    ∃ d : ι → ℕ, ∃ b : ι → PolynomialQuotient J,
      letI := hι
      (∀ i : ι, QuotientHomogeneous J (d i) (b i)) ∧
        a = ∑ i : ι, b i










def QuotientHomogeneousDecompositionDirect {n : ℕ}
    (J : PolynomialIdeal n) : Prop :=
  ∀ (ι : Type) [Fintype ι]
    (d : ι → ℕ) (b : ι → PolynomialQuotient J),
      Function.Injective d →
        (∀ i : ι, QuotientHomogeneous J (d i) (b i)) →
          (∑ i : ι, b i) = 0 →
            ∀ i : ι, b i = 0





def PolynomialIdeal.IsProper {n : ℕ}
    (J : PolynomialIdeal n) : Prop :=
  ¬ J.carrier 1






def PolynomialIdeal.IsHomogeneous {n : ℕ}
    (J : PolynomialIdeal n) : Prop :=
  ∀ p : PolyH n,
    J.carrier p →
      ∃ ι : Type, ∃ hι : Fintype ι, ∃ q : ι → PolyH n,
        letI := hι
        (∀ i : ι, J.carrier (q i)) ∧
          (∀ i : ι, ∃ d : ℕ, IsHomogeneousPolynomial d (q i)) ∧
            p = ∑ i : ι, q i







def PolynomialIdeal.IsHStable {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (J : PolynomialIdeal n) : Prop :=
  ∀ h : H1cCherednikAlgebra Γ RS,
    ∀ p : PolyH n,
      J.carrier p →
        J.carrier (polynomialRepresentation Γ RS h p)







theorem exists_inducedPolynomialQuotientAction {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (J : PolynomialIdeal n)
    (hstable : J.IsHStable Γ RS) :
    ∃ ρ : H1cCherednikAlgebra Γ RS →ₐ[ℂ]
        Module.End ℂ (PolynomialQuotient J),
      ∀ (h : H1cCherednikAlgebra Γ RS) (p : PolyH n),
        ρ h (polynomialQuotientMap J p) =
          polynomialQuotientMap J (polynomialRepresentation Γ RS h p) := by
  sorry





































noncomputable def inducedPolynomialQuotientAction {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (J : PolynomialIdeal n)
    (hstable : J.IsHStable Γ RS) :
    H1cCherednikAlgebra Γ RS →ₐ[ℂ]
      Module.End ℂ (PolynomialQuotient J) :=
  Classical.choose
    (exists_inducedPolynomialQuotientAction Γ RS J hstable)






structure FiniteDimensionalPolynomialRepresentationQuotient {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ) where
  J : PolynomialIdeal n
  proper : J.IsProper
  homogeneous : J.IsHomogeneous
  stable : J.IsHStable Γ RS
  finite_dimensional :
    FiniteDimensionalOverC (PolynomialQuotient J)
  homogeneous_decomposition :
    QuotientHasHomogeneousDecomposition J
  homogeneous_decomposition_direct :
    QuotientHomogeneousDecompositionDirect J


noncomputable def FiniteDimensionalPolynomialRepresentationQuotient.quotientAction
    {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (Q : FiniteDimensionalPolynomialRepresentationQuotient Γ RS) :
    H1cCherednikAlgebra Γ RS →ₐ[ℂ]
      Module.End ℂ (PolynomialQuotient Q.J) :=
  inducedPolynomialQuotientAction Γ RS Q.J Q.stable





structure QuotientHSubmodule {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (Q : FiniteDimensionalPolynomialRepresentationQuotient Γ RS) where
  carrier : PolynomialQuotient Q.J → Prop
  zero_mem : carrier 0
  add_mem :
    ∀ {a b : PolynomialQuotient Q.J}, carrier a → carrier b → carrier (a + b)
  smul_mem :
    ∀ (c : ℂ) {a : PolynomialQuotient Q.J}, carrier a → carrier (c • a)
  action_mem :
    ∀ (h : H1cCherednikAlgebra Γ RS) {a : PolynomialQuotient Q.J},
      carrier a → carrier (Q.quotientAction h a)


def QuotientHSubmoduleEq {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    {Q : FiniteDimensionalPolynomialRepresentationQuotient Γ RS}
    (P R : QuotientHSubmodule Q) : Prop :=
  ∀ a : PolynomialQuotient Q.J, P.carrier a ↔ R.carrier a





def zeroQuotientHSubmodule {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (Q : FiniteDimensionalPolynomialRepresentationQuotient Γ RS) :
    QuotientHSubmodule Q where
  carrier := fun a => a = 0
  zero_mem := rfl
  add_mem := by
    intro a b ha hb
    rw [ha, hb, zero_add]
  smul_mem := by
    intro c a ha
    rw [ha, smul_zero]
  action_mem := by
    intro h a ha
    rw [ha]
    exact map_zero (Q.quotientAction h)





def topQuotientHSubmodule {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (Q : FiniteDimensionalPolynomialRepresentationQuotient Γ RS) :
    QuotientHSubmodule Q where
  carrier := fun _ => True
  zero_mem := trivial
  add_mem := by
    intro a b ha hb
    trivial
  smul_mem := by
    intro c a ha
    trivial
  action_mem := by
    intro h a ha
    trivial






def IsIrreduciblePolynomialRepresentationQuotient {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (Q : FiniteDimensionalPolynomialRepresentationQuotient Γ RS) : Prop :=
  ∀ P : QuotientHSubmodule Q,
    QuotientHSubmoduleEq P (zeroQuotientHSubmodule Q) ∨
      QuotientHSubmoduleEq P (topQuotientHSubmodule Q)





def QuotientMultiplicationCommutative {n : ℕ}
    (J : PolynomialIdeal n) : Prop :=
  ∀ a b : PolynomialQuotient J, a * b = b * a





def QuotientGradingMultiplicative {n : ℕ}
    (J : PolynomialIdeal n) : Prop :=
  ∀ d e : ℕ,
    ∀ a b : PolynomialQuotient J,
      QuotientHomogeneous J d a →
        QuotientHomogeneous J e b →
          QuotientHomogeneous J (d + e) (a * b)





def TopDegreeOneDimensional {n : ℕ}
    (J : PolynomialIdeal n) (top : ℕ) : Prop :=
  ∃ ω : PolynomialQuotient J,
    QuotientHomogeneous J top ω ∧
      ω ≠ 0 ∧
        (∀ a : PolynomialQuotient J,
          QuotientHomogeneous J top a → ∃ c : ℂ, a = c • ω) ∧
          (∀ d : ℕ,
            top < d →
              ∀ a : PolynomialQuotient J,
                QuotientHomogeneous J d a → a = 0)






def FrobeniusPairingNondegenerate {n : ℕ}
    (J : PolynomialIdeal n) (top m : ℕ) : Prop :=
  (∀ a : PolynomialQuotient J,
      QuotientHomogeneous J m a →
        a ≠ 0 →
          ∃ b : PolynomialQuotient J,
            QuotientHomogeneous J (top - m) b ∧ a * b ≠ 0) ∧
    (∀ b : PolynomialQuotient J,
      QuotientHomogeneous J (top - m) b →
        b ≠ 0 →
          ∃ a : PolynomialQuotient J,
            QuotientHomogeneous J m a ∧ a * b ≠ 0)





def IsFrobeniusPolynomialQuotient {n : ℕ}
    (J : PolynomialIdeal n) : Prop :=
  QuotientMultiplicationCommutative J ∧
    QuotientHasHomogeneousDecomposition J ∧
      QuotientHomogeneousDecompositionDirect J ∧
        QuotientGradingMultiplicative J ∧
          ∃ top : ℕ,
            TopDegreeOneDimensional J top ∧
              ∀ m : ℕ, m ≤ top → FrobeniusPairingNondegenerate J top m









theorem theorem_3_43_irreducible_iff_frobenius {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ)
    (Q : FiniteDimensionalPolynomialRepresentationQuotient Γ RS) :
    IsIrreduciblePolynomialRepresentationQuotient Q ↔
      IsFrobeniusPolynomialQuotient Q.J := by
  sorry

end Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_43_irreducible_iff_frobenius

end