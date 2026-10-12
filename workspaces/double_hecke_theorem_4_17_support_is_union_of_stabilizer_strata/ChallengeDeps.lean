/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_4_17_support_is_union_of_stabilizer_strata

universe u v w
























abbrev Vec (r : ℕ) : Type :=
  Fin r → ℂ






abbrev RealVec (r : ℕ) : Type :=
  Fin r → ℝ


def realToComplexVec {r : ℕ} (x : RealVec r) : Vec r :=
  fun i => (x i : ℂ)


def stdBasisVec (r : ℕ) (i : Fin r) : Vec r :=
  fun j => if j = i then 1 else 0


def stdBasisRealVec (r : ℕ) (i : Fin r) : RealVec r :=
  fun j => if j = i then 1 else 0






abbrev PolyH (r : ℕ) : Type :=
  MvPolynomial (Fin r) ℂ






abbrev SymH (r : ℕ) : Type :=
  MvPolynomial (Fin r) ℂ






noncomputable def linearFormPolynomial {r : ℕ}
    (x : Vec r →ₗ[ℂ] ℂ) : PolyH r :=
  ∑ i : Fin r,
    MvPolynomial.C (x (stdBasisVec r i)) * MvPolynomial.X i





noncomputable def vecAsYPolynomial {r : ℕ} (y : Vec r) : SymH r :=
  ∑ i : Fin r, MvPolynomial.C (y i) * MvPolynomial.X i














structure FiniteCoxeterComplexData (r : ℕ) where
  W : Type u
  [instGroup : Group W]
  [instFintypeW : Fintype W]

  
  rho : W →* (Vec r ≃ₗ[ℂ] Vec r)
  rho_injective : Function.Injective rho

  
  rhoReal : W →* (RealVec r ≃ₗ[ℝ] RealVec r)

  
  rho_complexifies_rhoReal :
    ∀ (g : W) (z : Vec r) (i : Fin r),
      rho g z i =
        ∑ j : Fin r,
          ((rhoReal g (stdBasisRealVec r j)) i : ℂ) * z j

  
  realInner : RealVec r → RealVec r → ℝ
  realInner_add_left :
    ∀ x y z : RealVec r, realInner (x + y) z = realInner x z + realInner y z
  realInner_smul_left :
    ∀ (a : ℝ) (x y : RealVec r), realInner (a • x) y = a * realInner x y
  realInner_symm :
    ∀ x y : RealVec r, realInner x y = realInner y x
  realInner_self_nonneg :
    ∀ x : RealVec r, 0 ≤ realInner x x
  realInner_eq_zero_iff :
    ∀ x : RealVec r, realInner x x = 0 ↔ x = 0

  
  rhoReal_orthogonal :
    ∀ (g : W) (x y : RealVec r),
      realInner (rhoReal g x) (rhoReal g y) = realInner x y

  Reflection : Type v
  [instFintypeReflection : Fintype Reflection]
  reflElt : Reflection → W

  
  alpha : Reflection → Vec r →ₗ[ℂ] ℂ
  coroot : Reflection → Vec r
  alpha_coroot :
    ∀ s : Reflection, alpha s (coroot s) = 2

  
  realAlpha : Reflection → RealVec r →ₗ[ℝ] ℝ
  realCoroot : Reflection → RealVec r
  realAlpha_coroot :
    ∀ s : Reflection, realAlpha s (realCoroot s) = 2
  realAlpha_complexifies_alpha :
    ∀ (s : Reflection) (x : RealVec r),
      alpha s (realToComplexVec x) = (realAlpha s x : ℂ)
  realCoroot_complexifies_coroot :
    ∀ s : Reflection, coroot s = realToComplexVec (realCoroot s)

  
  real_reflection_formula :
    ∀ (s : Reflection) (x : RealVec r),
      rhoReal (reflElt s) x = x - ((realAlpha s x) • realCoroot s)

  
  reflection_formula :
    ∀ (s : Reflection) (x : Vec r),
      rho (reflElt s) x = x - ((alpha s x) • coroot s)

  refl_elt_injective :
    Function.Injective reflElt

  
  refl_exact :
    ∀ g : W,
      (∃ alpha : Vec r →ₗ[ℂ] ℂ,
       ∃ coroot : Vec r,
        alpha coroot = 2 ∧
          ∀ x : Vec r, rho g x = x - ((alpha x) • coroot)) ↔
        ∃ s : Reflection, reflElt s = g

  
  generated_by_reflections :
    ∀ g : W, ∃ L : List Reflection, (L.map reflElt).prod = g

attribute [instance] FiniteCoxeterComplexData.instGroup
attribute [instance] FiniteCoxeterComplexData.instFintypeW
attribute [instance] FiniteCoxeterComplexData.instFintypeReflection





def actVec {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (w : C.W) (x : Vec r) : Vec r :=
  C.rho w x







noncomputable def actCovec {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (w : C.W)
    (ξ : Vec r →ₗ[ℂ] ℂ) : Vec r →ₗ[ℂ] ℂ :=
  ξ.comp (C.rho (w⁻¹)).toLinearMap









inductive H1cGen {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r) where
  | X : (Vec r →ₗ[ℂ] ℂ) → H1cGen C
  | Y : Vec r → H1cGen C
  | G : C.W → H1cGen C





abbrev H1cFreeAlgebra {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r) : Type _ :=
  FreeAlgebra ℂ (H1cGen C)


noncomputable def gen {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    (a : H1cGen C) : H1cFreeAlgebra C :=
  FreeAlgebra.ι ℂ a





noncomputable def genX {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    (ξ : Vec r →ₗ[ℂ] ℂ) : H1cFreeAlgebra C :=
  gen (H1cGen.X ξ)





noncomputable def genY {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    (y : Vec r) : H1cFreeAlgebra C :=
  gen (H1cGen.Y y)





noncomputable def genG {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    (w : C.W) : H1cFreeAlgebra C :=
  gen (H1cGen.G w)


noncomputable def scalarC {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    (z : ℂ) : H1cFreeAlgebra C :=
  algebraMap ℂ (H1cFreeAlgebra C) z





def commutator {A : Type _} [Ring A] (a b : A) : A :=
  a * b - b * a







def equalCherednikParameter {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (c : ℂ) : C.Reflection → ℂ :=
  fun _ => c









noncomputable def yxCherednikRHSAtOne {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    (c : ℂ)
    (y : Vec r) (ξ : Vec r →ₗ[ℂ] ℂ) : H1cFreeAlgebra C :=
  scalarC (ξ y) -
    ∑ s : C.Reflection,
      scalarC ((equalCherednikParameter C c s) * C.alpha s y * ξ (C.coroot s)) *
        genG (C.reflElt s)






inductive h1cRel {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (c : ℂ) :
    H1cFreeAlgebra C → H1cFreeAlgebra C → Prop
  | x_add (ξ η : Vec r →ₗ[ℂ] ℂ) :
      h1cRel C c
        (genX (ξ + η))
        (genX ξ + genX η)
  | x_smul (a : ℂ) (ξ : Vec r →ₗ[ℂ] ℂ) :
      h1cRel C c
        (genX (a • ξ))
        (scalarC a * genX ξ)
  | y_add (y z : Vec r) :
      h1cRel C c
        (genY (y + z))
        (genY y + genY z)
  | y_smul (a : ℂ) (y : Vec r) :
      h1cRel C c
        (genY (a • y))
        (scalarC a * genY y)
  | group_unit :
      h1cRel C c
        (genG (C := C) 1)
        1
  | group_mul (g h : C.W) :
      h1cRel C c
        (genG (C := C) g * genG h)
        (genG (g * h))
  | group_act_x (g : C.W) (ξ : Vec r →ₗ[ℂ] ℂ) :
      h1cRel C c
        (genG (C := C) g * genX ξ * genG g⁻¹)
        (genX (actCovec C g ξ))
  | group_act_y (g : C.W) (y : Vec r) :
      h1cRel C c
        (genG (C := C) g * genY y * genG g⁻¹)
        (genY (actVec C g y))
  | xx (ξ η : Vec r →ₗ[ℂ] ℂ) :
      h1cRel C c
        (commutator (genX ξ) (genX η))
        0
  | yy (y z : Vec r) :
      h1cRel C c
        (commutator (genY y) (genY z))
        0
  | yx (y : Vec r) (ξ : Vec r →ₗ[ℂ] ℂ) :
      h1cRel C c
        (commutator (genY y) (genX ξ))
        (yxCherednikRHSAtOne (C := C) c y ξ)





abbrev H1cCherednikAlgebra {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (c : ℂ) : Type _ :=
  RingQuot (h1cRel C c)





noncomputable def h1cQuotientMap {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (c : ℂ) :
    H1cFreeAlgebra C →ₐ[ℂ] H1cCherednikAlgebra C c :=
  RingQuot.mkAlgHom ℂ (h1cRel C c)


noncomputable def h1cX {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    {c : ℂ}
    (ξ : Vec r →ₗ[ℂ] ℂ) : H1cCherednikAlgebra C c :=
  h1cQuotientMap C c (genX ξ)


noncomputable def h1cY {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    {c : ℂ}
    (y : Vec r) : H1cCherednikAlgebra C c :=
  h1cQuotientMap C c (genY y)







def FinitelyGeneratedOverPolynomialAction {r : ℕ}
    {M : Type w} [AddCommGroup M] [Module ℂ M]
    (A : PolyH r →ₐ[ℂ] Module.End ℂ M) : Prop :=
  ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → M,
    letI := hι
    ∀ m : M,
      ∃ coeff : ι → PolyH r,
        m = ∑ i : ι, A (coeff i) (b i)







def LocallyFiniteUnderPolynomialAction {r : ℕ}
    {M : Type w} [AddCommGroup M] [Module ℂ M]
    (A : SymH r →ₐ[ℂ] Module.End ℂ M) : Prop :=
  ∀ m : M,
    ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → M,
      letI := hι
      ∀ p : SymH r,
        ∃ coeff : ι → ℂ,
          A p m = ∑ i : ι, coeff i • b i











structure CategoryOObject {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (c : ℂ) where
  M : Type w
  [instAddCommGroup : AddCommGroup M]
  [instModule : Module ℂ M]
  rep : H1cCherednikAlgebra C c →ₐ[ℂ] Module.End ℂ M

  xPolyOp : PolyH r →ₐ[ℂ] Module.End ℂ M
  yPolyOp : SymH r →ₐ[ℂ] Module.End ℂ M

  xPolyOp_linear :
    ∀ ξ : Vec r →ₗ[ℂ] ℂ,
      xPolyOp (linearFormPolynomial ξ) = rep (h1cX (C := C) (c := c) ξ)
  yPolyOp_linear :
    ∀ y : Vec r,
      yPolyOp (vecAsYPolynomial y) = rep (h1cY (C := C) (c := c) y)

  finitelyGeneratedOverShStar :
    FinitelyGeneratedOverPolynomialAction xPolyOp
  locallyFiniteUnderSh :
    LocallyFiniteUnderPolynomialAction yPolyOp

attribute [instance] CategoryOObject.instAddCommGroup
attribute [instance] CategoryOObject.instModule







def PolynomialAnnihilatesCategoryOObject {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    {c : ℂ}
    (M : CategoryOObject C c)
    (p : PolyH r) : Prop :=
  ∀ m : M.M, M.xPolyOp p m = 0









noncomputable def polynomialEvalAt {r : ℕ}
    (x : Vec r) (p : PolyH r) : ℂ :=
  MvPolynomial.eval₂ (RingHom.id ℂ) x p










def CategoryOObjectSupport {r : ℕ}
    {C : FiniteCoxeterComplexData.{u, v} r}
    {c : ℂ}
    (M : CategoryOObject C c) : Set (Vec r) :=
  fun x =>
    ∀ p : PolyH r,
      PolynomialAnnihilatesCategoryOObject M p →
        polynomialEvalAt x p = 0





def PointStabilizerPredicate {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (x : Vec r) : C.W → Prop :=
  fun g => C.rho g x = x






def IsParabolicSubgroup {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (W' : Subgroup C.W) : Prop :=
  ∃ a : Vec r, ∀ g : C.W, g ∈ W' ↔ PointStabilizerPredicate C a g







def hRegParabolicStratum {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (W' : Subgroup C.W) : Set (Vec r) :=
  fun x => ∀ g : C.W, g ∈ W' ↔ PointStabilizerPredicate C x g


def StabilizerStratum {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (W' : Subgroup C.W) : Set (Vec r) :=
  hRegParabolicStratum C W'









def IsUnionOfStabilizerStrata {r : ℕ}
    (C : FiniteCoxeterComplexData.{u, v} r)
    (S : Set (Vec r)) : Prop :=
  ∃ strata : Set (Subgroup C.W),
    ∀ x : Vec r,
      S x ↔
        ∃ W' : Subgroup C.W,
          W' ∈ strata ∧
            IsParabolicSubgroup C W' ∧
              StabilizerStratum C W' x



end Autoform_Double_Hecke_Algebras_double_hecke_theorem_4_17_support_is_union_of_stabilizer_strata
