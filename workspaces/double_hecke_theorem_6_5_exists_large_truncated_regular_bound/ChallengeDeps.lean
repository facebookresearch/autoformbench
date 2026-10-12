/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_6_5_exists_large_truncated_regular_bound

universe u v w



















abbrev Vec (n : ℕ) : Type :=
  Fin n → ℂ


abbrev PolyH (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ


abbrev SymH (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ


def zeroVec (n : ℕ) : Vec n :=
  fun _ => 0


def vecSub {n : ℕ} (x y : Vec n) : Vec n :=
  fun i => x i - y i


def vecScale {n : ℕ} (a : ℂ) (x : Vec n) : Vec n :=
  fun i => a * x i


noncomputable def polynomialEvalAt {n : ℕ}
    (x : Vec n) (p : MvPolynomial (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval₂ (RingHom.id ℂ) x p


def stdBasisVec (n : ℕ) (i : Fin n) : Vec n :=
  fun j => if j = i then 1 else 0


def coordLinear (n : ℕ) (i : Fin n) : Vec n →ₗ[ℂ] ℂ where
  toFun := fun x => x i
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl


noncomputable def covecOfCoords {n : ℕ} (η : Vec n) :
    Vec n →ₗ[ℂ] ℂ :=
  ∑ i : Fin n, η i • coordLinear n i


def coordsOfCovec {n : ℕ}
    (x : Vec n →ₗ[ℂ] ℂ) : Vec n :=
  fun i => x (stdBasisVec n i)


noncomputable def linearFormPolynomial {n : ℕ}
    (x : Vec n →ₗ[ℂ] ℂ) : PolyH n :=
  ∑ i : Fin n,
    MvPolynomial.C (x (stdBasisVec n i)) * MvPolynomial.X i


noncomputable def vecAsYPolynomial {n : ℕ} (y : Vec n) : SymH n :=
  ∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.X i


noncomputable def twoPiI : ℂ :=
  (2 : ℂ) * (Real.pi : ℂ) * Complex.I


noncomputable def cyclotomicExp (m : ℕ) (a : ℕ) : ℂ :=
  Complex.exp (twoPiI * (a : ℂ) / (m : ℂ))







def IsRankOneNontrivialAction {n : ℕ} {G : Type u} [Group G]
    (rho : G →* (Vec n ≃ₗ[ℂ] Vec n)) (g : G) : Prop :=
  g ≠ 1 ∧
    ∃ normal : Vec n,
      normal ≠ 0 ∧
        ∀ x : Vec n,
          ∃ a : ℂ, vecSub x (rho g x) = vecScale a normal


structure ComplexReflectionKZData (n : ℕ) where
  G : Type u
  [instGroupG : Group G]
  [instFintypeG : Fintype G]

  rho : G →* (Vec n ≃ₗ[ℂ] Vec n)
  rho_injective : Function.Injective rho

  Hyperplane : Type v
  [instFintypeHyperplane : Fintype Hyperplane]

  alphaH : Hyperplane → Vec n →ₗ[ℂ] ℂ
  corootH : Hyperplane → Vec n
  alphaH_corootH :
    ∀ H : Hyperplane, alphaH H (corootH H) = 2

  sH : Hyperplane → G

  mH : Hyperplane → ℕ
  mH_gt_one : ∀ H : Hyperplane, 1 < mH H

  sH_pow_mH :
    ∀ H : Hyperplane, (sH H) ^ (mH H) = 1

  sH_power_injective :
    ∀ H : Hyperplane,
      Function.Injective (fun ℓ : Fin (mH H) => (sH H) ^ ℓ.val)

  
  reflection_hyperplanes_exhaustive :
    ∀ g : G,
      IsRankOneNontrivialAction rho g ↔
        ∃ H : Hyperplane, ∃ ℓ : Fin (mH H),
          ℓ.val ≠ 0 ∧ g = (sH H) ^ ℓ.val

  
  reflections_generate :
    Subgroup.closure
        {g : G | IsRankOneNontrivialAction rho g} = ⊤

  pointwise_stabilizer_exact :
    ∀ (H : Hyperplane) (g : G),
      ((∀ x : Vec n, alphaH H x = 0 → rho g x = x) ↔
        ∃ ℓ : Fin (mH H), g = (sH H) ^ ℓ.val)

  reflection_power_formula :
    ∀ (H : Hyperplane) (ℓ : Fin (mH H)) (x : Vec n),
      rho ((sH H) ^ ℓ.val) x =
        vecSub x
          (vecScale
            ((((1 : ℂ) - (cyclotomicExp (mH H) ℓ.val)⁻¹) / 2) *
              (alphaH H x))
            (corootH H))

  
  cPower : ∀ H : Hyperplane, Fin (mH H) → ℂ

  
  cPower_conj_invariant :
    ∀ (g : G) (H H' : Hyperplane)
      (ℓ : Fin (mH H)) (ℓ' : Fin (mH H')),
      ℓ.val ≠ 0 →
      ℓ'.val ≠ 0 →
      (sH H') ^ ℓ'.val = g * (sH H) ^ ℓ.val * g⁻¹ →
        cPower H' ℓ' = cPower H ℓ

attribute [instance] ComplexReflectionKZData.instGroupG
attribute [instance] ComplexReflectionKZData.instFintypeG
attribute [instance] ComplexReflectionKZData.instFintypeHyperplane


def actVec {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n)
    (g : C.G) (x : Vec n) : Vec n :=
  C.rho g x


noncomputable def actCovec {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n)
    (g : C.G)
    (x : Vec n →ₗ[ℂ] ℂ) : Vec n →ₗ[ℂ] ℂ :=
  x.comp (C.rho (g⁻¹)).toLinearMap


noncomputable def dualPointAction {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n)
    (g : C.G)
    (η : Vec n) : Vec n :=
  coordsOfCovec (actCovec C g (covecOfCoords η))


structure InvariantYPolynomial {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n) where
  poly : SymH n
  invariant :
    ∀ (g : C.G) (η : Vec n),
      polynomialEvalAt (dualPointAction C g η) poly =
        polynomialEvalAt η poly


noncomputable def invariantYPolynomialZeroEval {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    (Q : InvariantYPolynomial C) : ℂ :=
  polynomialEvalAt (zeroVec n) Q.poly


def commutator {A : Type _} [Ring A] (a b : A) : A :=
  a * b - b * a









noncomputable def cherednikPowerCoefficient
    {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n)
    (H : C.Hyperplane)
    (ℓ : Fin (C.mH H))
    (y : Vec n)
    (x : Vec n →ₗ[ℂ] ℂ) : ℂ :=
  if ℓ.val = 0 then
    0
  else
    C.cPower H ℓ * (C.alphaH H y) * x (C.corootH H)


structure CherednikRelationRealization
    {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n)
    (A : Type u) [Ring A] [Algebra ℂ A] where
  xGen : (Vec n →ₗ[ℂ] ℂ) → A
  yGen : Vec n → A
  gGen : C.G → A

  x_add :
    ∀ x x' : Vec n →ₗ[ℂ] ℂ,
      xGen (x + x') = xGen x + xGen x'
  x_smul :
    ∀ (a : ℂ) (x : Vec n →ₗ[ℂ] ℂ),
      xGen (a • x) = algebraMap ℂ A a * xGen x
  y_add :
    ∀ y y' : Vec n,
      yGen (fun i => y i + y' i) = yGen y + yGen y'
  y_smul :
    ∀ (a : ℂ) (y : Vec n),
      yGen (vecScale a y) = algebraMap ℂ A a * yGen y

  g_one :
    gGen 1 = 1
  g_mul :
    ∀ g h : C.G, gGen (g * h) = gGen g * gGen h

  group_act_x :
    ∀ (g : C.G) (x : Vec n →ₗ[ℂ] ℂ),
      gGen g * xGen x * gGen (g⁻¹) =
        xGen (actCovec C g x)
  group_act_y :
    ∀ (g : C.G) (y : Vec n),
      gGen g * yGen y * gGen (g⁻¹) =
        yGen (actVec C g y)

  xx :
    ∀ x x' : Vec n →ₗ[ℂ] ℂ,
      commutator (xGen x) (xGen x') = 0
  yy :
    ∀ y y' : Vec n,
      commutator (yGen y) (yGen y') = 0

  yx :
    ∀ (y : Vec n) (x : Vec n →ₗ[ℂ] ℂ),
      commutator (yGen y) (xGen x) =
        algebraMap ℂ A (x y) -
          ∑ H₀ : C.Hyperplane,
            ∑ ℓ : Fin (C.mH H₀),
              algebraMap ℂ A
                  (cherednikPowerCoefficient C H₀ ℓ y x) *
                gGen ((C.sH H₀) ^ ℓ.val)


structure RationalCherednikAlgebraData
    {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n) where
  H : Type u
  [instRingH : Ring H]
  [instAlgebraH : Algebra ℂ H]

  xGen : (Vec n →ₗ[ℂ] ℂ) → H
  yGen : Vec n → H
  gGen : C.G → H

  presentation :
    CherednikRelationRealization C H

  presentation_x :
    presentation.xGen = xGen
  presentation_y :
    presentation.yGen = yGen
  presentation_g :
    presentation.gGen = gGen

  universal_property :
    ∀ (A : Type u) [Ring A] [Algebra ℂ A],
      ∀ R : CherednikRelationRealization C A,
        ∃ φ : H →ₐ[ℂ] A,
          (∀ x : Vec n →ₗ[ℂ] ℂ, φ (xGen x) = R.xGen x) ∧
          (∀ y : Vec n, φ (yGen y) = R.yGen y) ∧
          (∀ g : C.G, φ (gGen g) = R.gGen g) ∧
            ∀ ψ : H →ₐ[ℂ] A,
              (∀ x : Vec n →ₗ[ℂ] ℂ, ψ (xGen x) = R.xGen x) →
              (∀ y : Vec n, ψ (yGen y) = R.yGen y) →
              (∀ g : C.G, ψ (gGen g) = R.gGen g) →
                ∀ h : H, ψ h = φ h

  xPolyAlgHom : PolyH n →ₐ[ℂ] H
  yPolyAlgHom : SymH n →ₐ[ℂ] H

  xPoly_linear :
    ∀ x : Vec n →ₗ[ℂ] ℂ,
      xPolyAlgHom (linearFormPolynomial x) = xGen x
  yPoly_linear :
    ∀ y : Vec n,
      yPolyAlgHom (vecAsYPolynomial y) = yGen y

  gradingElement : H

attribute [instance] RationalCherednikAlgebraData.instRingH
attribute [instance] RationalCherednikAlgebraData.instAlgebraH


def FinitelyGeneratedOverPolynomialAction {n : ℕ}
    {M : Type w} [AddCommGroup M] [Module ℂ M]
    (A : PolyH n →ₐ[ℂ] Module.End ℂ M) : Prop :=
  ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → M,
    letI := hι
    ∀ m : M, ∃ coeff : ι → PolyH n,
      m = ∑ i : ι, A (coeff i) (b i)


def LocallyFiniteUnderPolynomialAction {n : ℕ}
    {M : Type w} [AddCommGroup M] [Module ℂ M]
    (A : SymH n →ₐ[ℂ] Module.End ℂ M) : Prop :=
  ∀ m : M,
    ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → M,
      letI := hι
      ∀ p : SymH n, ∃ coeff : ι → ℂ,
        A p m = ∑ i : ι, coeff i • b i


noncomputable def zeroBlockOperatorY {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    {M : Type w} [AddCommGroup M] [Module ℂ M]
    (yPolyOp : SymH n →ₐ[ℂ] Module.End ℂ M)
    (Q : InvariantYPolynomial C) : Module.End ℂ M :=
  yPolyOp Q.poly -
    invariantYPolynomialZeroEval Q • (1 : Module.End ℂ M)


def InZeroGeneralizedBlockY {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    {M : Type w} [AddCommGroup M] [Module ℂ M]
    (yPolyOp : SymH n →ₐ[ℂ] Module.End ℂ M) : Prop :=
  ∀ m : M,
    ∀ Q : InvariantYPolynomial C,
      ∃ N : ℕ, 0 < N ∧ ((zeroBlockOperatorY yPolyOp Q) ^ N) m = 0


structure CategoryOZeroObject
    {n : ℕ}
    (C : ComplexReflectionKZData.{u, v} n)
    (Hc : RationalCherednikAlgebraData C) where
  M : Type w
  [instAddCommGroup : AddCommGroup M]
  [instModule : Module ℂ M]

  rep : Hc.H →ₐ[ℂ] Module.End ℂ M

  xPolyOp : PolyH n →ₐ[ℂ] Module.End ℂ M
  yPolyOp : SymH n →ₐ[ℂ] Module.End ℂ M

  xPolyOp_compat :
    ∀ p : PolyH n,
      xPolyOp p = rep (Hc.xPolyAlgHom p)
  yPolyOp_compat :
    ∀ p : SymH n,
      yPolyOp p = rep (Hc.yPolyAlgHom p)

  finitelyGeneratedOverShStar :
    FinitelyGeneratedOverPolynomialAction xPolyOp
  locallyFiniteUnderSh :
    LocallyFiniteUnderPolynomialAction yPolyOp

  zeroBlock :
    InZeroGeneralizedBlockY (C := C) yPolyOp

attribute [instance] CategoryOZeroObject.instAddCommGroup
attribute [instance] CategoryOZeroObject.instModule


structure CategoryOZeroHom
    {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    {Hc : RationalCherednikAlgebraData C}
    (M N : CategoryOZeroObject.{u, v, w} C Hc) where
  toLinear : M.M →ₗ[ℂ] N.M
  map_H :
    ∀ (h : Hc.H) (m : M.M),
      toLinear (M.rep h m) = N.rep h (toLinear m)


def CategoryOZeroHomEq
    {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    {Hc : RationalCherednikAlgebraData C}
    {M N : CategoryOZeroObject.{u, v, w} C Hc}
    (f g : CategoryOZeroHom M N) : Prop :=
  ∀ m : M.M, f.toLinear m = g.toLinear m

namespace CategoryOZeroHom


def id
    {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    {Hc : RationalCherednikAlgebraData C}
    (M : CategoryOZeroObject.{u, v, w} C Hc) :
    CategoryOZeroHom M M where
  toLinear := LinearMap.id
  map_H := by
    intro h m
    rfl


def comp
    {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    {Hc : RationalCherednikAlgebraData C}
    {L M N : CategoryOZeroObject.{u, v, w} C Hc}
    (f : CategoryOZeroHom L M)
    (g : CategoryOZeroHom M N) :
    CategoryOZeroHom L N where
  toLinear := g.toLinear.comp f.toLinear
  map_H := by
    intro h m
    calc
      g.toLinear (f.toLinear (L.rep h m))
          = g.toLinear (M.rep h (f.toLinear m)) := by
              rw [f.map_H h m]
      _ = N.rep h (g.toLinear (f.toLinear m)) := by
              rw [g.map_H h (f.toLinear m)]

end CategoryOZeroHom


def IsEpimorphismO
    {n : ℕ}
    {C : ComplexReflectionKZData.{u, v} n}
    {Hc : RationalCherednikAlgebraData C}
    {M N : CategoryOZeroObject.{u, v, w} C Hc}
    (f : CategoryOZeroHom M N) : Prop :=
  ∀ n : N.M, ∃ m : M.M, f.toLinear m = n


def IsAugmentationIdealElement {r : ℕ} (p : SymH r) : Prop :=
  polynomialEvalAt (zeroVec r) p = 0





def KilledByAugmentationIdealPower
    {r : ℕ}
    {M : Type w} [AddCommGroup M] [Module ℂ M]
    (yPolyOp : SymH r →ₐ[ℂ] Module.End ℂ M)
    (power : ℕ)
    (m : M) : Prop :=
  ∀ f : Fin power → SymH r,
    (∀ i : Fin power, IsAugmentationIdealElement (f i)) →
      yPolyOp (∏ i : Fin power, f i) m = 0







structure IsTruncatedRegularObject
    {r : ℕ}
    (C : ComplexReflectionKZData.{u, v} r)
    (Hc : RationalCherednikAlgebraData C)
    (truncationLevel : ℕ)
    (T : CategoryOZeroObject.{u, v, w} C Hc) where

  universalHom :
    ∀ N : CategoryOZeroObject.{u, v, w} C Hc,
      CategoryOZeroHom T N ≃
        {m : N.M //
          KilledByAugmentationIdealPower
            N.yPolyOp
            (truncationLevel + 1)
            m}

  killedFunctorMap :
    ∀ {N N' : CategoryOZeroObject.{u, v, w} C Hc},
      CategoryOZeroHom N N' →
        {m : N.M //
          KilledByAugmentationIdealPower
            N.yPolyOp
            (truncationLevel + 1)
            m} →
        {m : N'.M //
          KilledByAugmentationIdealPower
            N'.yPolyOp
            (truncationLevel + 1)
            m}

  killedFunctorMap_val :
    ∀ {N N' : CategoryOZeroObject.{u, v, w} C Hc}
      (f : CategoryOZeroHom N N')
      (x :
        {m : N.M //
          KilledByAugmentationIdealPower
            N.yPolyOp
            (truncationLevel + 1)
            m}),
        (killedFunctorMap f x).val = f.toLinear x.val

  universalHom_naturality :
    ∀ {N N' : CategoryOZeroObject.{u, v, w} C Hc}
      (f : CategoryOZeroHom N N')
      (h : CategoryOZeroHom T N),
        universalHom N' (CategoryOZeroHom.comp h f) =
          killedFunctorMap f (universalHom N h)







structure TruncatedRegularModuleFamily
    {r : ℕ}
    (C : ComplexReflectionKZData.{u, v} r)
    (Hc : RationalCherednikAlgebraData C) where
  obj : ℕ → CategoryOZeroObject.{u, v, w} C Hc
  isTruncatedRegular :
    ∀ n : ℕ, IsTruncatedRegularObject C Hc n (obj n)


def McnRegular
    {r : ℕ}
    {C : ComplexReflectionKZData.{u, v} r}
    {Hc : RationalCherednikAlgebraData C}
    (Mreg : TruncatedRegularModuleFamily.{u, v, w} C Hc)
    (n : ℕ) : CategoryOZeroObject.{u, v, w} C Hc :=
  Mreg.obj n


def IsProjectiveObjectO
    {r : ℕ}
    {C : ComplexReflectionKZData.{u, v} r}
    {Hc : RationalCherednikAlgebraData C}
    (P : CategoryOZeroObject.{u, v, w} C Hc) : Prop :=
  ∀ {M N : CategoryOZeroObject.{u, v, w} C Hc}
    (epi : CategoryOZeroHom M N),
      IsEpimorphismO epi →
        ∀ f : CategoryOZeroHom P N,
          ∃ lift : CategoryOZeroHom P M,
            CategoryOZeroHomEq
              (CategoryOZeroHom.comp lift epi)
              f


def IsGeneratorObjectO
    {r : ℕ}
    {C : ComplexReflectionKZData.{u, v} r}
    {Hc : RationalCherednikAlgebraData C}
    (P : CategoryOZeroObject.{u, v, w} C Hc) : Prop :=
  ∀ M : CategoryOZeroObject.{u, v, w} C Hc,
    (∀ f : CategoryOZeroHom P M, ∀ p : P.M, f.toLinear p = 0) →
      ∀ m : M.M, m = 0


def IsProjectiveGeneratorObjectO
    {r : ℕ}
    {C : ComplexReflectionKZData.{u, v} r}
    {Hc : RationalCherednikAlgebraData C}
    (P : CategoryOZeroObject.{u, v, w} C Hc) : Prop :=
  IsProjectiveObjectO P ∧ IsGeneratorObjectO P


structure IsDirectSummandO
    {r : ℕ}
    {C : ComplexReflectionKZData.{u, v} r}
    {Hc : RationalCherednikAlgebraData C}
    (P M : CategoryOZeroObject.{u, v, w} C Hc) where
  inclusion : CategoryOZeroHom P M
  projection : CategoryOZeroHom M P
  projection_inclusion :
    CategoryOZeroHomEq
      (CategoryOZeroHom.comp inclusion projection)
      (CategoryOZeroHom.id P)




def ContainsProjectiveGeneratorDirectSummand
    {r : ℕ}
    {C : ComplexReflectionKZData.{u, v} r}
    {Hc : RationalCherednikAlgebraData C}
    (M : CategoryOZeroObject.{u, v, w} C Hc) : Prop :=
  ∃ P : CategoryOZeroObject.{u, v, w} C Hc,
    ∃ _summand : IsDirectSummandO P M,
      IsProjectiveGeneratorObjectO P



end Autoform_Double_Hecke_Algebras_double_hecke_theorem_6_5_exists_large_truncated_regular_bound
