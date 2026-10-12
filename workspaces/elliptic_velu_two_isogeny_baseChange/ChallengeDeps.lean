/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





























noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_velu_two_isogeny_baseChange

universe u v

variable {K : Type u} [Field K]


def shortWeierstrass (A B : K) : WeierstrassCurve K where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B


abbrev ShortCurve (A B : K) : WeierstrassCurve.Affine K :=
  shortWeierstrass A B






structure StandardAffineMap (K : Type u) [Field K] where
  xNum : Polynomial K
  xDen : Polynomial K
  yNum : Polynomial K
  yDen : Polynomial K

namespace StandardAffineMap

variable (F : StandardAffineMap K)


def xCoord (x : K) : K :=
  F.xNum.eval x / F.xDen.eval x


def yScale (x : K) : K :=
  F.yNum.eval x / F.yDen.eval x


def yCoord (x y : K) : K :=
  F.yScale x * y


def degree : Nat :=
  max F.xNum.natDegree F.xDen.natDegree

end StandardAffineMap


def PolynomialCoprime (p q : Polynomial K) : Prop :=
  ∃ a b : Polynomial K, a * p + b * q = 1


def rationalDerivativeNumerator (u v : Polynomial K) : Polynomial K :=
  derivative u * v - u * derivative v


def RationalDerivativeNonzero (u v : Polynomial K) : Prop :=
  rationalDerivativeNumerator u v ≠ 0




abbrev Coords3 (K : Type u) := K × K × K

namespace Coords3



def X (P : Coords3 K) : K := P.1


def Y (P : Coords3 K) : K := P.2.1


def Z (P : Coords3 K) : K := P.2.2


def Nonzero (P : Coords3 K) : Prop :=
  X P ≠ 0 ∨ Y P ≠ 0 ∨ Z P ≠ 0


def ProjectivelyEquivalent (P Q : Coords3 K) : Prop :=
  ∃ Λ : K, Λ ≠ 0 ∧
    X Q = Λ * X P ∧ Y Q = Λ * Y P ∧ Z Q = Λ * Z P


def OnShortWeierstrass (A B : K) (P : Coords3 K) : Prop :=
  Y P ^ 2 * Z P = X P ^ 3 + A * X P * Z P ^ 2 + B * Z P ^ 3


def affine (x y : K) : Coords3 K :=
  (x, y, 1)

end Coords3


structure ProjectiveTriple (K : Type u) [Field K] where
  X : MvPolynomial (Fin 3) K
  Y : MvPolynomial (Fin 3) K
  Z : MvPolynomial (Fin 3) K

namespace ProjectiveTriple

variable (T : ProjectiveTriple K)


def evalFn (P : Coords3 K) : Fin 3 → K :=
  fun i =>
    if i = (0 : Fin 3) then Coords3.X P
    else if i = (1 : Fin 3) then Coords3.Y P
    else Coords3.Z P


def eval (P : Coords3 K) : Coords3 K :=
  (MvPolynomial.eval (evalFn P) T.X,
   MvPolynomial.eval (evalFn P) T.Y,
   MvPolynomial.eval (evalFn P) T.Z)


def NonzeroAt (P : Coords3 K) : Prop :=
  Coords3.Nonzero (T.eval P)

end ProjectiveTriple


def shortProjectivePolynomial (A B : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X (1 : Fin 3) ^ 2 * MvPolynomial.X (2 : Fin 3)
    - MvPolynomial.X (0 : Fin 3) ^ 3
    - MvPolynomial.C A * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) ^ 2
    - MvPolynomial.C B * MvPolynomial.X (2 : Fin 3) ^ 3


def shortProjectiveIdeal (A B : K) : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span ({shortProjectivePolynomial A B} : Set (MvPolynomial (Fin 3) K))







def shortProjectivePolynomialAtTriple
    (A B : K) (T : ProjectiveTriple K) : MvPolynomial (Fin 3) K :=
  T.Y ^ 2 * T.Z
    - T.X ^ 3
    - MvPolynomial.C A * T.X * T.Z ^ 2
    - MvPolynomial.C B * T.Z ^ 3

namespace ProjectiveTriple


def HomogeneousOfDegree (T : ProjectiveTriple K) (d : ℕ) : Prop :=
  T.X.IsHomogeneous d ∧ T.Y.IsHomogeneous d ∧ T.Z.IsHomogeneous d





def NotAllInSourceIdeal (A B : K) (T : ProjectiveTriple K) : Prop :=
  ¬ (T.X ∈ shortProjectiveIdeal A B ∧
     T.Y ∈ shortProjectiveIdeal A B ∧
     T.Z ∈ shortProjectiveIdeal A B)





def RationalMapRepresentative
    (A₁ B₁ A₂ B₂ : K) (T : ProjectiveTriple K) : Prop :=
  (∃ d : ℕ, T.HomogeneousOfDegree d) ∧
  T.NotAllInSourceIdeal A₁ B₁ ∧
  shortProjectivePolynomialAtTriple A₂ B₂ T ∈ shortProjectiveIdeal A₁ B₁

end ProjectiveTriple









def ProjectiveTriplesEquivalentOnSource
    (A B : K) (T U : ProjectiveTriple K) : Prop :=
  T.X * U.Y - U.X * T.Y ∈ shortProjectiveIdeal A B ∧
  T.X * U.Z - U.X * T.Z ∈ shortProjectiveIdeal A B ∧
  T.Y * U.Z - U.Y * T.Z ∈ shortProjectiveIdeal A B











structure IsProjectiveMorphismRepresentative
    (T : ProjectiveTriple K) (A₁ B₁ A₂ B₂ : K) : Prop where
  rational_map_representative :
    T.RationalMapRepresentative A₁ B₁ A₂ B₂
  maps_defined_points :
    ∀ P : Coords3 K,
      Coords3.Nonzero P →
      Coords3.OnShortWeierstrass A₁ B₁ P →
      T.NonzeroAt P →
      Coords3.OnShortWeierstrass A₂ B₂ (T.eval P)
  regular_everywhere :
    ∀ P : Coords3 K,
      Coords3.Nonzero P →
      Coords3.OnShortWeierstrass A₁ B₁ P →
      ∃ U : ProjectiveTriple K,
        U.RationalMapRepresentative A₁ B₁ A₂ B₂ ∧
        ProjectiveTriplesEquivalentOnSource A₁ B₁ T U ∧
        U.NonzeroAt P ∧
        Coords3.OnShortWeierstrass A₂ B₂ (U.eval P)





def ProjectiveTripleRepresentsStandardAffineMap
    (T : ProjectiveTriple K) (F : StandardAffineMap K) : Prop :=
  ∀ x y : K,
    F.xDen.eval x ≠ 0 →
    F.yDen.eval x ≠ 0 →
    Coords3.ProjectivelyEquivalent
      (T.eval (Coords3.affine x y))
      (F.xCoord x, F.yCoord x y, 1)





def AffineFormulaForPointMap [DecidableEq K]
    (A₁ B₁ A₂ B₂ : K)
    (F : StandardAffineMap K)
    (φ : (ShortCurve A₁ B₁).Point → (ShortCurve A₂ B₂).Point) : Prop :=
  φ 0 = 0 ∧
  (∀ P : (ShortCurve A₁ B₁).Point,
    match P with
    | 0 => True
    | .some x y hxy =>
        F.xDen.eval x ≠ 0 →
        F.yDen.eval x ≠ 0 →
        ∃ hImage,
          φ (.some x y hxy) =
            .some (F.xCoord x) (F.yCoord x y) hImage) ∧
  (∀ P : (ShortCurve A₁ B₁).Point,
    match P with
    | 0 => True
    | .some x y hxy =>
        F.xDen.eval x = 0 → φ (.some x y hxy) = 0)





def AffineKernelControlledByXDen [DecidableEq K]
    (A₁ B₁ A₂ B₂ : K)
    (F : StandardAffineMap K)
    (φ : (ShortCurve A₁ B₁).Point → (ShortCurve A₂ B₂).Point) : Prop :=
  ∀ P : (ShortCurve A₁ B₁).Point,
    match P with
    | 0 => True
    | .some x _ _ => φ P = 0 ↔ F.xDen.eval x = 0










structure IsSeparableIsogenyInStandardForm [DecidableEq K]
    (A₁ B₁ A₂ B₂ : K)
    [hE₁ : (ShortCurve A₁ B₁).IsElliptic]
    [hE₂ : (ShortCurve A₂ B₂).IsElliptic]
    (F : StandardAffineMap K)
    (T : ProjectiveTriple K)
    (φ : (ShortCurve A₁ B₁).Point → (ShortCurve A₂ B₂).Point) : Prop where
  x_lowest_terms : PolynomialCoprime F.xNum F.xDen
  y_lowest_terms : PolynomialCoprime F.yNum F.yDen
  projective_represents_affine_formula :
    ProjectiveTripleRepresentsStandardAffineMap T F
  morphism_representative :
    IsProjectiveMorphismRepresentative T A₁ B₁ A₂ B₂
  affine_formula_for_point_map :
    AffineFormulaForPointMap A₁ B₁ A₂ B₂ F φ
  affine_kernel_iff_xden_zero :
    AffineKernelControlledByXDen A₁ B₁ A₂ B₂ F φ
  maps_zero : φ 0 = 0
  group_hom : ∀ P Q : (ShortCurve A₁ B₁).Point, φ (P + Q) = φ P + φ Q
  surjective : Function.Surjective φ
  nonconstant : ∃ P : (ShortCurve A₁ B₁).Point, φ P ≠ 0
  separable : RationalDerivativeNonzero F.xNum F.xDen


def HasKernelGeneratedByOrderTwo [DecidableEq K]
    {A₁ B₁ A₂ B₂ : K}
    [(ShortCurve A₁ B₁).IsElliptic]
    [(ShortCurve A₂ B₂).IsElliptic]
    (φ : (ShortCurve A₁ B₁).Point → (ShortCurve A₂ B₂).Point)
    (P₀ : (ShortCurve A₁ B₁).Point) : Prop :=
  P₀ ≠ 0 ∧
  P₀ + P₀ = 0 ∧
  ∀ P : (ShortCurve A₁ B₁).Point, φ P = 0 ↔ P = 0 ∨ P = P₀




def veluT (A x₀ : K) : K :=
  3 * x₀ ^ 2 + A


def veluW (A x₀ : K) : K :=
  x₀ * veluT A x₀


def veluA' (A x₀ : K) : K :=
  A - 5 * veluT A x₀


def veluB' (A B x₀ : K) : K :=
  B - 7 * veluW A x₀


def veluXNum (A x₀ : K) : Polynomial K :=
  X ^ 2 - C x₀ * X + C (veluT A x₀)


def veluXDen (x₀ : K) : Polynomial K :=
  X - C x₀


def veluYNum (A x₀ : K) : Polynomial K :=
  (X - C x₀) ^ 2 - C (veluT A x₀)


def veluYDen (x₀ : K) : Polynomial K :=
  (X - C x₀) ^ 2


def veluTwoStandardMap (A x₀ : K) : StandardAffineMap K where
  xNum := veluXNum A x₀
  xDen := veluXDen x₀
  yNum := veluYNum A x₀
  yDen := veluYDen x₀



abbrev PX : MvPolynomial (Fin 3) K := MvPolynomial.X (0 : Fin 3)
abbrev PY : MvPolynomial (Fin 3) K := MvPolynomial.X (1 : Fin 3)
abbrev PZ : MvPolynomial (Fin 3) K := MvPolynomial.X (2 : Fin 3)


def veluXNumH (A x₀ : K) : MvPolynomial (Fin 3) K :=
  PX ^ 2 - MvPolynomial.C x₀ * PX * PZ + MvPolynomial.C (veluT A x₀) * PZ ^ 2


def veluXDenH (x₀ : K) : MvPolynomial (Fin 3) K :=
  PX - MvPolynomial.C x₀ * PZ


def veluYNumH (A x₀ : K) : MvPolynomial (Fin 3) K :=
  (PX - MvPolynomial.C x₀ * PZ) ^ 2 - MvPolynomial.C (veluT A x₀) * PZ ^ 2


def veluYDenH (x₀ : K) : MvPolynomial (Fin 3) K :=
  (PX - MvPolynomial.C x₀ * PZ) ^ 2












def veluTwoProjectiveTriple (A x₀ : K) : ProjectiveTriple K where
  X := veluXNumH A x₀ * veluYDenH x₀
  Y := veluYNumH A x₀ * veluXDenH x₀ * PY
  Z := veluXDenH x₀ * veluYDenH x₀ * PZ


def twoTorsionPoint {A B x₀ : K}
    [hE : (ShortCurve A B).IsElliptic]
    (hroot : x₀ ^ 3 + A * x₀ + B = 0) :
    (ShortCurve A B).Point :=
  WeierstrassCurve.Affine.Point.mk
    (W' := ShortCurve A B)
    (x := x₀)
    (y := 0)
    (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simpa [ShortCurve, shortWeierstrass] using hroot.symm)



end Autoform_Elliptic_Curves_elliptic_velu_two_isogeny_baseChange

end
