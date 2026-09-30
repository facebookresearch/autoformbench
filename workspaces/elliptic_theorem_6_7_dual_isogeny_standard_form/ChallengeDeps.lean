import Mathlib





















noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_theorem_6_7_dual_isogeny_standard_form

universe u v

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [IsAlgClosed K]
variable [Algebra.IsAlgebraic k K]




def shortWeierstrass {F : Type*} [Field F] (A B : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B


abbrev ShortCurve {F : Type*} [Field F] (A B : F) : WeierstrassCurve.Affine F :=
  shortWeierstrass A B


abbrev ShortGeometricCurve (A B : k) : WeierstrassCurve.Affine K :=
  ShortCurve (algebraMap k K A) (algebraMap k K B)


abbrev ShortPoint (A B : k) : Type v :=
  (ShortGeometricCurve (K := K) A B).Point


def shortCubic (A B : k) : Polynomial k :=
  X ^ 3 + C A * X + C B




def PolynomialCoprime (p q : Polynomial k) : Prop :=
  ∃ a b : Polynomial k, a * p + b * q = 1


def evalPolyOver (p : Polynomial k) (x : K) : K :=
  Polynomial.eval₂ (algebraMap k K) x p










structure StandardAffineMap (k : Type u) [Field k] where
  xNum : Polynomial k
  xDen : Polynomial k
  yNum : Polynomial k
  yDen : Polynomial k
  xDen_ne_zero : xDen ≠ 0
  yDen_ne_zero : yDen ≠ 0

namespace StandardAffineMap

variable (F : StandardAffineMap k)


def xCoord (x : K) : K :=
  evalPolyOver (K := K) F.xNum x / evalPolyOver (K := K) F.xDen x


def yScale (x : K) : K :=
  evalPolyOver (K := K) F.yNum x / evalPolyOver (K := K) F.yDen x


def yCoord (x y : K) : K :=
  F.yScale (K := K) x * y


def degree : Nat :=
  max F.xNum.natDegree F.xDen.natDegree

end StandardAffineMap







def StandardMapSatisfiesCurveEquation
    (A₁ B₁ A₂ B₂ : k) (F : StandardAffineMap k) : Prop :=
  F.yNum ^ 2 * shortCubic A₁ B₁ * F.xDen ^ 3 =
    F.yDen ^ 2 *
      (F.xNum ^ 3 + C A₂ * F.xNum * F.xDen ^ 2 + C B₂ * F.xDen ^ 3)





def StandardMapDenominatorDivisibility
    (A₁ B₁ : k) (F : StandardAffineMap k) : Prop :=
  F.xDen ^ 3 ∣ F.yDen ^ 2 ∧
    F.yDen ^ 2 ∣ F.xDen ^ 3 * shortCubic A₁ B₁






def StandardMapDenominatorsHaveSameRoots
    (F : StandardAffineMap k) : Prop :=
  ∀ x : K, evalPolyOver (K := K) F.xDen x = 0 ↔ evalPolyOver (K := K) F.yDen x = 0




abbrev Coords3 (F : Type*) := F × F × F

namespace Coords3

variable {F : Type*} [Field F]


def X (P : Coords3 F) : F := P.1


def Y (P : Coords3 F) : F := P.2.1


def Z (P : Coords3 F) : F := P.2.2


def Nonzero (P : Coords3 F) : Prop :=
  X P ≠ 0 ∨ Y P ≠ 0 ∨ Z P ≠ 0


def ProjectivelyEquivalent (P Q : Coords3 F) : Prop :=
  ∃ Λ : F, Λ ≠ 0 ∧
    X Q = Λ * X P ∧ Y Q = Λ * Y P ∧ Z Q = Λ * Z P


def OnShortWeierstrass (A B : F) (P : Coords3 F) : Prop :=
  Y P ^ 2 * Z P = X P ^ 3 + A * X P * Z P ^ 2 + B * Z P ^ 3


def affine (x y : F) : Coords3 F :=
  (x, y, 1)


def infinity : Coords3 F :=
  (0, 1, 0)

end Coords3


structure ProjectiveTriple (k : Type u) [Field k] where
  X : MvPolynomial (Fin 3) k
  Y : MvPolynomial (Fin 3) k
  Z : MvPolynomial (Fin 3) k

namespace ProjectiveTriple

variable (T : ProjectiveTriple k)


def evalFn (P : Coords3 K) : Fin 3 → K :=
  fun i =>
    if i = (0 : Fin 3) then Coords3.X P
    else if i = (1 : Fin 3) then Coords3.Y P
    else Coords3.Z P


def evalOver (P : Coords3 K) : Coords3 K :=
  (MvPolynomial.eval₂ (algebraMap k K) (evalFn (K := K) P) T.X,
   MvPolynomial.eval₂ (algebraMap k K) (evalFn (K := K) P) T.Y,
   MvPolynomial.eval₂ (algebraMap k K) (evalFn (K := K) P) T.Z)


def NonzeroAt (P : Coords3 K) : Prop :=
  Coords3.Nonzero (T.evalOver (K := K) P)


def HomogeneousOfDegree (T : ProjectiveTriple k) (d : ℕ) : Prop :=
  T.X.IsHomogeneous d ∧ T.Y.IsHomogeneous d ∧ T.Z.IsHomogeneous d

end ProjectiveTriple





def shortProjectivePolynomial (A B : k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.X (1 : Fin 3) ^ 2 * MvPolynomial.X (2 : Fin 3)
    - MvPolynomial.X (0 : Fin 3) ^ 3
    - MvPolynomial.C A * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) ^ 2
    - MvPolynomial.C B * MvPolynomial.X (2 : Fin 3) ^ 3


def shortProjectiveIdeal (A B : k) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ({shortProjectivePolynomial A B} : Set (MvPolynomial (Fin 3) k))


def shortProjectivePolynomialAtTriple
    (A B : k) (T : ProjectiveTriple k) : MvPolynomial (Fin 3) k :=
  T.Y ^ 2 * T.Z
    - T.X ^ 3
    - MvPolynomial.C A * T.X * T.Z ^ 2
    - MvPolynomial.C B * T.Z ^ 3

namespace ProjectiveTriple





def NotAllInSourceIdeal (A B : k) (T : ProjectiveTriple k) : Prop :=
  ¬ (T.X ∈ shortProjectiveIdeal A B ∧
     T.Y ∈ shortProjectiveIdeal A B ∧
     T.Z ∈ shortProjectiveIdeal A B)






def RationalMapRepresentative
    (A₁ B₁ A₂ B₂ : k) (T : ProjectiveTriple k) : Prop :=
  (∃ d : ℕ, T.HomogeneousOfDegree d) ∧
  T.NotAllInSourceIdeal A₁ B₁ ∧
  shortProjectivePolynomialAtTriple A₂ B₂ T ∈ shortProjectiveIdeal A₁ B₁

end ProjectiveTriple





def ProjectiveTriplesEquivalentOnSource
    (A B : k) (T U : ProjectiveTriple k) : Prop :=
  T.X * U.Y - U.X * T.Y ∈ shortProjectiveIdeal A B ∧
  T.X * U.Z - U.X * T.Z ∈ shortProjectiveIdeal A B ∧
  T.Y * U.Z - U.Y * T.Z ∈ shortProjectiveIdeal A B







structure IsProjectiveMorphismRepresentative
    (T : ProjectiveTriple k) (A₁ B₁ A₂ B₂ : k) : Prop where
  rational_map_representative :
    T.RationalMapRepresentative A₁ B₁ A₂ B₂
  maps_defined_points :
    ∀ P : Coords3 K,
      Coords3.Nonzero P →
      Coords3.OnShortWeierstrass (algebraMap k K A₁) (algebraMap k K B₁) P →
      T.NonzeroAt (K := K) P →
      Coords3.OnShortWeierstrass (algebraMap k K A₂) (algebraMap k K B₂)
        (T.evalOver (K := K) P)
  regular_everywhere :
    ∀ P : Coords3 K,
      Coords3.Nonzero P →
      Coords3.OnShortWeierstrass (algebraMap k K A₁) (algebraMap k K B₁) P →
      ∃ U : ProjectiveTriple k,
        U.RationalMapRepresentative A₁ B₁ A₂ B₂ ∧
        ProjectiveTriplesEquivalentOnSource A₁ B₁ T U ∧
        U.NonzeroAt (K := K) P ∧
        Coords3.OnShortWeierstrass (algebraMap k K A₂) (algebraMap k K B₂)
          (U.evalOver (K := K) P)





def ProjectiveTripleRepresentsStandardAffineMap
    (T : ProjectiveTriple k) (F : StandardAffineMap k) : Prop :=
  ∀ x y : K,
    evalPolyOver (K := K) F.xDen x ≠ 0 →
    evalPolyOver (K := K) F.yDen x ≠ 0 →
    Coords3.ProjectivelyEquivalent
      (T.evalOver (K := K) (Coords3.affine x y))
      (F.xCoord (K := K) x, F.yCoord (K := K) x y, 1)




def ProjectiveCoordsRepresentPoint
    (A B : k) (P : ShortPoint (K := K) A B) (Q : Coords3 K) : Prop :=
  match P with
  | 0 => Coords3.ProjectivelyEquivalent Q Coords3.infinity
  | .some x y _ => Coords3.ProjectivelyEquivalent Q (Coords3.affine x y)






def PointMapAgreesWithRepresentative
    (A₁ B₁ A₂ B₂ : k) (T : ProjectiveTriple k)
    (φ : ShortPoint (K := K) A₁ B₁ → ShortPoint (K := K) A₂ B₂) : Prop :=
  ∀ (P : ShortPoint (K := K) A₁ B₁) (Pcoords : Coords3 K) (U : ProjectiveTriple k),
    ProjectiveCoordsRepresentPoint (K := K) A₁ B₁ P Pcoords →
    U.RationalMapRepresentative A₁ B₁ A₂ B₂ →
    ProjectiveTriplesEquivalentOnSource A₁ B₁ T U →
    U.NonzeroAt (K := K) Pcoords →
    ProjectiveCoordsRepresentPoint (K := K) A₂ B₂ (φ P) (U.evalOver (K := K) Pcoords)





def AffineFormulaForPointMap [DecidableEq K]
    (A₁ B₁ A₂ B₂ : k)
    (F : StandardAffineMap k)
    (φ : ShortPoint (K := K) A₁ B₁ → ShortPoint (K := K) A₂ B₂) : Prop :=
  φ 0 = 0 ∧
  (∀ P : ShortPoint (K := K) A₁ B₁,
    match P with
    | 0 => True
    | .some x y hxy =>
        evalPolyOver (K := K) F.xDen x ≠ 0 →
        evalPolyOver (K := K) F.yDen x ≠ 0 →
        ∃ hImage,
          φ (.some x y hxy) =
            .some (F.xCoord (K := K) x) (F.yCoord (K := K) x y) hImage) ∧
  (∀ P : ShortPoint (K := K) A₁ B₁,
    match P with
    | 0 => True
    | .some x y hxy =>
        evalPolyOver (K := K) F.xDen x = 0 → φ (.some x y hxy) = 0)





def AffineKernelControlledByXDen [DecidableEq K]
    (A₁ B₁ A₂ B₂ : k)
    (F : StandardAffineMap k)
    (φ : ShortPoint (K := K) A₁ B₁ → ShortPoint (K := K) A₂ B₂) : Prop :=
  ∀ P : ShortPoint (K := K) A₁ B₁,
    match P with
    | 0 => True
    | .some x _ _ => φ P = 0 ↔ evalPolyOver (K := K) F.xDen x = 0
















structure IsogenyInStandardForm [DecidableEq K]
    (A₁ B₁ A₂ B₂ : k)
    [hE₁ : (ShortGeometricCurve (K := K) A₁ B₁).IsElliptic]
    [hE₂ : (ShortGeometricCurve (K := K) A₂ B₂).IsElliptic]
    (F : StandardAffineMap k)
    (T : ProjectiveTriple k)
    (φ : ShortPoint (K := K) A₁ B₁ → ShortPoint (K := K) A₂ B₂) : Prop where
  x_lowest_terms : PolynomialCoprime F.xNum F.xDen
  y_lowest_terms : PolynomialCoprime F.yNum F.yDen
  satisfies_curve_equation : StandardMapSatisfiesCurveEquation A₁ B₁ A₂ B₂ F
  denominator_divisibility : StandardMapDenominatorDivisibility A₁ B₁ F
  denominators_have_same_roots : StandardMapDenominatorsHaveSameRoots (K := K) F
  projective_represents_affine_formula :
    ProjectiveTripleRepresentsStandardAffineMap (K := K) T F
  morphism_representative :
    IsProjectiveMorphismRepresentative (K := K) T A₁ B₁ A₂ B₂
  point_map_agrees_with_projective_rep :
    PointMapAgreesWithRepresentative (K := K) A₁ B₁ A₂ B₂ T φ
  affine_formula_for_point_map :
    AffineFormulaForPointMap (K := K) A₁ B₁ A₂ B₂ F φ
  affine_kernel_iff_xden_zero :
    AffineKernelControlledByXDen (K := K) A₁ B₁ A₂ B₂ F φ
  maps_zero : φ 0 = 0
  group_hom : ∀ P Q : ShortPoint (K := K) A₁ B₁, φ (P + Q) = φ P + φ Q
  surjective : Function.Surjective φ
  nonconstant : ∃ P : ShortPoint (K := K) A₁ B₁, φ P ≠ 0





structure StandardFormIsogeny [DecidableEq K]
    (A₁ B₁ A₂ B₂ : k)
    [hE₁ : (ShortGeometricCurve (K := K) A₁ B₁).IsElliptic]
    [hE₂ : (ShortGeometricCurve (K := K) A₂ B₂).IsElliptic] where
  F : StandardAffineMap k
  T : ProjectiveTriple k
  toPointMap : ShortPoint (K := K) A₁ B₁ → ShortPoint (K := K) A₂ B₂
  is_isogeny : IsogenyInStandardForm (K := K) A₁ B₁ A₂ B₂ F T toPointMap

namespace StandardFormIsogeny

variable [DecidableEq K]
variable {A₁ B₁ A₂ B₂ : k}
variable [hE₁ : (ShortGeometricCurve (K := K) A₁ B₁).IsElliptic]
variable [hE₂ : (ShortGeometricCurve (K := K) A₂ B₂).IsElliptic]


instance instCoeFunStandardFormIsogeny :
    CoeFun (StandardFormIsogeny (K := K) A₁ B₁ A₂ B₂)
      (fun _ => ShortPoint (K := K) A₁ B₁ → ShortPoint (K := K) A₂ B₂) where
  coe α := α.toPointMap


def degree (α : StandardFormIsogeny (K := K) A₁ B₁ A₂ B₂) : Nat :=
  α.F.degree


def SameMap (α β : StandardFormIsogeny (K := K) A₁ B₁ A₂ B₂) : Prop :=
  ∀ P : ShortPoint (K := K) A₁ B₁, α P = β P

end StandardFormIsogeny






def IsDual [DecidableEq K]
    {A₁ B₁ A₂ B₂ : k}
    [hE₁ : (ShortGeometricCurve (K := K) A₁ B₁).IsElliptic]
    [hE₂ : (ShortGeometricCurve (K := K) A₂ B₂).IsElliptic]
    (αhat : StandardFormIsogeny (K := K) A₂ B₂ A₁ B₁)
    (α : StandardFormIsogeny (K := K) A₁ B₁ A₂ B₂) : Prop :=
  ∀ P : ShortPoint (K := K) A₁ B₁,
    αhat (α P) = α.degree • P



end Autoform_Elliptic_Curves_elliptic_theorem_6_7_dual_isogeny_standard_form
