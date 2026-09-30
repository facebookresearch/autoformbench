import Mathlib













































noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18

universe u v

variable {K : Type u} [Field K]




def baseChangeWeierstrass
    (Ω : Type v) [Field Ω] [Algebra K Ω] (E : WeierstrassCurve K) :
    WeierstrassCurve Ω where
  a₁ := algebraMap K Ω E.a₁
  a₂ := algebraMap K Ω E.a₂
  a₃ := algebraMap K Ω E.a₃
  a₄ := algebraMap K Ω E.a₄
  a₆ := algebraMap K Ω E.a₆


abbrev Curve (E : WeierstrassCurve K) : WeierstrassCurve.Affine K :=
  E


abbrev GeometricCurve
    (Ω : Type v) [Field Ω] [Algebra K Ω] (E : WeierstrassCurve K) :
    WeierstrassCurve.Affine Ω :=
  baseChangeWeierstrass (K := K) Ω E




abbrev CoordinateRing (E : WeierstrassCurve K) : Type u :=
  (Curve E).CoordinateRing


abbrev FunctionField (E : WeierstrassCurve K) : Type u :=
  (Curve E).FunctionField


noncomputable def functionFieldX (E : WeierstrassCurve K) : FunctionField E :=
  algebraMap (CoordinateRing E) (FunctionField E)
    ((Polynomial.X : Polynomial K) • (1 : CoordinateRing E))


noncomputable def functionFieldY (E : WeierstrassCurve K) : FunctionField E :=
  algebraMap (CoordinateRing E) (FunctionField E)
    ((WeierstrassCurve.Affine.CoordinateRing.basis (Curve E)) 1)


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


def affine (x y : K) : Coords3 K :=
  (x, y, 1)


def infinity : Coords3 K :=
  (0, 1, 0)


def OnWeierstrass (E : WeierstrassCurve K) (P : Coords3 K) : Prop :=
  Y P ^ 2 * Z P + E.a₁ * X P * Y P * Z P + E.a₃ * Y P * Z P ^ 2 =
    X P ^ 3 + E.a₂ * X P ^ 2 * Z P + E.a₄ * X P * Z P ^ 2 + E.a₆ * Z P ^ 3

end Coords3


structure ProjectiveTriple (K : Type u) [Field K] where
  X : MvPolynomial (Fin 3) K
  Y : MvPolynomial (Fin 3) K
  Z : MvPolynomial (Fin 3) K

namespace ProjectiveTriple

variable (T : ProjectiveTriple K)


def evalFnOver {Ω : Type v} [Field Ω] (P : Coords3 Ω) : Fin 3 → Ω :=
  fun i =>
    if i = (0 : Fin 3) then Coords3.X P
    else if i = (1 : Fin 3) then Coords3.Y P
    else Coords3.Z P


def evalOver {Ω : Type v} [Field Ω] [Algebra K Ω] (P : Coords3 Ω) : Coords3 Ω :=
  (MvPolynomial.eval₂ (algebraMap K Ω) (evalFnOver P) T.X,
   MvPolynomial.eval₂ (algebraMap K Ω) (evalFnOver P) T.Y,
   MvPolynomial.eval₂ (algebraMap K Ω) (evalFnOver P) T.Z)


def NonzeroAtOver {Ω : Type v} [Field Ω] [Algebra K Ω] (P : Coords3 Ω) : Prop :=
  Coords3.Nonzero (T.evalOver P)

end ProjectiveTriple






def weierstrassProjectivePolynomial (E : WeierstrassCurve K) :
    MvPolynomial (Fin 3) K :=
  MvPolynomial.X (1 : Fin 3) ^ 2 * MvPolynomial.X (2 : Fin 3)
    + MvPolynomial.C E.a₁ * MvPolynomial.X (0 : Fin 3) *
        MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (2 : Fin 3)
    + MvPolynomial.C E.a₃ * MvPolynomial.X (1 : Fin 3) *
        MvPolynomial.X (2 : Fin 3) ^ 2
    - MvPolynomial.X (0 : Fin 3) ^ 3
    - MvPolynomial.C E.a₂ * MvPolynomial.X (0 : Fin 3) ^ 2 *
        MvPolynomial.X (2 : Fin 3)
    - MvPolynomial.C E.a₄ * MvPolynomial.X (0 : Fin 3) *
        MvPolynomial.X (2 : Fin 3) ^ 2
    - MvPolynomial.C E.a₆ * MvPolynomial.X (2 : Fin 3) ^ 3


def weierstrassProjectiveIdeal (E : WeierstrassCurve K) :
    Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span ({weierstrassProjectivePolynomial E} : Set (MvPolynomial (Fin 3) K))





def weierstrassProjectivePolynomialAtTriple
    (E : WeierstrassCurve K) (T : ProjectiveTriple K) : MvPolynomial (Fin 3) K :=
  T.Y ^ 2 * T.Z
    + MvPolynomial.C E.a₁ * T.X * T.Y * T.Z
    + MvPolynomial.C E.a₃ * T.Y * T.Z ^ 2
    - T.X ^ 3
    - MvPolynomial.C E.a₂ * T.X ^ 2 * T.Z
    - MvPolynomial.C E.a₄ * T.X * T.Z ^ 2
    - MvPolynomial.C E.a₆ * T.Z ^ 3

namespace ProjectiveTriple


def HomogeneousOfDegree (T : ProjectiveTriple K) (d : ℕ) : Prop :=
  T.X.IsHomogeneous d ∧ T.Y.IsHomogeneous d ∧ T.Z.IsHomogeneous d





def NotAllInSourceIdeal (E : WeierstrassCurve K) (T : ProjectiveTriple K) : Prop :=
  ¬ (T.X ∈ weierstrassProjectiveIdeal E ∧
     T.Y ∈ weierstrassProjectiveIdeal E ∧
     T.Z ∈ weierstrassProjectiveIdeal E)









def RationalMapRepresentative
    (E₁ E₂ : WeierstrassCurve K) (T : ProjectiveTriple K) : Prop :=
  (∃ d : ℕ, T.HomogeneousOfDegree d) ∧
  T.NotAllInSourceIdeal E₁ ∧
  weierstrassProjectivePolynomialAtTriple E₂ T ∈ weierstrassProjectiveIdeal E₁

end ProjectiveTriple





def ProjectiveTriplesEquivalentOnSource
    (E : WeierstrassCurve K) (T U : ProjectiveTriple K) : Prop :=
  T.X * U.Y - U.X * T.Y ∈ weierstrassProjectiveIdeal E ∧
  T.X * U.Z - U.X * T.Z ∈ weierstrassProjectiveIdeal E ∧
  T.Y * U.Z - U.Y * T.Z ∈ weierstrassProjectiveIdeal E






structure IsProjectiveMorphismRepresentative
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (T : ProjectiveTriple K) (E₁ E₂ : WeierstrassCurve K) : Prop where
  rational_map_representative :
    T.RationalMapRepresentative E₁ E₂
  maps_defined_geometric_points :
    ∀ P : Coords3 Ω,
      Coords3.Nonzero P →
      Coords3.OnWeierstrass (baseChangeWeierstrass (K := K) Ω E₁) P →
      T.NonzeroAtOver P →
      Coords3.OnWeierstrass
        (baseChangeWeierstrass (K := K) Ω E₂) (T.evalOver P)
  regular_everywhere_geometric :
    ∀ P : Coords3 Ω,
      Coords3.Nonzero P →
      Coords3.OnWeierstrass (baseChangeWeierstrass (K := K) Ω E₁) P →
      ∃ U : ProjectiveTriple K,
        U.RationalMapRepresentative E₁ E₂ ∧
        ProjectiveTriplesEquivalentOnSource E₁ T U ∧
        U.NonzeroAtOver P ∧
        Coords3.OnWeierstrass
          (baseChangeWeierstrass (K := K) Ω E₂) (U.evalOver P)







noncomputable def evalProjectivePolynomialInFunctionField
    (E : WeierstrassCurve K) (p : MvPolynomial (Fin 3) K) : FunctionField E :=
  MvPolynomial.eval₂ (algebraMap K (FunctionField E))
    (fun i =>
      if i = (0 : Fin 3) then functionFieldX E
      else if i = (1 : Fin 3) then functionFieldY E
      else (1 : FunctionField E)) p

namespace ProjectiveTriple


noncomputable def xFunction (T : ProjectiveTriple K) (E : WeierstrassCurve K) :
    FunctionField E :=
  evalProjectivePolynomialInFunctionField E T.X /
    evalProjectivePolynomialInFunctionField E T.Z


noncomputable def yFunction (T : ProjectiveTriple K) (E : WeierstrassCurve K) :
    FunctionField E :=
  evalProjectivePolynomialInFunctionField E T.Y /
    evalProjectivePolynomialInFunctionField E T.Z

end ProjectiveTriple










structure FunctionFieldPullbackData
    (E₁ E₂ : WeierstrassCurve K) (T : ProjectiveTriple K) where
  pullback : FunctionField E₂ →ₐ[K] FunctionField E₁
  maps_x : pullback (functionFieldX E₂) = T.xFunction E₁
  maps_y : pullback (functionFieldY E₂) = T.yFunction E₁
  injective : Function.Injective pullback
  finite_extension : FiniteDimensional pullback.toRingHom.fieldRange (FunctionField E₁)

namespace FunctionFieldPullbackData

variable {E₁ E₂ : WeierstrassCurve K} {T : ProjectiveTriple K}


abbrev imageField (D : FunctionFieldPullbackData E₁ E₂ T) :
    Subfield (FunctionField E₁) :=
  D.pullback.toRingHom.fieldRange


noncomputable def degree (D : FunctionFieldPullbackData E₁ E₂ T) : ℕ :=
  Module.finrank D.imageField (FunctionField E₁)

end FunctionFieldPullbackData


def pointCoords
    {Ω : Type v} [Field Ω] [Algebra K Ω]
    (E : WeierstrassCurve K)
    (P : (GeometricCurve (K := K) Ω E).Point) : Coords3 Ω :=
  match P with
  | 0 => Coords3.infinity
  | .some x y _ => Coords3.affine x y


def PointHasProjectiveCoords
    {Ω : Type v} [Field Ω] [Algebra K Ω]
    (E : WeierstrassCurve K)
    (P : (GeometricCurve (K := K) Ω E).Point)
    (C : Coords3 Ω) : Prop :=
  Coords3.ProjectivelyEquivalent C (pointCoords (K := K) E P)






def ProjectiveFormulaForPointMap
    {Ω : Type v} [Field Ω] [Algebra K Ω]
    (E₁ E₂ : WeierstrassCurve K)
    (T : ProjectiveTriple K)
    (φ : (GeometricCurve (K := K) Ω E₁).Point →
         (GeometricCurve (K := K) Ω E₂).Point) : Prop :=
  φ 0 = 0 ∧
  ∀ P : (GeometricCurve (K := K) Ω E₁).Point,
    ∃ U : ProjectiveTriple K,
      U.RationalMapRepresentative E₁ E₂ ∧
      ProjectiveTriplesEquivalentOnSource E₁ T U ∧
      U.NonzeroAtOver (pointCoords (K := K) E₁ P) ∧
      PointHasProjectiveCoords (K := K) E₂ (φ P)
        (U.evalOver (pointCoords (K := K) E₁ P))








structure IsIsogenyRepresentative
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E₁ E₂ : WeierstrassCurve K)
    [hE₁ : (GeometricCurve (K := K) Ω E₁).IsElliptic]
    [hE₂ : (GeometricCurve (K := K) Ω E₂).IsElliptic]
    (T : ProjectiveTriple K)
    (φ : (GeometricCurve (K := K) Ω E₁).Point →
         (GeometricCurve (K := K) Ω E₂).Point) : Prop where
  morphism_representative :
    IsProjectiveMorphismRepresentative (Ω := Ω) T E₁ E₂
  projective_formula_for_point_map :
    ProjectiveFormulaForPointMap (Ω := Ω) E₁ E₂ T φ
  maps_zero : φ 0 = 0
  group_hom :
    ∀ P Q : (GeometricCurve (K := K) Ω E₁).Point,
      φ (P + Q) = φ P + φ Q
  geometrically_surjective : Function.Surjective φ
  nonconstant : ∃ P : (GeometricCurve (K := K) Ω E₁).Point, φ P ≠ 0



variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
variable {E : WeierstrassCurve K}
variable [hE : (GeometricCurve (K := K) Ω E).IsElliptic]









structure AlgebraicEndomorphismData
    (φ : AddMonoid.End (GeometricCurve (K := K) Ω E).Point) where
  T : ProjectiveTriple K
  isogeny :
    IsIsogenyRepresentative (Ω := Ω) E E T (fun P => φ P)
  functionField : FunctionFieldPullbackData E E T















structure EllipticCurveEndomorphism (E : WeierstrassCurve K)
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [hE : (GeometricCurve (K := K) Ω E).IsElliptic] where
  toEnd : AddMonoid.End (GeometricCurve (K := K) Ω E).Point
  algebraic :
    toEnd = 0 ∨ Nonempty (AlgebraicEndomorphismData (Ω := Ω) (E := E) toEnd)

attribute [coe] EllipticCurveEndomorphism.toEnd

instance instCoeFunEllipticCurveEndomorphism :
    CoeFun (EllipticCurveEndomorphism E Ω)
      (fun _ => (GeometricCurve (K := K) Ω E).Point →
        (GeometricCurve (K := K) Ω E).Point) where
  coe α := fun P => α.toEnd P


theorem has_algebraicData_of_nonzero
    (α : EllipticCurveEndomorphism E Ω)
    (hα : α.toEnd ≠ 0) :
    Nonempty (AlgebraicEndomorphismData (Ω := Ω) (E := E) α.toEnd) := by
  rcases α.algebraic with hzero | hdata
  · exact (hα hzero).elim
  · exact hdata






noncomputable def chosenAlgebraicData
    (α : EllipticCurveEndomorphism E Ω)
    (hα : α.toEnd ≠ 0) :
    AlgebraicEndomorphismData (Ω := Ω) (E := E) α.toEnd :=
  Classical.choice (has_algebraicData_of_nonzero (E := E) (Ω := Ω) α hα)











noncomputable def degree (α : EllipticCurveEndomorphism E Ω) : ℕ := by
  classical
  exact if hα : α.toEnd = 0 then
    0
  else
    (chosenAlgebraicData (E := E) (Ω := Ω) α hα).functionField.degree















end Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18

end