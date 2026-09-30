import Mathlib



























noncomputable section

open scoped BigOperators

universe u

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_geometric_group_law_23_19_divisorClass


abbrev ProjectivePlaneVector (k : Type u) : Type u :=
  Fin 3 → k


abbrev ProjectiveLineParameter (k : Type u) : Type u :=
  Fin 2 → k


def Nonzero
    {k : Type u} [Zero k] (T : ProjectiveLineParameter k) : Prop :=
  T 0 ≠ 0 ∨ T 1 ≠ 0


def Equivalent
    {k : Type u} [Field k] (S T : ProjectiveLineParameter k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ ∀ i : Fin 2, S i = c * T i





def IsProjectiveLineParametrization
    {k : Type u} [Field k] (U V : ProjectivePlaneVector k) : Prop :=
  ∀ a b : k, (∀ i : Fin 3, a * U i + b * V i = 0) → a = 0 ∧ b = 0


def pointOnParametrizedLine
    {k : Type u} [Field k]
    (U V : ProjectivePlaneVector k) (T : ProjectiveLineParameter k) :
    ProjectivePlaneVector k :=
  fun i => T 0 * U i + T 1 * V i


def lineCoordinatePolynomial
    {k : Type u} [Field k]
    (U V : ProjectivePlaneVector k) (i : Fin 3) : MvPolynomial (Fin 2) k :=
  MvPolynomial.C (U i) * MvPolynomial.X 0 +
    MvPolynomial.C (V i) * MvPolynomial.X 1





def weierstrassPolynomialOnLine
    {k : Type u} [Field k]
    (W : WeierstrassCurve k) (U V : ProjectivePlaneVector k) :
    MvPolynomial (Fin 2) k :=
  let X := lineCoordinatePolynomial U V 0
  let Y := lineCoordinatePolynomial U V 1
  let Z := lineCoordinatePolynomial U V 2
  Y ^ 2 * Z + MvPolynomial.C W.a₁ * X * Y * Z +
    MvPolynomial.C W.a₃ * Y * Z ^ 2 -
      (X ^ 3 + MvPolynomial.C W.a₂ * X ^ 2 * Z +
        MvPolynomial.C W.a₄ * X * Z ^ 2 + MvPolynomial.C W.a₆ * Z ^ 3)





def parameterRootFactor
    {k : Type u} [Field k] (T : ProjectiveLineParameter k) :
    MvPolynomial (Fin 2) k :=
  MvPolynomial.C (T 1) * MvPolynomial.X 0 -
    MvPolynomial.C (T 0) * MvPolynomial.X 1





def ProjectivePointRepresentedBy
    {k : Type u} [Field k]
    {W : WeierstrassCurve k} (P : W.toProjective.Point)
    (p : ProjectivePlaneVector k) : Prop :=
  P.point = (⟦p⟧ : WeierstrassCurve.Projective.PointClass k)


def pointAtInfinityVector (k : Type u) [Zero k] [One k] : ProjectivePlaneVector k :=
  fun i => if i = 1 then 1 else 0


def IsPointAtInfinity
    {k : Type u} [Field k]
    {W : WeierstrassCurve k} (O : W.toProjective.Point) : Prop :=
  ProjectivePointRepresentedBy O (pointAtInfinityVector k)





structure LineIntersectionTripleData
    {k : Type u} [Field k]
    (W : WeierstrassCurve k)
    (A B C : W.toProjective.Point) where
  U : ProjectivePlaneVector k
  V : ProjectivePlaneVector k
  line_is_projective : IsProjectiveLineParametrization U V
  parameterA : ProjectiveLineParameter k
  parameterB : ProjectiveLineParameter k
  parameterC : ProjectiveLineParameter k
  parameterA_nonzero : Nonzero parameterA
  parameterB_nonzero : Nonzero parameterB
  parameterC_nonzero : Nonzero parameterC
  representsA :
    ProjectivePointRepresentedBy A (pointOnParametrizedLine U V parameterA)
  representsB :
    ProjectivePointRepresentedBy B (pointOnParametrizedLine U V parameterB)
  representsC :
    ProjectivePointRepresentedBy C (pointOnParametrizedLine U V parameterC)
  cubic_factorization :
    ∃ c : k, c ≠ 0 ∧
      weierstrassPolynomialOnLine W U V =
        MvPolynomial.C c * parameterRootFactor parameterA *
          parameterRootFactor parameterB * parameterRootFactor parameterC





def IsLineIntersectionTriple
    {k : Type u} [Field k]
    (W : WeierstrassCurve k)
    (A B C : W.toProjective.Point) : Prop :=
  Nonempty (LineIntersectionTripleData W A B C)






structure ThirdIntersectionData
    {k : Type u} [Field k]
    (W : WeierstrassCurve k)
    (P Q R : W.toProjective.Point) where
  lineData : LineIntersectionTripleData W P Q R
  secant_or_tangent :
    (P = Q ∧ Equivalent lineData.parameterA lineData.parameterB) ∨
      (P ≠ Q ∧ ¬ Equivalent lineData.parameterA lineData.parameterB)





def IsThirdIntersectionPointOnSecantTangent
    {k : Type u} [Field k]
    (W : WeierstrassCurve k)
    (P Q R : W.toProjective.Point) : Prop :=
  Nonempty (ThirdIntersectionData W P Q R)





def IsGeometricNegation
    {k : Type u} [Field k]
    (W : WeierstrassCurve k)
    (O R S : W.toProjective.Point) : Prop :=
  IsLineIntersectionTriple W R S O


abbrev PointDivisor
    {k : Type u} [Field k] (W : WeierstrassCurve k) : Type u :=
  W.toProjective.Point →₀ ℤ


def pointDivisor
    {k : Type u} [Field k]
    {W : WeierstrassCurve k} (P : W.toProjective.Point) : PointDivisor W := by
  classical
  exact Finsupp.single P 1


def triplePointDivisor
    {k : Type u} [Field k]
    {W : WeierstrassCurve k} (A B C : W.toProjective.Point) : PointDivisor W :=
  pointDivisor A + pointDivisor B + pointDivisor C





def LineRatioPrincipalDivisorSet
    {k : Type u} [Field k] (W : WeierstrassCurve k) : Set (PointDivisor W) :=
  { D |
    ∃ A B C A' B' C' : W.toProjective.Point,
      IsLineIntersectionTriple W A B C ∧
        IsLineIntersectionTriple W A' B' C' ∧
          D = triplePointDivisor A B C - triplePointDivisor A' B' C' }






def LineRatioPrincipalDivisors
    {k : Type u} [Field k] (W : WeierstrassCurve k) : AddSubgroup (PointDivisor W) :=
  AddSubgroup.closure (LineRatioPrincipalDivisorSet W)





def DivisorClassEquivalentByLineRatios
    {k : Type u} [Field k] (W : WeierstrassCurve k)
    (D E : PointDivisor W) : Prop :=
  D - E ∈ LineRatioPrincipalDivisors W











def DivisorClassGroupLawSum
    {k : Type u} [Field k]
    (W : WeierstrassCurve k)
    (O P Q S : W.toProjective.Point) : Prop :=
  DivisorClassEquivalentByLineRatios W
    (pointDivisor P + pointDivisor Q)
    (pointDivisor O + pointDivisor S)



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_geometric_group_law_23_19_divisorClass
