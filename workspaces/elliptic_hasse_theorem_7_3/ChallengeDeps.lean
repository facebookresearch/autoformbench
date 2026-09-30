import Mathlib



























noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_hasse_theorem_7_3

universe u v

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [IsAlgClosed K]
variable [Algebra.IsAlgebraic k K]




abbrev baseChange (E : WeierstrassCurve k) : WeierstrassCurve K :=
  E.map (algebraMap k K)


abbrev RationalPoint (E : WeierstrassCurve k) : Type u :=
  E.toAffine.Point


abbrev GeometricPoint (E : WeierstrassCurve k) : Type v :=
  (baseChange (K := K) E).toAffine.Point







noncomputable instance instFintypeAffinePoint
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) : Fintype W.toAffine.Point := by
  classical
  let S := {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2}
  haveI : Fintype S :=
    Fintype.subtype
      ((Finset.univ : Finset (F × F)).filter
        (fun xy => W.toAffine.Nonsingular xy.1 xy.2))
      (by
        intro xy
        simp)
  haveI : Fintype (WithTop S) := inferInstance
  exact Fintype.ofEquiv
    (WithTop S)
    W.toAffine.nonsingularPointEquiv.symm


noncomputable instance instFintypeRationalPoint
    [Fintype k] [DecidableEq k] (E : WeierstrassCurve k) :
    Fintype (RationalPoint E) := by
  change Fintype E.toAffine.Point
  infer_instance




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


def affine (x y : F) : Coords3 F :=
  (x, y, 1)


def infinity : Coords3 F :=
  (0, 1, 0)





def OnWeierstrass (E : WeierstrassCurve F) (P : Coords3 F) : Prop :=
  Y P ^ 2 * Z P + E.a₁ * X P * Y P * Z P + E.a₃ * Y P * Z P ^ 2 =
    X P ^ 3 + E.a₂ * X P ^ 2 * Z P + E.a₄ * X P * Z P ^ 2 + E.a₆ * Z P ^ 3

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


def HomogeneousOfDegree (d : ℕ) : Prop :=
  T.X.IsHomogeneous d ∧ T.Y.IsHomogeneous d ∧ T.Z.IsHomogeneous d

end ProjectiveTriple

abbrev PX : MvPolynomial (Fin 3) k := MvPolynomial.X (0 : Fin 3)
abbrev PY : MvPolynomial (Fin 3) k := MvPolynomial.X (1 : Fin 3)
abbrev PZ : MvPolynomial (Fin 3) k := MvPolynomial.X (2 : Fin 3)





def projectivePolynomial (E : WeierstrassCurve k) : MvPolynomial (Fin 3) k :=
  PY ^ 2 * PZ
    + MvPolynomial.C E.a₁ * PX * PY * PZ
    + MvPolynomial.C E.a₃ * PY * PZ ^ 2
    - PX ^ 3
    - MvPolynomial.C E.a₂ * PX ^ 2 * PZ
    - MvPolynomial.C E.a₄ * PX * PZ ^ 2
    - MvPolynomial.C E.a₆ * PZ ^ 3


def projectiveIdeal (E : WeierstrassCurve k) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ({projectivePolynomial E} : Set (MvPolynomial (Fin 3) k))


def projectivePolynomialAtTriple
    (E : WeierstrassCurve k) (T : ProjectiveTriple k) : MvPolynomial (Fin 3) k :=
  T.Y ^ 2 * T.Z
    + MvPolynomial.C E.a₁ * T.X * T.Y * T.Z
    + MvPolynomial.C E.a₃ * T.Y * T.Z ^ 2
    - T.X ^ 3
    - MvPolynomial.C E.a₂ * T.X ^ 2 * T.Z
    - MvPolynomial.C E.a₄ * T.X * T.Z ^ 2
    - MvPolynomial.C E.a₆ * T.Z ^ 3

namespace ProjectiveTriple





def NotAllInSourceIdeal (E : WeierstrassCurve k) (T : ProjectiveTriple k) : Prop :=
  ¬ (T.X ∈ projectiveIdeal E ∧ T.Y ∈ projectiveIdeal E ∧ T.Z ∈ projectiveIdeal E)





def RationalMapRepresentative
    (E₁ E₂ : WeierstrassCurve k) (T : ProjectiveTriple k) : Prop :=
  (∃ d : ℕ, T.HomogeneousOfDegree d) ∧
  T.NotAllInSourceIdeal E₁ ∧
  projectivePolynomialAtTriple E₂ T ∈ projectiveIdeal E₁

end ProjectiveTriple





def ProjectiveTriplesEquivalentOnSource
    (E : WeierstrassCurve k) (T U : ProjectiveTriple k) : Prop :=
  T.X * U.Y - U.X * T.Y ∈ projectiveIdeal E ∧
  T.X * U.Z - U.X * T.Z ∈ projectiveIdeal E ∧
  T.Y * U.Z - U.Y * T.Z ∈ projectiveIdeal E






structure IsProjectiveMorphismRepresentative
    (T : ProjectiveTriple k) (E₁ E₂ : WeierstrassCurve k) : Prop where
  rational_map_representative :
    T.RationalMapRepresentative E₁ E₂
  maps_defined_points :
    ∀ P : Coords3 K,
      Coords3.Nonzero P →
      Coords3.OnWeierstrass (baseChange (K := K) E₁) P →
      T.NonzeroAt (K := K) P →
      Coords3.OnWeierstrass (baseChange (K := K) E₂) (T.evalOver (K := K) P)
  regular_everywhere :
    ∀ P : Coords3 K,
      Coords3.Nonzero P →
      Coords3.OnWeierstrass (baseChange (K := K) E₁) P →
      ∃ U : ProjectiveTriple k,
        U.RationalMapRepresentative E₁ E₂ ∧
        ProjectiveTriplesEquivalentOnSource E₁ T U ∧
        U.NonzeroAt (K := K) P ∧
        Coords3.OnWeierstrass (baseChange (K := K) E₂) (U.evalOver (K := K) P)


def ProjectiveCoordsRepresentPoint
    (E : WeierstrassCurve k) (P : GeometricPoint (K := K) E) (Q : Coords3 K) : Prop :=
  match P with
  | 0 => Coords3.ProjectivelyEquivalent Q Coords3.infinity
  | .some x y _ => Coords3.ProjectivelyEquivalent Q (Coords3.affine x y)






def PointMapAgreesWithRepresentative
    (E₁ E₂ : WeierstrassCurve k) (T : ProjectiveTriple k)
    (φ : GeometricPoint (K := K) E₁ → GeometricPoint (K := K) E₂) : Prop :=
  ∀ (P : GeometricPoint (K := K) E₁) (Pcoords : Coords3 K) (U : ProjectiveTriple k),
    ProjectiveCoordsRepresentPoint (K := K) E₁ P Pcoords →
    U.RationalMapRepresentative E₁ E₂ →
    ProjectiveTriplesEquivalentOnSource E₁ T U →
    U.NonzeroAt (K := K) Pcoords →
    ProjectiveCoordsRepresentPoint (K := K) E₂ (φ P) (U.evalOver (K := K) Pcoords)








structure Hom [DecidableEq K]
    (E₁ E₂ : WeierstrassCurve k)
    [E₁.IsElliptic] [(baseChange (K := K) E₁).IsElliptic]
    [E₂.IsElliptic] [(baseChange (K := K) E₂).IsElliptic] where
  toPointMap : GeometricPoint (K := K) E₁ → GeometricPoint (K := K) E₂
  representative : ProjectiveTriple k
  morphism_representative :
    IsProjectiveMorphismRepresentative (K := K) representative E₁ E₂
  point_map_agrees_with_representative :
    PointMapAgreesWithRepresentative (K := K) E₁ E₂ representative toPointMap
  maps_zero : toPointMap 0 = 0
  map_add : ∀ P Q : GeometricPoint (K := K) E₁,
    toPointMap (P + Q) = toPointMap P + toPointMap Q

namespace Hom

variable [DecidableEq K]
variable {E₁ E₂ E₃ : WeierstrassCurve k}
variable [E₁.IsElliptic] [(baseChange (K := K) E₁).IsElliptic]
variable [E₂.IsElliptic] [(baseChange (K := K) E₂).IsElliptic]
variable [E₃.IsElliptic] [(baseChange (K := K) E₃).IsElliptic]


instance instCoeFunHom : CoeFun (Hom (K := K) E₁ E₂)
    (fun _ => GeometricPoint (K := K) E₁ → GeometricPoint (K := K) E₂) where
  coe φ := φ.toPointMap

end Hom


abbrev End [DecidableEq K]
    (E : WeierstrassCurve k)
    [E.IsElliptic] [(baseChange (K := K) E).IsElliptic] : Type _ :=
  Hom (K := K) E E

namespace End

variable [DecidableEq K]
variable {E : WeierstrassCurve k}
variable [E.IsElliptic] [(baseChange (K := K) E).IsElliptic]


def PointwiseSumIsZSMul (α β : End (K := K) E) (t : ℤ) : Prop :=
  ∀ P : GeometricPoint (K := K) E, α P + β P = t • P


def PointwiseCompIsZSMul (β α : End (K := K) E) (n : ℤ) : Prop :=
  ∀ P : GeometricPoint (K := K) E, β (α P) = n • P

end End




def frobeniusProjectiveTriple [Fintype k] : ProjectiveTriple k where
  X := PX ^ Fintype.card k
  Y := PY ^ Fintype.card k
  Z := PZ ^ Fintype.card k


























end Autoform_Elliptic_Curves_elliptic_hasse_theorem_7_3

end