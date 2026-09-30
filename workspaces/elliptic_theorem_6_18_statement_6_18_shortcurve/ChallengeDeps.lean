import Mathlib





























noncomputable section

open Polynomial

namespace Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18_shortcurve

universe u v

variable {K : Type u} [Field K]






def shortWeierstrass (A B : K) : WeierstrassCurve K where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B









abbrev GeometricShortCurve
    (Ω : Type v) [Field Ω] [Algebra K Ω] (A B : K) : WeierstrassCurve.Affine Ω :=
  shortWeierstrass (algebraMap K Ω A) (algebraMap K Ω B)










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


def baseChange (Ω : Type v) [Field Ω] [Algebra K Ω] : StandardAffineMap Ω where
  xNum := F.xNum.map (algebraMap K Ω)
  xDen := F.xDen.map (algebraMap K Ω)
  yNum := F.yNum.map (algebraMap K Ω)
  yDen := F.yDen.map (algebraMap K Ω)


def xCoordOver {Ω : Type v} [Field Ω] [Algebra K Ω] (x : Ω) : Ω :=
  (F.baseChange Ω).xCoord x


def yCoordOver {Ω : Type v} [Field Ω] [Algebra K Ω] (x y : Ω) : Ω :=
  (F.baseChange Ω).yCoord x y


def xDenEvalOver {Ω : Type v} [Field Ω] [Algebra K Ω] (x : Ω) : Ω :=
  ((F.baseChange Ω).xDen).eval x


def yDenEvalOver {Ω : Type v} [Field Ω] [Algebra K Ω] (x : Ω) : Ω :=
  ((F.baseChange Ω).yDen).eval x








def degree : ℕ :=
  max F.xNum.natDegree F.xDen.natDegree

end StandardAffineMap


def PolynomialCoprime (p q : Polynomial K) : Prop :=
  ∃ a b : Polynomial K, a * p + b * q = 1




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
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (T : ProjectiveTriple K) (A₁ B₁ A₂ B₂ : K) : Prop where
  rational_map_representative :
    T.RationalMapRepresentative A₁ B₁ A₂ B₂
  maps_defined_geometric_points :
    ∀ P : Coords3 Ω,
      Coords3.Nonzero P →
      Coords3.OnShortWeierstrass (algebraMap K Ω A₁) (algebraMap K Ω B₁) P →
      T.NonzeroAtOver P →
      Coords3.OnShortWeierstrass
        (algebraMap K Ω A₂) (algebraMap K Ω B₂) (T.evalOver P)
  regular_everywhere_geometric :
    ∀ P : Coords3 Ω,
      Coords3.Nonzero P →
      Coords3.OnShortWeierstrass (algebraMap K Ω A₁) (algebraMap K Ω B₁) P →
      ∃ U : ProjectiveTriple K,
        U.RationalMapRepresentative A₁ B₁ A₂ B₂ ∧
        ProjectiveTriplesEquivalentOnSource A₁ B₁ T U ∧
        U.NonzeroAtOver P ∧
        Coords3.OnShortWeierstrass
          (algebraMap K Ω A₂) (algebraMap K Ω B₂) (U.evalOver P)






def ProjectiveTripleRepresentsStandardAffineMap
    {Ω : Type v} [Field Ω] [Algebra K Ω]
    (T : ProjectiveTriple K) (F : StandardAffineMap K) : Prop :=
  ∀ x y : Ω,
    F.xDenEvalOver x ≠ 0 →
    F.yDenEvalOver x ≠ 0 →
    Coords3.ProjectivelyEquivalent
      (T.evalOver (Coords3.affine x y))
      (F.xCoordOver x, F.yCoordOver x y, 1)








def AffineFormulaForPointMap
    {Ω : Type v} [Field Ω] [Algebra K Ω] [DecidableEq Ω]
    (A₁ B₁ A₂ B₂ : K)
    (F : StandardAffineMap K)
    (φ : (GeometricShortCurve (K := K) Ω A₁ B₁).Point →
         (GeometricShortCurve (K := K) Ω A₂ B₂).Point) : Prop :=
  φ 0 = 0 ∧
  (∀ P : (GeometricShortCurve (K := K) Ω A₁ B₁).Point,
    match P with
    | 0 => True
    | .some x y hxy =>
        F.xDenEvalOver x ≠ 0 →
        F.yDenEvalOver x ≠ 0 →
        ∃ hImage,
          φ (.some x y hxy) =
            .some (F.xCoordOver x) (F.yCoordOver x y) hImage) ∧
  (∀ P : (GeometricShortCurve (K := K) Ω A₁ B₁).Point,
    match P with
    | 0 => True
    | .some x y hxy =>
        F.xDenEvalOver x = 0 → φ (.some x y hxy) = 0)







def AffineKernelControlledByXDen
    {Ω : Type v} [Field Ω] [Algebra K Ω] [DecidableEq Ω]
    (A₁ B₁ A₂ B₂ : K)
    (F : StandardAffineMap K)
    (φ : (GeometricShortCurve (K := K) Ω A₁ B₁).Point →
         (GeometricShortCurve (K := K) Ω A₂ B₂).Point) : Prop :=
  ∀ P : (GeometricShortCurve (K := K) Ω A₁ B₁).Point,
    match P with
    | 0 => True
    | .some x _ _ => φ P = 0 ↔ F.xDenEvalOver x = 0













structure IsIsogenyInStandardForm
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (A₁ B₁ A₂ B₂ : K)
    [hE₁ : (GeometricShortCurve (K := K) Ω A₁ B₁).IsElliptic]
    [hE₂ : (GeometricShortCurve (K := K) Ω A₂ B₂).IsElliptic]
    (F : StandardAffineMap K)
    (T : ProjectiveTriple K)
    (φ : (GeometricShortCurve (K := K) Ω A₁ B₁).Point →
         (GeometricShortCurve (K := K) Ω A₂ B₂).Point) : Prop where
  x_lowest_terms : PolynomialCoprime F.xNum F.xDen
  y_lowest_terms : PolynomialCoprime F.yNum F.yDen
  xDen_nonzero : F.xDen ≠ 0
  yDen_nonzero : F.yDen ≠ 0
  xden_yden_same_geometric_roots :
    ∀ x : Ω, F.xDenEvalOver x = 0 ↔ F.yDenEvalOver x = 0
  projective_represents_affine_formula :
    ProjectiveTripleRepresentsStandardAffineMap (Ω := Ω) T F
  morphism_representative :
    IsProjectiveMorphismRepresentative (Ω := Ω) T A₁ B₁ A₂ B₂
  affine_formula_for_point_map :
    AffineFormulaForPointMap (Ω := Ω) A₁ B₁ A₂ B₂ F φ
  affine_kernel_iff_xden_zero :
    AffineKernelControlledByXDen (Ω := Ω) A₁ B₁ A₂ B₂ F φ
  maps_zero : φ 0 = 0
  group_hom :
    ∀ P Q : (GeometricShortCurve (K := K) Ω A₁ B₁).Point,
      φ (P + Q) = φ P + φ Q
  geometrically_surjective : Function.Surjective φ
  nonconstant : ∃ P : (GeometricShortCurve (K := K) Ω A₁ B₁).Point, φ P ≠ 0



variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
variable {A B : K}
variable [hE : (GeometricShortCurve (K := K) Ω A B).IsElliptic]







structure StandardEndomorphismData
    (φ : AddMonoid.End (GeometricShortCurve (K := K) Ω A B).Point) where
  F : StandardAffineMap K
  T : ProjectiveTriple K
  isogeny :
    IsIsogenyInStandardForm (Ω := Ω) A B A B F T (fun P => φ P)














structure ShortWeierstrassEndomorphism (A B : K)
    (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    [hE : (GeometricShortCurve Ω A B).IsElliptic] where
  toEnd : AddMonoid.End (GeometricShortCurve Ω A B).Point
  algebraic :
    toEnd = 0 ∨ Nonempty (StandardEndomorphismData (Ω := Ω) (A := A) (B := B) toEnd)

attribute [coe] ShortWeierstrassEndomorphism.toEnd

instance instCoeFunShortWeierstrassEndomorphism :
    CoeFun (ShortWeierstrassEndomorphism A B Ω)
      (fun _ => (GeometricShortCurve (K := K) Ω A B).Point →
        (GeometricShortCurve (K := K) Ω A B).Point) where
  coe α := fun P => α.toEnd P


theorem has_standardData_of_nonzero
    (α : ShortWeierstrassEndomorphism A B Ω)
    (hα : α.toEnd ≠ 0) :
    Nonempty (StandardEndomorphismData (Ω := Ω) (A := A) (B := B) α.toEnd) := by
  rcases α.algebraic with hzero | hdata
  · exact (hα hzero).elim
  · exact hdata





noncomputable def chosenStandardData
    (α : ShortWeierstrassEndomorphism A B Ω)
    (hα : α.toEnd ≠ 0) :
    StandardEndomorphismData (Ω := Ω) (A := A) (B := B) α.toEnd :=
  Classical.choice (has_standardData_of_nonzero (A := A) (B := B) (Ω := Ω) α hα)










noncomputable def degree (α : ShortWeierstrassEndomorphism A B Ω) : ℕ := by
  classical
  exact if hα : α.toEnd = 0 then
    0
  else
    (chosenStandardData (A := A) (B := B) (Ω := Ω) α hα).F.degree















end Autoform_Elliptic_Curves_elliptic_theorem_6_18_statement_6_18_shortcurve

end