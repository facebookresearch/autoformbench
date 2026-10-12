/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
















noncomputable section

open Polynomial
open scoped BigOperators

namespace Autoform_Elliptic_Curves_elliptic_theorem_22_11_Kohel

section SecT618

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






def NotAllInSourceIdeal (E : WeierstrassCurve K) (T : ProjectiveTriple K) : Prop :=
  ¬ (T.X ∈ weierstrassProjectiveIdeal E ∧
     T.Y ∈ weierstrassProjectiveIdeal E ∧
     T.Z ∈ weierstrassProjectiveIdeal E)

end ProjectiveTriple





def ProjectiveTriplesEquivalentOnSource
    (E : WeierstrassCurve K) (T U : ProjectiveTriple K) : Prop :=
  T.X * U.Y - U.X * T.Y ∈ weierstrassProjectiveIdeal E ∧
  T.X * U.Z - U.X * T.Z ∈ weierstrassProjectiveIdeal E ∧
  T.Y * U.Z - U.Y * T.Z ∈ weierstrassProjectiveIdeal E







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

end SecT618

section SecKohel

universe u v w



structure EllipticCurveWithJ (k : Type u) [Field k] (j : k) where
  curve : WeierstrassCurve k
  isElliptic : curve.IsElliptic
  j_eq : @WeierstrassCurve.j k _ curve isElliptic = j

attribute [instance] EllipticCurveWithJ.isElliptic

noncomputable scoped instance algebraicClosureDecidableEq
    (k : Type u) [Field k] : DecidableEq (AlgebraicClosure k) :=
  Classical.decEq _


abbrev GeometricCurveModel
    {k : Type u} [Field k] {j : k} (E : EllipticCurveWithJ k j) :
    WeierstrassCurve (AlgebraicClosure k) :=
  baseChangeWeierstrass
    (K := k) (AlgebraicClosure k) E.curve


abbrev GeometricPoint
    {k : Type u} [Field k] {j : k} (E : EllipticCurveWithJ k j) : Type u :=
  (GeometricCurve
    (K := AlgebraicClosure k) (AlgebraicClosure k)
    (GeometricCurveModel E)).Point


def kroneckerPrime (D : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then
    if (2 : ℤ) ∣ D then
      0
    else if D % 8 = 1 ∨ D % 8 = 7 then
      1
    else if D % 8 = 3 ∨ D % 8 = 5 then
      -1
    else
      0
  else
    ((Finset.univ.filter
      (fun x : Fin p =>
        (((x.val : ℤ) ^ (2 : ℕ) - D) % (p : ℤ) = 0))).card : ℤ) - 1




structure DirectedMultigraph (V : Type u) where
  edgeMultiplicity : V → V → ℕ

namespace DirectedMultigraph

variable {V : Type u} [DecidableEq V] [Fintype V]


def outDegreeIn (G : DirectedMultigraph V) (S : Finset V) (v : V) : ℕ :=
  ∑ w ∈ S, G.edgeMultiplicity v w


def Adj (G : DirectedMultigraph V) (v w : V) : Prop :=
  G.edgeMultiplicity v w ≠ 0 ∨ G.edgeMultiplicity w v ≠ 0


def SymmetricOn (G : DirectedMultigraph V) (S : Finset V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ S → w ∈ S →
    G.edgeMultiplicity v w = G.edgeMultiplicity w v


def ConnectedOn (G : DirectedMultigraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧
    ∀ ⦃v w : V⦄, v ∈ S → w ∈ S →
      Relation.ReflTransGen
        (fun a b : V => a ∈ S ∧ b ∈ S ∧ G.Adj a b) v w


def IsConnectedComponent (G : DirectedMultigraph V) (S : Finset V) : Prop :=
  G.ConnectedOn S ∧
    ∀ ⦃v w : V⦄, v ∈ S → G.Adj v w → w ∈ S

end DirectedMultigraph




def IsSquarefreeInteger (n : ℤ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ ((p : ℤ) ^ (2 : ℕ) ∣ n)


def IsNegativeFundamentalDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧
    ((D % 4 = 1 ∧ IsSquarefreeInteger D) ∨
      ∃ m : ℤ,
        D = 4 * m ∧
        IsSquarefreeInteger m ∧
        (m % 4 = 2 ∨ m % 4 = 3))


def IsFullRankZOrder
    {L : Type u} [Field L] [Algebra ℚ L] (R : Subring L) : Prop :=
  Module.Finite ℤ R ∧ Algebra.adjoin ℚ (R : Set L) = ⊤





structure ImaginaryQuadraticField where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra ℚ carrier]
  fundamentalDiscriminant : ℤ
  fundamentalDiscriminant_is_fundamental :
    IsNegativeFundamentalDiscriminant fundamentalDiscriminant
  finrank_eq_two : Module.finrank ℚ carrier = 2
  generated_by_sqrt_discriminant :
    ∃ α : carrier,
      Algebra.adjoin ℚ ({α} : Set carrier) = ⊤ ∧
        α * α = algebraMap ℚ carrier (fundamentalDiscriminant : ℚ)
  maximalOrder : Subring carrier
  maximalOrder_fullRank : IsFullRankZOrder maximalOrder
  maximalOrder_maximal :
    ∀ R : Subring carrier,
      IsFullRankZOrder R → maximalOrder ≤ R → R = maximalOrder

attribute [instance] ImaginaryQuadraticField.field
attribute [instance] ImaginaryQuadraticField.algebra


def MemZPlusFMaximalOrder
    (K : ImaginaryQuadraticField.{u}) (f : ℕ) (x : K.carrier) : Prop :=
  ∃ z : ℤ, ∃ y : K.carrier, y ∈ K.maximalOrder ∧
    x = algebraMap ℤ K.carrier z + algebraMap ℤ K.carrier (f : ℤ) * y




structure ImaginaryQuadraticOrder (K : ImaginaryQuadraticField.{u}) where
  toSubring : Subring K.carrier
  conductor : ℕ
  conductor_pos : 0 < conductor
  mem_iff_mem_z_plus_f_maximalOrder :
    ∀ x : K.carrier,
      x ∈ toSubring ↔ MemZPlusFMaximalOrder K conductor x

namespace ImaginaryQuadraticOrder


def discr {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) : ℤ :=
  (O.conductor : ℤ) ^ (2 : ℕ) * K.fundamentalDiscriminant

end ImaginaryQuadraticOrder




def idealCarrierInField
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring) : Set K.carrier :=
  Subtype.val '' (I : Set O.toSubring)


def IsIdealMultiplier
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring)
    (a : K.carrier) : Prop :=
  ∀ ⦃x : K.carrier⦄,
    x ∈ idealCarrierInField O I →
      a * x ∈ idealCarrierInField O I




abbrev geometricCurve
    {k : Type u} [Field k] {j : k} (E : EllipticCurveWithJ k j) :
    WeierstrassCurve (AlgebraicClosure k) :=
  baseChangeWeierstrass (K := k) (AlgebraicClosure k) E.curve


abbrev GeometricEndPoint
    {k : Type u} [Field k] {j : k} (E : EllipticCurveWithJ k j) : Type u :=
  (GeometricCurve
    (K := AlgebraicClosure k) (AlgebraicClosure k) (geometricCurve E)).Point




structure VolcanoLevels (V : Type u) where
  depth : ℕ
  level : ℕ → Finset V

namespace VolcanoLevels

variable {V : Type u} [DecidableEq V]


def IsPartitionOf (L : VolcanoLevels V) (S : Finset V) : Prop :=
  (∀ i : ℕ, i ≤ L.depth → (L.level i).Nonempty) ∧
  (∀ v : V, v ∈ S ↔ ∃ i : ℕ, i ≤ L.depth ∧ v ∈ L.level i) ∧
    ∀ ⦃i j : ℕ⦄, i ≤ L.depth → j ≤ L.depth → i ≠ j →
      Disjoint (L.level i) (L.level j)

end VolcanoLevels


def IsEllVolcano {V : Type u} [DecidableEq V] [Fintype V]
    (ℓ : ℕ) (G : DirectedMultigraph V) (S : Finset V)
    (L : VolcanoLevels V) : Prop :=
  G.ConnectedOn S ∧
  G.SymmetricOn S ∧
  L.IsPartitionOf S ∧
  (∃ r : ℕ, r ≤ 2 ∧
    ∀ v : V, v ∈ L.level 0 →
      G.outDegreeIn (L.level 0) v = r) ∧
  (∀ i : ℕ, 0 < i → i ≤ L.depth →
    ∀ v : V, v ∈ L.level i →
      G.outDegreeIn (L.level (i - 1)) v = 1) ∧
  (∀ ⦃i j : ℕ⦄, i ≤ L.depth → j ≤ L.depth →
    ∀ ⦃v w : V⦄, v ∈ L.level i → w ∈ L.level j →
      G.edgeMultiplicity v w ≠ 0 →
        (i = 0 ∧ j = 0) ∨ i + 1 = j ∨ j + 1 = i) ∧
  (∀ i : ℕ, i < L.depth →
    ∀ v : V, v ∈ L.level i →
      G.outDegreeIn S v = ℓ + 1)

end SecKohel

end Autoform_Elliptic_Curves_elliptic_theorem_22_11_Kohel

end
