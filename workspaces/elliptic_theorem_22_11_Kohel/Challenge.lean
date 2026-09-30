import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Quotient
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import ChallengeDeps

open Autoform_Elliptic_Curves_elliptic_theorem_22_11_Kohel















noncomputable section

open Polynomial
open scoped BigOperators

namespace Autoform_Elliptic_Curves_elliptic_theorem_22_11_Kohel

section SecT618

universe u v

variable {K : Type u} [Field K]


theorem geometricCurve_isElliptic
    {Ω : Type v} [Field Ω] [Algebra K Ω]
    (E : WeierstrassCurve K) [E.IsElliptic] :
    (GeometricCurve (K := K) Ω E).IsElliptic := by
  sorry

attribute [instance] geometricCurve_isElliptic


noncomputable def polynomialFunction (E : WeierstrassCurve K) (p : Polynomial K) :
    FunctionField E :=
  p.eval₂ (algebraMap K (FunctionField E)) (functionFieldX E)

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

namespace ProjectiveTriple


def HomogeneousOfDegree (T : ProjectiveTriple K) (d : ℕ) : Prop :=
  T.X.IsHomogeneous d ∧ T.Y.IsHomogeneous d ∧ T.Z.IsHomogeneous d










def RationalMapRepresentative
    (E₁ E₂ : WeierstrassCurve K) (T : ProjectiveTriple K) : Prop :=
  (∃ d : ℕ, T.HomogeneousOfDegree d) ∧
  T.NotAllInSourceIdeal E₁ ∧
  weierstrassProjectivePolynomialAtTriple E₂ T ∈ weierstrassProjectiveIdeal E₁

end ProjectiveTriple






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


theorem finite_dimensional (D : FunctionFieldPullbackData E₁ E₂ T) :
    FiniteDimensional D.imageField (FunctionField E₁) :=
  D.finite_extension

end FunctionFieldPullbackData






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








structure AlgebraicIsogenyData
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E₁ E₂ : WeierstrassCurve K)
    [hE₁ : (GeometricCurve (K := K) Ω E₁).IsElliptic]
    [hE₂ : (GeometricCurve (K := K) Ω E₂).IsElliptic]
    (φ : (GeometricCurve (K := K) Ω E₁).Point →+
         (GeometricCurve (K := K) Ω E₂).Point) where
  T : ProjectiveTriple K
  isogeny :
    IsIsogenyRepresentative (Ω := Ω) E₁ E₂ T (fun P => φ P)
  functionField : FunctionFieldPullbackData E₁ E₂ T





theorem algebraicIsogeny_degree_unique
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E₁ E₂ : WeierstrassCurve K)
    [hE₁ : (GeometricCurve (K := K) Ω E₁).IsElliptic]
    [hE₂ : (GeometricCurve (K := K) Ω E₂).IsElliptic]
    (φ : (GeometricCurve (K := K) Ω E₁).Point →+
         (GeometricCurve (K := K) Ω E₂).Point)
    (D₁ D₂ : AlgebraicIsogenyData (Ω := Ω) E₁ E₂ φ) :
    D₁.functionField.degree = D₂.functionField.degree := by
  sorry


structure EllipticCurveIsogeny
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E₁ E₂ : WeierstrassCurve K)
    [hE₁ : (GeometricCurve (K := K) Ω E₁).IsElliptic]
    [hE₂ : (GeometricCurve (K := K) Ω E₂).IsElliptic] where
  toHom : (GeometricCurve (K := K) Ω E₁).Point →+
    (GeometricCurve (K := K) Ω E₂).Point
  algebraic : AlgebraicIsogenyData (Ω := Ω) E₁ E₂ toHom

namespace EllipticCurveIsogeny

variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
variable {E₁ E₂ : WeierstrassCurve K}
variable [hE₁ : (GeometricCurve (K := K) Ω E₁).IsElliptic]
variable [hE₂ : (GeometricCurve (K := K) Ω E₂).IsElliptic]


noncomputable def degree (φ : EllipticCurveIsogeny (Ω := Ω) E₁ E₂) : ℕ :=
  φ.algebraic.functionField.degree


abbrev kernel (φ : EllipticCurveIsogeny (Ω := Ω) E₁ E₂) :
    AddSubgroup (GeometricCurve (K := K) Ω E₁).Point :=
  φ.toHom.ker





def IsSeparable (φ : EllipticCurveIsogeny (Ω := Ω) E₁ E₂) : Prop :=
  Nat.card φ.kernel = φ.degree


def HasCyclicKernel (φ : EllipticCurveIsogeny (Ω := Ω) E₁ E₂) : Prop :=
  IsAddCyclic φ.kernel

end EllipticCurveIsogeny






def IsAlgebraicHom
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E₁ E₂ : WeierstrassCurve K)
    [hE₁ : (GeometricCurve (K := K) Ω E₁).IsElliptic]
    [hE₂ : (GeometricCurve (K := K) Ω E₂).IsElliptic]
    (φ : (GeometricCurve (K := K) Ω E₁).Point →+
         (GeometricCurve (K := K) Ω E₂).Point) : Prop :=
  φ = 0 ∨ Nonempty (AlgebraicIsogenyData (Ω := Ω) E₁ E₂ φ)


theorem EndSubring_one_mem
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve K)
    [hE : (GeometricCurve (K := K) Ω E).IsElliptic] :
    IsAlgebraicHom (Ω := Ω) E E
      (1 : AddMonoid.End (GeometricCurve (K := K) Ω E).Point) := by
  sorry


theorem EndSubring_add_mem
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve K)
    [hE : (GeometricCurve (K := K) Ω E).IsElliptic]
    (a b : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)
    (ha : IsAlgebraicHom (Ω := Ω) E E a) (hb : IsAlgebraicHom (Ω := Ω) E E b) :
    IsAlgebraicHom (Ω := Ω) E E (a + b) := by
  sorry


theorem EndSubring_neg_mem
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve K)
    [hE : (GeometricCurve (K := K) Ω E).IsElliptic]
    (x : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)
    (hx : IsAlgebraicHom (Ω := Ω) E E x) :
    IsAlgebraicHom (Ω := Ω) E E (-x) := by
  sorry


theorem EndSubring_mul_mem
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve K)
    [hE : (GeometricCurve (K := K) Ω E).IsElliptic]
    (a b : AddMonoid.End (GeometricCurve (K := K) Ω E).Point)
    (ha : IsAlgebraicHom (Ω := Ω) E E a) (hb : IsAlgebraicHom (Ω := Ω) E E b) :
    IsAlgebraicHom (Ω := Ω) E E (a * b) := by
  sorry





def EndSubring
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve K)
    [hE : (GeometricCurve (K := K) Ω E).IsElliptic] :
    Subring (AddMonoid.End (GeometricCurve (K := K) Ω E).Point) where
  carrier := {φ | IsAlgebraicHom (Ω := Ω) E E φ}
  zero_mem' := by
    exact Or.inl rfl
  one_mem' := EndSubring_one_mem (K := K) (Ω := Ω) E
  add_mem' := fun {a b} ha hb => EndSubring_add_mem (K := K) (Ω := Ω) E a b ha hb
  neg_mem' := fun {x} hx => EndSubring_neg_mem (K := K) (Ω := Ω) E x hx
  mul_mem' := fun {a b} ha hb => EndSubring_mul_mem (K := K) (Ω := Ω) E a b ha hb


abbrev End
    {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (E : WeierstrassCurve K)
    [hE : (GeometricCurve (K := K) Ω E).IsElliptic] : Type _ :=
  (EndSubring (K := K) (Ω := Ω) E : Type _)

section DegreeDualTrace

variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
variable {E : WeierstrassCurve K}
variable [hE : (GeometricCurve (K := K) Ω E).IsElliptic]


theorem endomorphism_has_isogeny_data
    (α : End (K := K) (Ω := Ω) E) (hα : α ≠ 0) :
    Nonempty (AlgebraicIsogenyData (K := K) (Ω := Ω) E E α.1) := by
  sorry


noncomputable def chosenEndomorphismData
    (α : End (K := K) (Ω := Ω) E) (hα : α ≠ 0) :
    AlgebraicIsogenyData (K := K) (Ω := Ω) E E α.1 :=
  Classical.choice (endomorphism_has_isogeny_data (K := K) (Ω := Ω) α hα)

open Classical in




noncomputable def endomorphismDegree
    (α : End (K := K) (Ω := Ω) E) : ℕ :=
  if hα : α = 0 then 0
  else (chosenEndomorphismData (K := K) (Ω := Ω) α hα).functionField.degree


def IsDualEndomorphism
    (α β : End (K := K) (Ω := Ω) E) : Prop :=
  (α = 0 ∧ β = 0) ∨
    (α ≠ 0 ∧
      β * α = (endomorphismDegree (K := K) (Ω := Ω) α : End (K := K) (Ω := Ω) E) ∧
      α * β = (endomorphismDegree (K := K) (Ω := Ω) α : End (K := K) (Ω := Ω) E))


theorem exists_unique_dualEnd
    (α : End (K := K) (Ω := Ω) E) :
    ∃! β : End (K := K) (Ω := Ω) E,
      IsDualEndomorphism (K := K) (Ω := Ω) α β := by
  sorry


noncomputable def dualEnd
    (α : End (K := K) (Ω := Ω) E) : End (K := K) (Ω := Ω) E :=
  Classical.choose (ExistsUnique.exists (exists_unique_dualEnd (K := K) (Ω := Ω) α))


theorem dualEnd_spec
    (α : End (K := K) (Ω := Ω) E) :
    IsDualEndomorphism (K := K) (Ω := Ω) α (dualEnd (K := K) (Ω := Ω) α) :=
  Classical.choose_spec (ExistsUnique.exists (exists_unique_dualEnd (K := K) (Ω := Ω) α))


def HasEndomorphismTrace
    (α : End (K := K) (Ω := Ω) E) (t : ℤ) : Prop :=
  α + dualEnd (K := K) (Ω := Ω) α = (t : End (K := K) (Ω := Ω) E)


theorem exists_unique_endomorphismTrace
    (α : End (K := K) (Ω := Ω) E) :
    ∃! t : ℤ, HasEndomorphismTrace (K := K) (Ω := Ω) α t := by
  sorry


noncomputable def endomorphismTrace
    (α : End (K := K) (Ω := Ω) E) : ℤ :=
  Classical.choose
    (ExistsUnique.exists (exists_unique_endomorphismTrace (K := K) (Ω := Ω) α))


theorem endomorphismTrace_spec
    (α : End (K := K) (Ω := Ω) E) :
    HasEndomorphismTrace (K := K) (Ω := Ω) α
      (endomorphismTrace (K := K) (Ω := Ω) α) :=
  Classical.choose_spec
    (ExistsUnique.exists (exists_unique_endomorphismTrace (K := K) (Ω := Ω) α))

end DegreeDualTrace

end SecT618

section SecKohel

universe u v w


theorem ellipticCurveWithJ_exists
    (k : Type u) [Field k] (j : k) : Nonempty (EllipticCurveWithJ k j) := by
  sorry


noncomputable def chosenEllipticCurveWithJ
    (k : Type u) [Field k] (j : k) : EllipticCurveWithJ k j :=
  Classical.choice (ellipticCurveWithJ_exists k j)










structure CyclicIsogenyKernelFrom
    (k : Type u) [Field k] {j₁ : k}
    (E₁ : EllipticCurveWithJ k j₁) (ℓ : ℕ) (j₂ : k) where
  kernel : AddSubgroup (GeometricPoint E₁)
  cyclic : IsAddCyclic kernel
  card_eq_degree : Nat.card kernel = ℓ
  realized :
    ∃ E₂ : EllipticCurveWithJ k j₂,
      ∃ φ : EllipticCurveIsogeny
          (K := AlgebraicClosure k) (Ω := AlgebraicClosure k)
          (GeometricCurveModel E₁) (GeometricCurveModel E₂),
        φ.degree = ℓ ∧
        φ.IsSeparable ∧
        φ.kernel = kernel


abbrev CyclicIsogenyKernelBetweenJ
    (k : Type u) [Field k] (ℓ : ℕ) (j₁ j₂ : k) : Type u :=
  CyclicIsogenyKernelFrom k (chosenEllipticCurveWithJ k j₁) ℓ j₂


theorem cyclicIsogenyKernel_count_independent_of_source
    (k : Type u) [Field k] (ℓ : ℕ) {j₁ : k}
    (E₁ E₁' : EllipticCurveWithJ k j₁) (j₂ : k) :
    Nat.card (CyclicIsogenyKernelFrom k E₁ ℓ j₂) =
      Nat.card (CyclicIsogenyKernelFrom k E₁' ℓ j₂) := by
  sorry









noncomputable def ellIsogenyGraph
    (k : Type u) [Field k] (ℓ : ℕ) : DirectedMultigraph k where
  edgeMultiplicity j₁ j₂ :=
    Nat.card (CyclicIsogenyKernelBetweenJ k ℓ j₁ j₂)

theorem idealMultiplier_zero
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring) :
    IsIdealMultiplier O I 0 := by
  sorry

theorem idealMultiplier_one
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring) :
    IsIdealMultiplier O I 1 := by
  sorry

theorem idealMultiplier_add
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring)
    {a b : K.carrier} :
    IsIdealMultiplier O I a → IsIdealMultiplier O I b →
      IsIdealMultiplier O I (a + b) := by
  sorry

theorem idealMultiplier_neg
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring)
    {a : K.carrier} :
    IsIdealMultiplier O I a → IsIdealMultiplier O I (-a) := by
  sorry

theorem idealMultiplier_mul
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring)
    {a b : K.carrier} :
    IsIdealMultiplier O I a → IsIdealMultiplier O I b →
      IsIdealMultiplier O I (a * b) := by
  sorry


def idealMultiplierRing
    {K : ImaginaryQuadraticField.{u}}
    (O : ImaginaryQuadraticOrder K) (I : Ideal O.toSubring) :
    Subring K.carrier where
  carrier := {a | IsIdealMultiplier O I a}
  zero_mem' := idealMultiplier_zero O I
  one_mem' := idealMultiplier_one O I
  add_mem' := by
    intro a b ha hb
    exact idealMultiplier_add O I ha hb
  neg_mem' := by
    intro a ha
    exact idealMultiplier_neg O I ha
  mul_mem' := by
    intro a b ha hb
    exact idealMultiplier_mul O I ha hb





structure ProperIdeal
    {K : ImaginaryQuadraticField.{u}} (O : ImaginaryQuadraticOrder K) where
  toIdeal : Ideal O.toSubring
  nonzero : toIdeal ≠ ⊥
  finite_quotient : Finite (O.toSubring ⧸ toIdeal)
  multiplier_ring_eq_order : idealMultiplierRing O toIdeal = O.toSubring

namespace ProperIdeal

variable {K : ImaginaryQuadraticField.{u}}
variable {O : ImaginaryQuadraticOrder K}


noncomputable def norm (I : ProperIdeal O) : ℕ :=
  letI : Finite (O.toSubring ⧸ I.toIdeal) := I.finite_quotient
  Nat.card (O.toSubring ⧸ I.toIdeal)


def IsPrincipal (I : ProperIdeal O) : Prop :=
  ∃ a : O.toSubring, a ≠ 0 ∧ I.toIdeal = Ideal.span ({a} : Set O.toSubring)

end ProperIdeal

theorem topIdeal_ne_bot {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} : (⊤ : Ideal O.toSubring) ≠ ⊥ := by
  sorry

theorem topIdeal_finite {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} :
    Finite (O.toSubring ⧸ (⊤ : Ideal O.toSubring)) := by
  sorry

theorem topIdeal_multiplier {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} :
    idealMultiplierRing O (⊤ : Ideal O.toSubring) = O.toSubring := by
  sorry

namespace ProperIdeal

variable {K : ImaginaryQuadraticField.{u}}
variable {O : ImaginaryQuadraticOrder K}


def one : ProperIdeal O where
  toIdeal := ⊤
  nonzero := topIdeal_ne_bot
  finite_quotient := topIdeal_finite
  multiplier_ring_eq_order := topIdeal_multiplier

end ProperIdeal

theorem mulIdeal_ne_bot {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} (I J : ProperIdeal O) :
    I.toIdeal * J.toIdeal ≠ ⊥ := by
  sorry

theorem mulIdeal_finite {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} (I J : ProperIdeal O) :
    Finite (O.toSubring ⧸ (I.toIdeal * J.toIdeal)) := by
  sorry

theorem mulIdeal_proper {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} (I J : ProperIdeal O) :
    idealMultiplierRing O (I.toIdeal * J.toIdeal) = O.toSubring := by
  sorry

namespace ProperIdeal

variable {K : ImaginaryQuadraticField.{u}}
variable {O : ImaginaryQuadraticOrder K}


def mul (I J : ProperIdeal O) : ProperIdeal O where
  toIdeal := I.toIdeal * J.toIdeal
  nonzero := mulIdeal_ne_bot I J
  finite_quotient := mulIdeal_finite I J
  multiplier_ring_eq_order := mulIdeal_proper I J


def pow (I : ProperIdeal O) : ℕ → ProperIdeal O
  | 0 => one
  | n + 1 => mul (pow I n) I

end ProperIdeal


theorem exists_positive_principal_power {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} (I : ProperIdeal O) :
    ∃ n : ℕ, 0 < n ∧ ProperIdeal.IsPrincipal (ProperIdeal.pow I n) := by
  sorry

namespace ProperIdeal

variable {K : ImaginaryQuadraticField.{u}}
variable {O : ImaginaryQuadraticOrder K}

open Classical in




noncomputable def classOrder (I : ProperIdeal O) : ℕ :=
  Nat.find (exists_positive_principal_power I)

end ProperIdeal


structure ProperIdealClassOfPrimeNorm
    {K : ImaginaryQuadraticField.{u}}
    {O : ImaginaryQuadraticOrder K} (ℓ : ℕ) where
  ideal : ProperIdeal O
  norm_eq_ell : ideal.norm = ℓ


abbrev geometricEndomorphismRing
    (k : Type u) [Field k] {j : k} (E : EllipticCurveWithJ k j) : Type u :=
  End
    (K := AlgebraicClosure k) (Ω := AlgebraicClosure k) (geometricCurve E)


theorem qPowerFrobenius_nonsingular
    (k : Type u) [Field k] [Fintype k]
    {j : k} (E : EllipticCurveWithJ k j)
    {x y : AlgebraicClosure k}
    (h :
      (GeometricCurve
        (K := AlgebraicClosure k) (AlgebraicClosure k)
        (geometricCurve E)).Nonsingular x y) :
    (GeometricCurve
      (K := AlgebraicClosure k) (AlgebraicClosure k)
      (geometricCurve E)).Nonsingular
        (x ^ Fintype.card k) (y ^ Fintype.card k) := by
  sorry


def qPowerFrobeniusPointMap
    (k : Type u) [Field k] [Fintype k]
    {j : k} (E : EllipticCurveWithJ k j) :
    GeometricEndPoint E → GeometricEndPoint E
  | 0 => 0
  | .some x y h =>
      .some (x ^ Fintype.card k) (y ^ Fintype.card k)
        (qPowerFrobenius_nonsingular k E h)


theorem qPowerFrobeniusPointMap_add
    (k : Type u) [Field k] [Fintype k]
    {j : k} (E : EllipticCurveWithJ k j)
    (P Q : GeometricEndPoint E) :
    qPowerFrobeniusPointMap k E (P + Q) =
      qPowerFrobeniusPointMap k E P + qPowerFrobeniusPointMap k E Q := by
  sorry


def qPowerFrobeniusHom
    (k : Type u) [Field k] [Fintype k]
    {j : k} (E : EllipticCurveWithJ k j) :
    AddMonoid.End (GeometricEndPoint E) where
  toFun := qPowerFrobeniusPointMap k E
  map_zero' := rfl
  map_add' := qPowerFrobeniusPointMap_add k E


theorem qPowerFrobenius_algebraic
    (k : Type u) [Field k] [Fintype k]
    {j : k} (E : EllipticCurveWithJ k j) :
    Nonempty
      (AlgebraicIsogenyData
        (K := AlgebraicClosure k) (Ω := AlgebraicClosure k)
        (geometricCurve E) (geometricCurve E)
        (qPowerFrobeniusHom k E)) := by
  sorry


def frobeniusEnd
    (k : Type u) [Field k] [Fintype k]
    {j : k} (E : EllipticCurveWithJ k j) :
    geometricEndomorphismRing k E :=
  ⟨qPowerFrobeniusHom k E,
    Or.inr (qPowerFrobenius_algebraic k E)⟩


noncomputable def ellipticCurveFrobeniusTrace
    (k : Type u) [Field k] [Fintype k]
    {j : k} (E : EllipticCurveWithJ k j) : ℤ :=
  endomorphismTrace
    (K := AlgebraicClosure k) (Ω := AlgebraicClosure k)
    (frobeniusEnd k E)


structure IsGeometricEndomorphismRingOf
    (k : Type u) [Field k] [Fintype k]
    (q : ℕ) {j : k} (E : EllipticCurveWithJ k j)
    {K : ImaginaryQuadraticField.{u}} (O : ImaginaryQuadraticOrder K) : Prop where
  finite_field_cardinality : Fintype.card k = q
  ring_equiv : Nonempty (geometricEndomorphismRing k E ≃+* O.toSubring)


structure IsFrobeniusTraceOf
    (k : Type u) [Field k] [Fintype k]
    (q : ℕ) {j : k} (E : EllipticCurveWithJ k j) (t : ℤ) : Prop where
  finite_field_cardinality : Fintype.card k = q
  trace_eq : t = ellipticCurveFrobeniusTrace k E


structure OrdinaryCMJData
    (k : Type u) [Field k] [Fintype k]
    (q : ℕ) (j : k) (K : ImaginaryQuadraticField.{u}) where
  curve : EllipticCurveWithJ k j
  endOrder : ImaginaryQuadraticOrder K
  isEndRing : IsGeometricEndomorphismRingOf k q curve endOrder
  frobeniusTrace : ℤ
  isFrobeniusTrace : IsFrobeniusTraceOf k q curve frobeniusTrace


def IsOrdinaryJ
    (k : Type u) [Field k] [Fintype k]
    (q : ℕ) (j : k) : Prop :=
  ∃ K : ImaginaryQuadraticField.{u}, Nonempty (OrdinaryCMJData k q j K)


structure IsOrdinaryComponent
    (k : Type u) [Field k] [Fintype k] [DecidableEq k]
    (q ℓ : ℕ) (V : Finset k) : Prop where
  component :
    DirectedMultigraph.IsConnectedComponent (ellIsogenyGraph k ℓ) V
  ordinary :
    ∀ j : k, j ∈ V → IsOrdinaryJ k q j


structure KohelTheorem22_11Conclusion
    (k : Type u) [Field k] [Fintype k] [DecidableEq k]
    (q ℓ : ℕ) (V : Finset k) where

  levels : VolcanoLevels k

  is_volcano :
    IsEllVolcano ℓ (ellIsogenyGraph k ℓ) V levels

  level_subset_component :
    ∀ i : ℕ, i ≤ levels.depth → levels.level i ⊆ V

  K : ImaginaryQuadraticField.{u}

  orderAtLevel :
    (i : ℕ) → i ≤ levels.depth → ImaginaryQuadraticOrder K

  vertexCM :
    ∀ j : k, j ∈ V → OrdinaryCMJData k q j K

  
  endomorphism_ring_on_level :
    ∀ i : ℕ, ∀ hi : i ≤ levels.depth,
      ∀ j : k, ∀ hj : j ∈ levels.level i,
        (vertexCM j (level_subset_component i hi hj)).endOrder.toSubring =
          (orderAtLevel i hi).toSubring

  
  surface_degree :
    ∀ j : k, j ∈ levels.level 0 →
      ((ellIsogenyGraph k ℓ).outDegreeIn (levels.level 0) j : ℤ) =
        1 + kroneckerPrime
          (ImaginaryQuadraticOrder.discr
            (orderAtLevel 0 (Nat.zero_le levels.depth))) ℓ

  
  surfaceIdeal_of_kronecker_nonneg :
    0 ≤ kroneckerPrime
          (ImaginaryQuadraticOrder.discr
            (orderAtLevel 0 (Nat.zero_le levels.depth))) ℓ →
      ProperIdealClassOfPrimeNorm
        (O := orderAtLevel 0 (Nat.zero_le levels.depth)) ℓ

  
  surface_card_of_kronecker_nonneg :
    ∀ hnonneg :
      0 ≤ kroneckerPrime
          (ImaginaryQuadraticOrder.discr
            (orderAtLevel 0 (Nat.zero_le levels.depth))) ℓ,
      (levels.level 0).card =
        ProperIdeal.classOrder
          (surfaceIdeal_of_kronecker_nonneg hnonneg).ideal

  
  surface_card_of_kronecker_neg :
    kroneckerPrime
        (ImaginaryQuadraticOrder.discr
          (orderAtLevel 0 (Nat.zero_le levels.depth))) ℓ < 0 →
      (levels.level 0).card = 1

  t : ℤ
  v : ℤ

  
  trace_sq_eq :
    ∀ j : k, ∀ hj : j ∈ V,
      t ^ (2 : ℕ) = (vertexCM j hj).frobeniusTrace ^ (2 : ℕ)

  
  depth_formula :
    (4 : ℤ) * (q : ℤ) =
      t ^ (2 : ℕ) -
        ((ℓ : ℤ) ^ (2 * levels.depth)) *
          v ^ (2 : ℕ) *
          ImaginaryQuadraticOrder.discr
            (orderAtLevel 0 (Nat.zero_le levels.depth))

  ell_not_dvd_v :
    ¬ ((ℓ : ℤ) ∣ v)

  
  ell_not_dvd_surface_conductor :
    ¬ ℓ ∣ (orderAtLevel 0 (Nat.zero_le levels.depth)).conductor

  
  successive_order_inclusion :
    ∀ i : ℕ, ∀ hi : i < levels.depth,
      (orderAtLevel (i + 1) (Nat.succ_le_of_lt hi)).toSubring ≤
        (orderAtLevel i (Nat.le_of_lt hi)).toSubring

  
  successive_conductor_eq :
    ∀ i : ℕ, ∀ hi : i < levels.depth,
      (orderAtLevel (i + 1) (Nat.succ_le_of_lt hi)).conductor =
        ℓ * (orderAtLevel i (Nat.le_of_lt hi)).conductor








theorem theorem_22_11_Kohel
    (k : Type u) [Field k] [Fintype k] [DecidableEq k]
    {q ℓ : ℕ}
    (hFieldCard : Fintype.card k = q)
    (hℓPrime : Nat.Prime ℓ)
    (hℓNotDvdq : ¬ ℓ ∣ q)
    (V : Finset k)
    (hV : IsOrdinaryComponent k q ℓ V)
    (hNoJ0 : (0 : k) ∉ V)
    (hNoJ1728 : (1728 : k) ∉ V) :
    Nonempty (KohelTheorem22_11Conclusion.{u} k q ℓ V) := by
  sorry

end SecKohel

end Autoform_Elliptic_Curves_elliptic_theorem_22_11_Kohel

end
