import Mathlib

set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_43_irreducible_iff_frobenius

universe u v



























abbrev Vec (n : ℕ) : Type :=
  Fin n → ℂ






abbrev PolyH (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ






noncomputable def dot {n : ℕ} (v w : Vec n) : ℂ :=
  ∑ i : Fin n, v i * w i






structure FiniteOrthogonalLinearGroup (n : ℕ) where
  G : Type u
  [instGroup : Group G]
  [instFintype : Fintype G]
  rho : G →* (Vec n ≃ₗ[ℂ] Vec n)
  rho_injective : Function.Injective rho
  rho_orthogonal :
    ∀ (g : G) (v w : Vec n),
      dot (rho g v) (rho g w) = dot v w

attribute [instance] FiniteOrthogonalLinearGroup.instGroup
attribute [instance] FiniteOrthogonalLinearGroup.instFintype


def stdBasisVec (n : ℕ) (i : Fin n) : Vec n :=
  fun j => if j = i then 1 else 0


def coordLinear (n : ℕ) (i : Fin n) : Vec n →ₗ[ℂ] ℂ where
  toFun := fun v => v i
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl






noncomputable def linearFormPolynomial {n : ℕ}
    (x : Vec n →ₗ[ℂ] ℂ) : PolyH n :=
  ∑ i : Fin n,
    MvPolynomial.C (x (stdBasisVec n i)) * MvPolynomial.X i









def actVec {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (g : Γ.G) (v : Vec n) : Vec n :=
  Γ.rho g v







noncomputable def actCovec {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (g : Γ.G)
    (x : Vec n →ₗ[ℂ] ℂ) : Vec n →ₗ[ℂ] ℂ :=
  x.comp (Γ.rho (g⁻¹)).toLinearMap







noncomputable def polynomialGActionAlgHom {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (g : Γ.G) : PolyH n →ₐ[ℂ] PolyH n :=
  MvPolynomial.aeval
    (fun i : Fin n =>
      linearFormPolynomial
        ((coordLinear n i).comp (Γ.rho (g⁻¹)).toLinearMap))


noncomputable def polynomialGAction {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (g : Γ.G) : Module.End ℂ (PolyH n) :=
  (polynomialGActionAlgHom Γ g).toLinearMap













structure ReflectionData {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n) where
  elt : Γ.G
  eig : ℂ
  eig_ne_one : eig ≠ 1
  alpha : Vec n →ₗ[ℂ] ℂ
  coroot : Vec n
  alpha_coroot : alpha coroot = 2
  reflection_formula :
    ∀ v : Vec n,
      Γ.rho elt v =
        v - ((((1 : ℂ) - eig⁻¹) / 2) • ((alpha v) • coroot))





def IsReflectionElement {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (g : Γ.G) : Prop :=
  ∃ r : ReflectionData Γ, r.elt = g








structure ReflectionSystem {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n) where
  S : Type v
  [instFintype : Fintype S]
  refl : S → ReflectionData Γ
  refl_elt_injective :
    Function.Injective (fun s : S => (refl s).elt)
  refl_exact :
    ∀ g : Γ.G,
      IsReflectionElement Γ g ↔ ∃ s : S, (refl s).elt = g
  conj : Γ.G → S → S
  conj_elt :
    ∀ (g : Γ.G) (s : S),
      (refl (conj g s)).elt = g * (refl s).elt * g⁻¹
  param : S → ℂ
  param_conj_invariant :
    ∀ (g : Γ.G) (s : S),
      param (conj g s) = param s

attribute [instance] ReflectionSystem.instFintype





noncomputable def alphaPolynomial {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    (RS : ReflectionSystem Γ)
    (s : RS.S) : PolyH n :=
  linearFormPolynomial ((RS.refl s).alpha)













inductive H1cGen {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n) where
  | X : (Vec n →ₗ[ℂ] ℂ) → H1cGen Γ
  | Y : Vec n → H1cGen Γ
  | G : Γ.G → H1cGen Γ





abbrev H1cFreeAlgebra {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n) : Type _ :=
  FreeAlgebra ℂ (H1cGen Γ)





noncomputable def gen {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    (a : H1cGen Γ) : H1cFreeAlgebra Γ :=
  FreeAlgebra.ι ℂ a





noncomputable def genX {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    (x : Vec n →ₗ[ℂ] ℂ) : H1cFreeAlgebra Γ :=
  gen (H1cGen.X x)





noncomputable def genY {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    (y : Vec n) : H1cFreeAlgebra Γ :=
  gen (H1cGen.Y y)





noncomputable def genG {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    (g : Γ.G) : H1cFreeAlgebra Γ :=
  gen (H1cGen.G g)





noncomputable def scalarC {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    (z : ℂ) : H1cFreeAlgebra Γ :=
  algebraMap ℂ (H1cFreeAlgebra Γ) z





def commutator {A : Type _} [Ring A] (a b : A) : A :=
  a * b - b * a







noncomputable def yxCherednikRHSAtOne {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    (RS : ReflectionSystem Γ)
    (y : Vec n) (x : Vec n →ₗ[ℂ] ℂ) : H1cFreeAlgebra Γ :=
  scalarC (x y) -
    ∑ s : RS.S,
      scalarC
          (RS.param s *
            ((RS.refl s).alpha y) *
            (x ((RS.refl s).coroot))) *
        genG (RS.refl s).elt






inductive h1cRel {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ) :
    H1cFreeAlgebra Γ → H1cFreeAlgebra Γ → Prop
  | x_add (x x' : Vec n →ₗ[ℂ] ℂ) :
      h1cRel Γ RS
        (genX (x + x'))
        (genX x + genX x')
  | x_smul (a : ℂ) (x : Vec n →ₗ[ℂ] ℂ) :
      h1cRel Γ RS
        (genX (a • x))
        (scalarC a * genX x)
  | y_add (y y' : Vec n) :
      h1cRel Γ RS
        (genY (y + y'))
        (genY y + genY y')
  | y_smul (a : ℂ) (y : Vec n) :
      h1cRel Γ RS
        (genY (a • y))
        (scalarC a * genY y)
  | group_unit :
      h1cRel Γ RS
        (genG (Γ := Γ) 1)
        1
  | group_mul (g h : Γ.G) :
      h1cRel Γ RS
        (genG (Γ := Γ) g * genG h)
        (genG (g * h))
  | group_act_x (g : Γ.G) (x : Vec n →ₗ[ℂ] ℂ) :
      h1cRel Γ RS
        (genG (Γ := Γ) g * genX x * genG g⁻¹)
        (genX (actCovec Γ g x))
  | group_act_y (g : Γ.G) (y : Vec n) :
      h1cRel Γ RS
        (genG (Γ := Γ) g * genY y * genG g⁻¹)
        (genY (actVec Γ g y))
  | xx (x x' : Vec n →ₗ[ℂ] ℂ) :
      h1cRel Γ RS
        (commutator (genX x) (genX x'))
        0
  | yy (y y' : Vec n) :
      h1cRel Γ RS
        (commutator (genY y) (genY y'))
        0
  | yx (y : Vec n) (x : Vec n →ₗ[ℂ] ℂ) :
      h1cRel Γ RS
        (commutator (genY y) (genX x))
        (yxCherednikRHSAtOne RS y x)





abbrev H1cCherednikAlgebra {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ) : Type _ :=
  RingQuot (h1cRel Γ RS)





noncomputable def h1cQuotientMap {n : ℕ}
    (Γ : FiniteOrthogonalLinearGroup.{u} n)
    (RS : ReflectionSystem Γ) :
    H1cFreeAlgebra Γ →ₐ[ℂ] H1cCherednikAlgebra Γ RS :=
  RingQuot.mkAlgHom ℂ (h1cRel Γ RS)


noncomputable def h1cX {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (x : Vec n →ₗ[ℂ] ℂ) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genX x)


noncomputable def h1cY {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (y : Vec n) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genY y)


noncomputable def h1cG {n : ℕ}
    {Γ : FiniteOrthogonalLinearGroup.{u} n}
    {RS : ReflectionSystem Γ}
    (g : Γ.G) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genG g)













def monomialTotalDegree {n : ℕ} (α : Fin n →₀ ℕ) : ℕ :=
  α.sum fun _ k => k






def IsHomogeneousPolynomial {n : ℕ} (d : ℕ) (p : PolyH n) : Prop :=
  ∀ α ∈ p.support, monomialTotalDegree α = d















def FiniteDimensionalOverC
    (A : Type _) [AddCommGroup A] [Module ℂ A] : Prop :=
  ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → A,
    letI := hι
    ∀ a : A, ∃ coeff : ι → ℂ,
      a = ∑ i : ι, coeff i • b i


























end Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_43_irreducible_iff_frobenius

end