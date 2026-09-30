/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness



















abbrev Vec (n : ℕ) : Type :=
  Fin n → ℂ






abbrev SymH (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ






abbrev SymHStar (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ






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






noncomputable def vecAsYPolynomial {n : ℕ} (y : Vec n) : SymH n :=
  ∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.X i






noncomputable def covecAsXPolynomial {n : ℕ}
    (x : Vec n →ₗ[ℂ] ℂ) : SymHStar n :=
  ∑ i : Fin n, MvPolynomial.C (x (stdBasisVec n i)) * MvPolynomial.X i





structure FiniteLinearGroup (n : ℕ) where
  G : Type
  [instGroup : Group G]
  [instFintype : Fintype G]
  rho : G →* (Vec n ≃ₗ[ℂ] Vec n)
  rho_injective : Function.Injective rho

attribute [instance] FiniteLinearGroup.instGroup
attribute [instance] FiniteLinearGroup.instFintype





def actVec {n : ℕ}
    (Γ : FiniteLinearGroup n) (g : Γ.G) (v : Vec n) : Vec n :=
  Γ.rho g v








noncomputable def actCovec {n : ℕ}
    (Γ : FiniteLinearGroup n) (g : Γ.G)
    (x : Vec n →ₗ[ℂ] ℂ) : Vec n →ₗ[ℂ] ℂ :=
  x.comp (Γ.rho (g⁻¹)).toLinearMap



def diagonalLinearMap {n : ℕ} (μ : Fin n → ℂ) : Vec n →ₗ[ℂ] Vec n where
  toFun := fun v i => μ i * v i
  map_add' := by
    intro v w
    funext i
    simp [mul_add]
  map_smul' := by
    intro a v
    funext i
    simp [mul_assoc, mul_comm, mul_left_comm]







def HasComplexEigenbasis {n : ℕ} (T : Vec n →ₗ[ℂ] Vec n) : Prop :=
  ∃ e : Vec n ≃ₗ[ℂ] Vec n,
    ∃ μ : Fin n → ℂ,
      ∀ v : Vec n, T (e v) = e (diagonalLinearMap μ v)






def OneDimensionalRange {n : ℕ} (T : Vec n →ₗ[ℂ] Vec n) : Prop :=
  ∃ v : Vec n,
    v ≠ 0 ∧ LinearMap.range T = Submodule.span ℂ ({v} : Set (Vec n))






def IsComplexReflection {n : ℕ}
    (Γ : FiniteLinearGroup n) (g : Γ.G) : Prop :=
  HasComplexEigenbasis (Γ.rho g).toLinearMap ∧
    OneDimensionalRange
      ((LinearMap.id : Vec n →ₗ[ℂ] Vec n) - (Γ.rho g).toLinearMap)








structure ReflectionData {n : ℕ}
    (Γ : FiniteLinearGroup n) where
  elt : Γ.G
  is_complex_reflection : IsComplexReflection Γ elt
  eig : ℂ
  eig_ne_zero : eig ≠ 0
  eig_ne_one : eig ≠ 1
  alpha : Vec n →ₗ[ℂ] ℂ
  coroot : Vec n
  alpha_eigen : actCovec Γ elt alpha = eig • alpha
  coroot_eigen : actVec Γ elt coroot = eig⁻¹ • coroot
  alpha_coroot : alpha coroot = 2


def ReflectionData.asReflection {n : ℕ}
    {Γ : FiniteLinearGroup n}
    (r : ReflectionData Γ) : {g : Γ.G // IsComplexReflection Γ g} :=
  ⟨r.elt, r.is_complex_reflection⟩







structure ReflectionSystem {n : ℕ}
    (Γ : FiniteLinearGroup n) where
  S : Type
  [instFintype : Fintype S]
  refl : S → ReflectionData Γ
  reflections_complete :
    Function.Bijective
      (fun s : S => ReflectionData.asReflection (refl s))
  conj : Γ.G → S → S
  conj_one : ∀ s : S, conj 1 s = s
  conj_mul : ∀ (g h : Γ.G) (s : S),
    conj (g * h) s = conj g (conj h s)
  conj_elt :
    ∀ (g : Γ.G) (s : S),
      (refl (conj g s)).elt = g * (refl s).elt * g⁻¹
  conj_eig :
    ∀ (g : Γ.G) (s : S),
      (refl (conj g s)).eig = (refl s).eig
  conj_root_coroot :
    ∀ (g : Γ.G) (s : S),
      ∃ a : ℂ,
        a ≠ 0 ∧
          (refl (conj g s)).alpha = a • actCovec Γ g (refl s).alpha ∧
          (refl (conj g s)).coroot = a⁻¹ • actVec Γ g (refl s).coroot
  param : S → ℂ
  param_conj_invariant :
    ∀ (g : Γ.G) (s : S),
      param (conj g s) = param s

attribute [instance] ReflectionSystem.instFintype







inductive H1cGen {n : ℕ}
    (Γ : FiniteLinearGroup n) where
  | X : (Vec n →ₗ[ℂ] ℂ) → H1cGen Γ
  | Y : Vec n → H1cGen Γ
  | G : Γ.G → H1cGen Γ






abbrev H1cFreeAlgebra {n : ℕ}
    (Γ : FiniteLinearGroup n) : Type :=
  FreeAlgebra ℂ (H1cGen Γ)





noncomputable def gen {n : ℕ}
    {Γ : FiniteLinearGroup n}
    (a : H1cGen Γ) : H1cFreeAlgebra Γ :=
  FreeAlgebra.ι ℂ a





noncomputable def genX {n : ℕ}
    {Γ : FiniteLinearGroup n}
    (x : Vec n →ₗ[ℂ] ℂ) : H1cFreeAlgebra Γ :=
  gen (H1cGen.X x)





noncomputable def genY {n : ℕ}
    {Γ : FiniteLinearGroup n}
    (y : Vec n) : H1cFreeAlgebra Γ :=
  gen (H1cGen.Y y)





noncomputable def genG {n : ℕ}
    {Γ : FiniteLinearGroup n}
    (g : Γ.G) : H1cFreeAlgebra Γ :=
  gen (H1cGen.G g)





noncomputable def scalarC {n : ℕ}
    {Γ : FiniteLinearGroup n}
    (z : ℂ) : H1cFreeAlgebra Γ :=
  algebraMap ℂ (H1cFreeAlgebra Γ) z





def commutator {A : Type} [Ring A] (a b : A) : A :=
  a * b - b * a








noncomputable def yxCherednikRHSAtOne {n : ℕ}
    {Γ : FiniteLinearGroup n}
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
    (Γ : FiniteLinearGroup n)
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
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ) : Type :=
  RingQuot (h1cRel Γ RS)





noncomputable def h1cQuotientMap {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ) :
    H1cFreeAlgebra Γ →ₐ[ℂ] H1cCherednikAlgebra Γ RS :=
  RingQuot.mkAlgHom ℂ (h1cRel Γ RS)





noncomputable def h1cX {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    (x : Vec n →ₗ[ℂ] ℂ) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genX x)





noncomputable def h1cY {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    (y : Vec n) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genY y)





noncomputable def h1cG {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    (g : Γ.G) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genG g)







noncomputable def gradingElement {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ) : H1cCherednikAlgebra Γ RS :=
  (∑ i : Fin n,
      h1cX (RS := RS) (coordLinear n i) *
        h1cY (RS := RS) (stdBasisVec n i)) +
    algebraMap ℂ (H1cCherednikAlgebra Γ RS) ((n : ℂ) / 2) -
    ∑ s : RS.S,
      algebraMap ℂ (H1cCherednikAlgebra Γ RS)
          ((2 * RS.param s) / ((1 : ℂ) - (RS.refl s).eig)) *
        h1cG (RS := RS) (RS.refl s).elt





noncomputable def yPolynomialAction {n : ℕ}
    (Γ : FiniteLinearGroup n) (g : Γ.G) : SymH n →ₐ[ℂ] SymH n :=
  MvPolynomial.aeval
    (fun i : Fin n => vecAsYPolynomial (actVec Γ g (stdBasisVec n i)))





structure InvariantYPolynomial {n : ℕ}
    (Γ : FiniteLinearGroup n) where
  poly : SymH n
  invariant : ∀ g : Γ.G, yPolynomialAction Γ g poly = poly






noncomputable def invariantZeroEval {n : ℕ}
    {Γ : FiniteLinearGroup n}
    (Q : InvariantYPolynomial Γ) : ℂ :=
  MvPolynomial.eval (fun _ : Fin n => (0 : ℂ)) Q.poly











structure H1cModuleAction {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ReflectionSystem Γ)
    (M : Type)
    [AddCommGroup M] [Module ℂ M] where
  rep : H1cCherednikAlgebra Γ RS →ₐ[ℂ] Module.End ℂ M
  yPolyOp : SymH n →ₐ[ℂ] Module.End ℂ M
  xPolyOp : SymHStar n →ₐ[ℂ] Module.End ℂ M
  yPolyOp_linear :
    ∀ y : Vec n, yPolyOp (vecAsYPolynomial y) = rep (h1cY (RS := RS) y)
  xPolyOp_linear :
    ∀ x : Vec n →ₗ[ℂ] ℂ,
      xPolyOp (covecAsXPolynomial x) = rep (h1cX (RS := RS) x)





noncomputable def H1cModuleAction.yOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (y : Vec n) : Module.End ℂ M :=
  A.rep (h1cY (RS := RS) y)





noncomputable def H1cModuleAction.gradingOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Module.End ℂ M :=
  A.rep (gradingElement Γ RS)







noncomputable def H1cModuleAction.yListOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) :
    List (Vec n) → Module.End ℂ M
  | [] => 1
  | y :: ys => A.yOp y * A.yListOp ys







def LinearOperatorLocallyFinite
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) : Prop :=
  ∀ m : M,
    ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → M,
      letI := hι
      ∀ k : ℕ,
        ∃ coeff : ι → ℂ,
          (T ^ k) m = ∑ i : ι, coeff i • b i






def LieHActsLocallyNilpotently {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Prop :=
  ∀ m : M,
    ∃ N : ℕ,
      ∀ ys : List (Vec n),
        ys.length = N → A.yListOp ys m = 0






def SymHActsLocallyFinitely {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Prop :=
  ∀ m : M,
    ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → M,
      letI := hι
      ∀ p : SymH n,
        ∃ coeff : ι → ℂ,
          A.yPolyOp p m = ∑ i : ι, coeff i • b i





def FinitelyGeneratedOverSymHStar {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Prop :=
  ∃ ι : Type, ∃ hι : Fintype ι, ∃ b : ι → M,
    letI := hι
    ∀ m : M,
      ∃ coeff : ι → SymHStar n,
        m = ∑ i : ι, A.xPolyOp (coeff i) (b i)






noncomputable def zeroBlockOperator {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (Q : InvariantYPolynomial Γ) : Module.End ℂ M :=
  A.yPolyOp Q.poly - (invariantZeroEval Q) • (1 : Module.End ℂ M)





def InZeroGeneralizedBlock {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Prop :=
  ∀ m : M,
    ∀ Q : InvariantYPolynomial Γ,
      ∃ N : ℕ, ((zeroBlockOperator A Q) ^ N) m = 0





def InCategoryO {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Prop :=
  FinitelyGeneratedOverSymHStar A ∧ SymHActsLocallyFinitely A






def InCategoryOZero {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Prop :=
  InCategoryO A ∧ InZeroGeneralizedBlock A







end Autoform_Double_Hecke_Algebras_double_hecke_theorem_3_20_grading_element_local_finiteness

end
