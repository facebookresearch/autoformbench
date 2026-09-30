import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules

















abbrev Vec (n : ℕ) : Type :=
  Fin n → ℂ


abbrev SymH (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ


def stdBasisVec (n : ℕ) (i : Fin n) : Vec n :=
  fun j => if j = i then 1 else 0





noncomputable def vecAsYPolynomial {n : ℕ} (y : Vec n) : SymH n :=
  ∑ i : Fin n, MvPolynomial.C (y i) * MvPolynomial.X i





noncomputable def directionalPDeriv {n : ℕ}
    (x : Vec n →ₗ[ℂ] ℂ) (Q : SymH n) : SymH n :=
  ∑ i : Fin n,
    MvPolynomial.C (x (stdBasisVec n i)) * (MvPolynomial.pderiv i Q)


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





noncomputable def yPolynomialAction {n : ℕ}
    (Γ : FiniteLinearGroup n) (g : Γ.G) : SymH n →ₐ[ℂ] SymH n :=
  MvPolynomial.aeval
    (fun i : Fin n => vecAsYPolynomial (actVec Γ g (stdBasisVec n i)))







def IsComplexReflectionElement {n : ℕ}
    (Γ : FiniteLinearGroup n) (g : Γ.G) : Prop :=
  ∃ (lambda : ℂ) (alpha : Vec n →ₗ[ℂ] ℂ) (coroot : Vec n),
    lambda ≠ 1 ∧ alpha coroot = 2 ∧
      ∀ v : Vec n,
        actVec Γ g v =
          v + ((((lambda⁻¹ - 1) / 2) * alpha v) • coroot)


structure ReflectionData {n : ℕ}
    (Γ : FiniteLinearGroup n) where
  elt : Γ.G
  eigenvalue : ℂ
  alpha : Vec n →ₗ[ℂ] ℂ
  coroot : Vec n
  eigenvalue_ne_one : eigenvalue ≠ 1
  alpha_coroot : alpha coroot = 2
  reflection_formula :
    ∀ v : Vec n,
      actVec Γ elt v =
        v + ((((eigenvalue⁻¹ - 1) / 2) * alpha v) • coroot)









structure ComplexReflectionSystem {n : ℕ}
    (Γ : FiniteLinearGroup n) where
  S : Type
  [instFintype : Fintype S]
  refl : S → ReflectionData Γ
  refl_elt_injective : Function.Injective (fun s : S => (refl s).elt)
  refl_complete :
    ∀ g : Γ.G, IsComplexReflectionElement Γ g →
      ∃ s : S, (refl s).elt = g
  conj : Γ.G → S → S
  conj_id : ∀ s : S, conj 1 s = s
  conj_mul : ∀ (g h : Γ.G) (s : S), conj (g * h) s = conj g (conj h s)
  conj_elt :
    ∀ (g : Γ.G) (s : S),
      (refl (conj g s)).elt = g * (refl s).elt * g⁻¹
  conj_eigenvalue :
    ∀ (g : Γ.G) (s : S),
      (refl (conj g s)).eigenvalue = (refl s).eigenvalue
  conj_alpha :
    ∀ (g : Γ.G) (s : S),
      (refl (conj g s)).alpha = actCovec Γ g (refl s).alpha
  conj_coroot :
    ∀ (g : Γ.G) (s : S),
      (refl (conj g s)).coroot = actVec Γ g (refl s).coroot
  param : S → ℂ
  param_conj_invariant :
    ∀ (g : Γ.G) (s : S),
      param (conj g s) = param s

attribute [instance] ComplexReflectionSystem.instFintype


noncomputable def invariantYSubalgebra {n : ℕ}
    (Γ : FiniteLinearGroup n) : Subalgebra ℂ (SymH n) where
  carrier := {Q : SymH n | ∀ g : Γ.G, yPolynomialAction Γ g Q = Q}
  zero_mem' := by
    intro g
    simp
  one_mem' := by
    intro g
    simp
  add_mem' := by
    intro Q R hQ hR g
    simp [map_add, hQ g, hR g]
  mul_mem' := by
    intro Q R hQ hR g
    simp [map_mul, hQ g, hR g]
  algebraMap_mem' := by
    intro z g
    simp


abbrev InvariantYPolynomial {n : ℕ}
    (Γ : FiniteLinearGroup n) : Type :=
  invariantYSubalgebra Γ





abbrev InvariantCharacter {n : ℕ}
    (Γ : FiniteLinearGroup n) : Type :=
  invariantYSubalgebra Γ →ₐ[ℂ] ℂ















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
    (RS : ComplexReflectionSystem Γ)
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
    (RS : ComplexReflectionSystem Γ) :
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
    (RS : ComplexReflectionSystem Γ) : Type :=
  RingQuot (h1cRel Γ RS)


noncomputable def h1cQuotientMap {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ComplexReflectionSystem Γ) :
    H1cFreeAlgebra Γ →ₐ[ℂ] H1cCherednikAlgebra Γ RS :=
  RingQuot.mkAlgHom ℂ (h1cRel Γ RS)


noncomputable def h1cX {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    (x : Vec n →ₗ[ℂ] ℂ) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genX x)


noncomputable def h1cY {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    (y : Vec n) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genY y)


noncomputable def h1cG {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    (g : Γ.G) : H1cCherednikAlgebra Γ RS :=
  h1cQuotientMap Γ RS (genG g)














structure H1cModuleAction {n : ℕ}
    (Γ : FiniteLinearGroup n)
    (RS : ComplexReflectionSystem Γ)
    (M : Type)
    [AddCommGroup M] [Module ℂ M] where
  rep : H1cCherednikAlgebra Γ RS →ₐ[ℂ] Module.End ℂ M
  yPolyOp : SymH n →ₐ[ℂ] Module.End ℂ M
  yPolyOp_linear :
    ∀ y : Vec n, yPolyOp (vecAsYPolynomial y) = rep (h1cY (RS := RS) y)


noncomputable def H1cModuleAction.xOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (x : Vec n →ₗ[ℂ] ℂ) : Module.End ℂ M :=
  A.rep (h1cX (RS := RS) x)


noncomputable def H1cModuleAction.gOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (g : Γ.G) : Module.End ℂ M :=
  A.rep (h1cG (RS := RS) g)


noncomputable def H1cModuleAction.invariantYOp {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (Q : InvariantYPolynomial Γ) : Module.End ℂ M :=
  A.yPolyOp (Q : SymH n)





def LocallyFiniteInvariantYModule {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M) : Prop :=
  ∀ m : M,
    ∃ (ι : Type) (_ : Fintype ι) (u : ι → M),
      let V : Submodule ℂ M := Submodule.span ℂ (Set.range u)
      m ∈ V ∧
        ∀ Q : InvariantYPolynomial Γ,
          ∀ v : M, v ∈ V → A.invariantYOp Q v ∈ V






noncomputable def eigenOperator {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (χ : InvariantCharacter Γ)
    (Q : InvariantYPolynomial Γ) : Module.End ℂ M :=
  A.invariantYOp Q - (χ Q) • (1 : Module.End ℂ M)









def generalizedWeightSpace {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (χ : InvariantCharacter Γ) : Submodule ℂ M where
  carrier :=
    {m : M | ∀ Q : InvariantYPolynomial Γ,
      ∃ N : ℕ, ((eigenOperator A χ Q) ^ N) m = 0}
  zero_mem' := by
    intro Q
    exact ⟨0, by simp [eigenOperator]⟩
  add_mem' := by
    intro u v hu hv Q
    let T : Module.End ℂ M := eigenOperator A χ Q
    obtain ⟨N, hNu⟩ := hu Q
    obtain ⟨K, hKv⟩ := hv Q
    refine ⟨N + K, ?_⟩
    have hNu' : (T ^ (N + K)) u = 0 := by
      rw [Nat.add_comm N K, pow_add]
      change (T ^ K) ((T ^ N) u) = 0
      rw [hNu]
      simp
    have hKv' : (T ^ (N + K)) v = 0 := by
      rw [pow_add]
      change (T ^ N) ((T ^ K) v) = 0
      rw [hKv]
      simp
    change (T ^ (N + K)) (u + v) = 0
    rw [map_add, hNu', hKv', zero_add]
  smul_mem' := by
    intro a u hu Q
    let T : Module.End ℂ M := eigenOperator A χ Q
    obtain ⟨N, hNu⟩ := hu Q
    refine ⟨N, ?_⟩
    change (T ^ N) (a • u) = 0
    rw [map_smul, hNu, smul_zero]


def StableUnderH1c {n : ℕ}
    {Γ : FiniteLinearGroup n}
    {RS : ComplexReflectionSystem Γ}
    {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : H1cModuleAction Γ RS M)
    (N : Submodule ℂ M) : Prop :=
  ∀ a : H1cCherednikAlgebra Γ RS,
    ∀ m : M, m ∈ N → A.rep a m ∈ N



end Autoform_Double_Hecke_Algebras_double_hecke_proposition_3_16_generalized_weight_spaces_are_submodules

end
