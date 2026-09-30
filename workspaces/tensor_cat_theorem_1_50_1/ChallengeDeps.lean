import Mathlib

noncomputable section

open scoped BigOperators
open CategoryTheory MonoidalCategory Module
open CategoryTheory.Limits

namespace Autoform_Tensor_Categories_tensor_cat_theorem_1_50_1

universe uₖ uC vC uD vD u v







def IsNonnegativeReal (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re

lemma intCast_isNonnegativeReal {n : ℤ} (hn : 0 ≤ n) :
    IsNonnegativeReal ((n : ℂ)) := by
  constructor
  · simp
  · simpa using (Int.cast_nonneg hn : (0 : ℝ) ≤ (n : ℝ))

section PerronRoot

variable {ι : Type u} [Fintype ι] [Nonempty ι]








abbrev matrixEnd (M : Matrix ι ι ℂ) : Module.End ℂ (ι → ℂ) :=
  M.mulVecLin








def IsEigenvalue (M : Matrix ι ι ℂ) (μ : ℂ) : Prop :=
  Module.End.HasEigenvalue (matrixEnd M) μ







def MatrixNonnegative (M : Matrix ι ι ℂ) : Prop :=
  ∀ i j : ι, IsNonnegativeReal (M i j)









def IsPerronRoot (M : Matrix ι ι ℂ) (ρ : ℂ) : Prop :=
  IsNonnegativeReal ρ ∧
  IsEigenvalue M ρ ∧
  ∀ μ : ℂ, IsEigenvalue M μ → ‖μ‖ ≤ ρ.re



end PerronRoot















structure TransitiveZPlusRing (ι : Type u) (A : Type v)
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [Ring A] where
  basis : Basis ι ℤ A
  oneIndex : ι
  basis_one : basis oneIndex = (1 : A)

  



  mul_nonneg :
    ∀ i j k : ι, 0 ≤ basis.repr (basis i * basis j) k

  




  transitive :
    ∀ i k : ι,
      (∃ j : ι, 0 < basis.repr (basis i * basis j) k) ∧
      (∃ j : ι, 0 < basis.repr (basis j * basis i) k)

namespace TransitiveZPlusRing

variable {ι : Type u} {A : Type v}
variable [Fintype ι] [Nonempty ι] [DecidableEq ι] [Ring A]








abbrev AC (_ : TransitiveZPlusRing ι A) : Type _ :=
  ι → ℂ








noncomputable def toAC (T : TransitiveZPlusRing ι A) (x : A) : T.AC :=
  fun i => (T.basis.repr x i : ℂ)






end TransitiveZPlusRing









structure ExactFunctor
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) : Prop where
  preservesFiniteLimits : PreservesFiniteLimits F
  preservesFiniteColimits : PreservesFiniteColimits F







def IsSubquotient
    {C : Type uC} [Category.{vC} C]
    (Y X : C) : Prop :=
  ∃ (S : C) (i : S ⟶ X) (p : S ⟶ Y), Mono i ∧ Epi p







def IsProjectiveCover
    {C : Type uC} [Category.{vC} C]
    {P X : C} (p : P ⟶ X) : Prop :=
  Projective P ∧ Epi p ∧ ∀ e : P ⟶ P, e ≫ p = p → IsIso e











structure QuasiTensorFunctor
    (k : Type uₖ) [Field k]
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
      [Preadditive C] [Abelian C] [Linear k C]
      [MonoidalPreadditive C] [MonoidalLinear k C]
    (D : Type uD) [Category.{vD} D] [MonoidalCategory D]
      [Preadditive D] [Abelian D] [Linear k D]
      [MonoidalPreadditive D] [MonoidalLinear k D] where
  toFunctor : C ⥤ D
  additive : Functor.Additive toFunctor
  faithful : Functor.Faithful toFunctor
  exact : ExactFunctor toFunctor
  tensorIso :
    (toFunctor.prod toFunctor ⋙ MonoidalCategory.tensor D) ≅
      (MonoidalCategory.tensor C ⋙ toFunctor)
  unitIso : toFunctor.obj (𝟙_ C) ≅ 𝟙_ D

namespace QuasiTensorFunctor

variable
  {k : Type uₖ} [Field k]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [Abelian C] [Linear k C]
    [MonoidalPreadditive C] [MonoidalLinear k C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    [Abelian D] [Linear k D]
    [MonoidalPreadditive D] [MonoidalLinear k D]







def Surjective (F : QuasiTensorFunctor k C D) : Prop :=
  ∀ Y : D, ∃ X : C, IsSubquotient Y (F.toFunctor.obj X)

end QuasiTensorFunctor







structure ProjectiveObject
    (C : Type uC) [Category.{vC} C] where
  obj : C
  isProjective : Projective obj

namespace ProjectiveObject







def map
    {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D)
    (hF : ∀ P : ProjectiveObject C, Projective (F.obj P.obj))
    (P : ProjectiveObject C) : ProjectiveObject D where
  obj := F.obj P.obj
  isProjective := hF P

end ProjectiveObject






























end Autoform_Tensor_Categories_tensor_cat_theorem_1_50_1

end