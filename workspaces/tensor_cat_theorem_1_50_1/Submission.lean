import ChallengeDeps
import Submission.Helpers





import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Noetherian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

open Autoform_Tensor_Categories_tensor_cat_theorem_1_50_1
noncomputable section

open scoped BigOperators
open CategoryTheory MonoidalCategory Module
open CategoryTheory.Limits

namespace Autoform_Tensor_Categories_tensor_cat_theorem_1_50_1

universe uₖ uC vC uD vD u v







def IsPositiveReal (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 < z.re

section PerronRoot

variable {ι : Type u} [Fintype ι] [Nonempty ι]







theorem perronRoot_exists (M : Matrix ι ι ℂ) (hM : MatrixNonnegative M) :
    ∃ ρ : ℂ, IsPerronRoot M ρ := by
  sorry

end PerronRoot

namespace TransitiveZPlusRing

variable {ι : Type u} {A : Type v}
variable [Fintype ι] [Nonempty ι] [DecidableEq ι] [Ring A]








noncomputable def mulC (T : TransitiveZPlusRing ι A) (x y : T.AC) : T.AC :=
  fun k =>
    ∑ i : ι, ∑ j : ι,
      x i * y j * (T.basis.repr (T.basis i * T.basis j) k : ℂ)









noncomputable def leftMulMatrix (T : TransitiveZPlusRing ι A) (x : A) : Matrix ι ι ℂ :=
  fun row col => (T.basis.repr (x * T.basis col) row : ℂ)








theorem leftMulMatrix_nonnegative_of_basis
    (T : TransitiveZPlusRing ι A) (i : ι) :
    MatrixNonnegative (T.leftMulMatrix (T.basis i)) := by
  intro row col
  simpa [leftMulMatrix] using
    intCast_isNonnegativeReal (T.mul_nonneg i col row)









noncomputable def FPdimBasis (T : TransitiveZPlusRing ι A) (i : ι) : ℂ :=
  Classical.choose
    (perronRoot_exists
      (T.leftMulMatrix (T.basis i))
      (T.leftMulMatrix_nonnegative_of_basis i))






theorem FPdimBasis_isPerronRoot
    (T : TransitiveZPlusRing ι A) (i : ι) :
    IsPerronRoot (T.leftMulMatrix (T.basis i)) (T.FPdimBasis i) := by
  exact Classical.choose_spec
    (perronRoot_exists
      (T.leftMulMatrix (T.basis i))
      (T.leftMulMatrix_nonnegative_of_basis i))








noncomputable def FPdimC (T : TransitiveZPlusRing ι A) (x : T.AC) : ℂ :=
  ∑ i : ι, x i * T.FPdimBasis i







noncomputable def FPdim (T : TransitiveZPlusRing ι A) (x : A) : ℂ :=
  T.FPdimC (T.toAC x)

theorem indexNonempty
    (T : TransitiveZPlusRing ι A) : Nonempty ι :=
  ⟨T.oneIndex⟩

end TransitiveZPlusRing



















structure FiniteTensorCategoryData
    (k : Type uₖ) [Field k] [IsAlgClosed k]
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
      [Preadditive C] [Abelian C] [Linear k C]
      [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C] where
  
  homFiniteDimensional : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)

  



  finiteLengthObject : ∀ X : C, IsArtinianObject X ∧ IsNoetherianObject X

  
  unitEndEquiv : (𝟙_ C ⟶ 𝟙_ C) ≃ₗ[k] k

  
  SimpleIndex : Type uC
  [nonempty : Nonempty SimpleIndex]
  
  [simpleIndexFintype : Fintype SimpleIndex]
  
  [simpleIndexDecidableEq : DecidableEq SimpleIndex]
  
  simpleObj : SimpleIndex → C

  
  simpleObj_simple : ∀ i : SimpleIndex, Simple (simpleObj i)

  
  simpleObj_complete : ∀ X : C, Simple X → ∃ i : SimpleIndex, Nonempty (X ≅ simpleObj i)

  
  simpleObj_skeletal :
    ∀ i j : SimpleIndex, Nonempty (simpleObj i ≅ simpleObj j) → i = j

  
  unitIndex : SimpleIndex

  
  unitIso : 𝟙_ C ≅ simpleObj unitIndex

  
  projectiveCover : SimpleIndex → ProjectiveObject C

  
  projectiveCoverMap :
    ∀ i : SimpleIndex, (projectiveCover i).obj ⟶ simpleObj i

  
  projectiveCover_isCover :
    ∀ i : SimpleIndex, IsProjectiveCover (projectiveCoverMap i)

  





  GrothendieckRing : Type uC

  


  [grothendieckRingInst : Ring GrothendieckRing]
  







  grothendieckZPlus :
    TransitiveZPlusRing SimpleIndex GrothendieckRing

  










  grothendieckBasis_tensor :
    ∀ i j : SimpleIndex,
      grothendieckZPlus.basis i * grothendieckZPlus.basis j =
        grothendieckZPlus.basis.equivFun.symm
          (fun l : SimpleIndex =>
            (Module.finrank k
              ((projectiveCover l).obj ⟶ (simpleObj i ⊗ simpleObj j)) : ℤ))

attribute [instance] FiniteTensorCategoryData.simpleIndexFintype
attribute [instance] FiniteTensorCategoryData.simpleIndexDecidableEq
attribute [instance] FiniteTensorCategoryData.grothendieckRingInst
attribute [instance] FiniteTensorCategoryData.nonempty
attribute [instance] FiniteTensorCategoryData.simpleIndexFintype
attribute [instance] FiniteTensorCategoryData.simpleIndexDecidableEq
attribute [instance] FiniteTensorCategoryData.grothendieckRingInst

namespace FiniteTensorCategoryData

variable
  {k : Type uₖ} [Field k] [IsAlgClosed k]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [Abelian C] [Linear k C]
    [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]












noncomputable def compositionMultiplicity
    (T : FiniteTensorCategoryData k C) (X : C) (i : T.SimpleIndex) : ℕ :=
  Module.finrank k ((T.projectiveCover i).obj ⟶ X)











noncomputable def grothendieckClass
    (T : FiniteTensorCategoryData k C) (X : C) : T.GrothendieckRing :=
  T.grothendieckZPlus.basis.equivFun.symm
    (fun i : T.SimpleIndex => (T.compositionMultiplicity X i : ℤ))








theorem grothendieckClass_simple
    (T : FiniteTensorCategoryData k C) (i : T.SimpleIndex) :
    T.grothendieckClass (T.simpleObj i) = T.grothendieckZPlus.basis i := by
  sorry








theorem grothendieckClass_tensor
    (T : FiniteTensorCategoryData k C) (X Y : C) :
    T.grothendieckClass (X ⊗ Y) =
      T.grothendieckClass X * T.grothendieckClass Y := by
  sorry













noncomputable def projectiveMultiplicity
    (T : FiniteTensorCategoryData k C)
    (P : ProjectiveObject C) (i : T.SimpleIndex) : ℕ :=
  Module.finrank k (P.obj ⟶ T.simpleObj i)


theorem projectiveMultiplicity_cover_self
    (T : FiniteTensorCategoryData k C) (i : T.SimpleIndex) :
    T.projectiveMultiplicity (T.projectiveCover i) i = 1 := by
  sorry


theorem projectiveMultiplicity_cover_ne
    (T : FiniteTensorCategoryData k C) (i j : T.SimpleIndex) (hij : i ≠ j) :
    T.projectiveMultiplicity (T.projectiveCover i) j = 0 := by
  sorry



theorem projectiveMultiplicity_isoInvariant
    (T : FiniteTensorCategoryData k C)
    {P Q : ProjectiveObject C} (hPQ : Nonempty (P.obj ≅ Q.obj))
    (i : T.SimpleIndex) :
    T.projectiveMultiplicity P i = T.projectiveMultiplicity Q i := by
  sorry








noncomputable def fpdimObject
    (T : FiniteTensorCategoryData k C) (X : C) : ℂ :=
    letI : Nonempty T.SimpleIndex := T.nonempty
  TransitiveZPlusRing.FPdim
    T.grothendieckZPlus
    (T.grothendieckClass X)







noncomputable def fpdimSimple
    (T : FiniteTensorCategoryData k C) (i : T.SimpleIndex) : ℂ :=
    letI : Nonempty T.SimpleIndex := T.nonempty
  TransitiveZPlusRing.FPdim
    T.grothendieckZPlus
    (T.grothendieckZPlus.basis i)







theorem fpdimObject_simple
    (T : FiniteTensorCategoryData k C) (i : T.SimpleIndex) :
    T.fpdimObject (T.simpleObj i) = T.fpdimSimple i := by
  unfold fpdimObject fpdimSimple
  rw [T.grothendieckClass_simple i]





noncomputable def fpdimProjectiveCover
    (T : FiniteTensorCategoryData k C) (i : T.SimpleIndex) : ℂ :=
  T.fpdimObject ((T.projectiveCover i).obj)








abbrev ProjectiveK0 (T : FiniteTensorCategoryData k C) : Type uC :=
  T.SimpleIndex → ℂ











noncomputable def regularObject
    (T : FiniteTensorCategoryData k C) : ProjectiveK0 T :=
  fun i => T.fpdimSimple i









noncomputable def categoryFPdim
    (T : FiniteTensorCategoryData k C) : ℂ :=
  ∑ i : T.SimpleIndex,
    T.fpdimSimple i * T.fpdimProjectiveCover i

variable
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    [Abelian D] [Linear k D]
    [MonoidalPreadditive D] [MonoidalLinear k D]
    [RigidCategory D]













noncomputable def pushForwardProjectiveK0
    (TC : FiniteTensorCategoryData k C)
    (TD : FiniteTensorCategoryData k D)
    (mapProj : ProjectiveObject C → ProjectiveObject D)
    (v : ProjectiveK0 TC) : ProjectiveK0 TD :=
  fun j =>
    ∑ i : TC.SimpleIndex,
      v i *
        ((TD.projectiveMultiplicity
          (mapProj (TC.projectiveCover i)) j : ℕ) : ℂ)

end FiniteTensorCategoryData

section Theorem1501

variable
  {k : Type uₖ} [Field k] [IsAlgClosed k]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [Abelian C] [Linear k C]
    [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    [Abelian D] [Linear k D]
    [MonoidalPreadditive D] [MonoidalLinear k D]
    [RigidCategory D]










theorem theorem_1_49_3_maps_projective
    (TC : FiniteTensorCategoryData k C)
    (TD : FiniteTensorCategoryData k D)
    (F : QuasiTensorFunctor k C D)
    (hF : F.Surjective)
    (P : ProjectiveObject C) :
    Projective (F.toFunctor.obj P.obj) := by
  sorry







def projectiveMapOfSurjectiveQuasiTensor
    (TC : FiniteTensorCategoryData k C)
    (TD : FiniteTensorCategoryData k D)
    (F : QuasiTensorFunctor k C D)
    (hF : F.Surjective) :
    ProjectiveObject C → ProjectiveObject D :=
  ProjectiveObject.map F.toFunctor
    (theorem_1_49_3_maps_projective TC TD F hF)








noncomputable def mapRegular
    (TC : FiniteTensorCategoryData k C)
    (TD : FiniteTensorCategoryData k D)
    (F : QuasiTensorFunctor k C D)
    (hF : F.Surjective) :
    FiniteTensorCategoryData.ProjectiveK0 TD :=
  FiniteTensorCategoryData.pushForwardProjectiveK0 TC TD
    (projectiveMapOfSurjectiveQuasiTensor TC TD F hF)
    (FiniteTensorCategoryData.regularObject TC)















theorem theorem_1_50_1
    (TC : FiniteTensorCategoryData k C)
    (TD : FiniteTensorCategoryData k D)
    (F : QuasiTensorFunctor k C D)
    (hF : F.Surjective) :
    mapRegular TC TD F hF =
      ((FiniteTensorCategoryData.categoryFPdim TC /
          FiniteTensorCategoryData.categoryFPdim TD : ℂ) •
        FiniteTensorCategoryData.regularObject TD) := by
  sorry

end Theorem1501


end Autoform_Tensor_Categories_tensor_cat_theorem_1_50_1

end
