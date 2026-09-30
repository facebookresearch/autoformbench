import ChallengeDeps




import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

open Autoform_Tensor_Categories_tensor_cat_proposition_1_45_5




















open scoped BigOperators
open Module

universe u v

namespace Autoform_Tensor_Categories_tensor_cat_proposition_1_45_5







section PerronRoot

variable {ι : Type u} [Fintype ι]















theorem perronRoot_exists (M : Matrix ι ι ℂ) [Nonempty ι] (hM : MatrixNonnegative M) :
    ∃ ρ : ℂ, IsPerronRoot M ρ := by
  sorry

end PerronRoot



namespace TransitiveZPlusRing

variable {ι : Type u} {A : Type v}
variable [Fintype ι] [DecidableEq ι] [Ring A]









noncomputable def leftMulMatrix (T : TransitiveZPlusRing ι A) (x : A) : Matrix ι ι ℂ :=
  fun row col => (T.basis.repr (x * T.basis col) row : ℂ)








theorem leftMulMatrix_nonnegative_of_basis
    (T : TransitiveZPlusRing ι A) (i : ι) :
    MatrixNonnegative (T.leftMulMatrix (T.basis i)) := by
  intro row col
  simpa [leftMulMatrix] using
    intCast_isNonnegativeReal (T.mul_nonneg i col row)









noncomputable def FPdimBasis (T : TransitiveZPlusRing ι A) (i : ι) : ℂ :=
  letI : Nonempty ι := ⟨T.oneIndex⟩
  Classical.choose
    (perronRoot_exists
      (T.leftMulMatrix (T.basis i))
      (T.leftMulMatrix_nonnegative_of_basis i))


















theorem FPdimBasis_isPerronRoot
    (T : TransitiveZPlusRing ι A) (i : ι) :
    IsPerronRoot (T.leftMulMatrix (T.basis i)) (T.FPdimBasis i) := by
  letI : Nonempty ι := ⟨T.oneIndex⟩
  exact Classical.choose_spec
    (perronRoot_exists
      (T.leftMulMatrix (T.basis i))
      (T.leftMulMatrix_nonnegative_of_basis i))








noncomputable def FPdimC (T : TransitiveZPlusRing ι A) (x : T.AC) : ℂ :=
  ∑ i : ι, x i * T.FPdimBasis i







noncomputable def FPdim (T : TransitiveZPlusRing ι A) (x : A) : ℂ :=
  T.FPdimC (T.toAC x)







def IsLeftRegularElement (T : TransitiveZPlusRing ι A) (R : T.AC) : Prop :=
  R ≠ 0 ∧
  ∀ x : A, T.mulC (T.toAC x) R = T.FPdim x • R







def IsRightRegularElement (T : TransitiveZPlusRing ι A) (R : T.AC) : Prop :=
  ∀ y : A, T.mulC R (T.toAC y) = T.FPdim y • R







def CharacterNonzero (χ : A →+* ℂ) : Prop :=
  ∃ x : A, χ x ≠ 0



































theorem proposition_1_45_5
    (T : TransitiveZPlusRing ι A) :
    ∃ φ : A →+* ℂ,
      (∀ x : A, φ x = T.FPdim x) ∧

      (∃ R : T.AC,
        T.IsLeftRegularElement R ∧
        T.PositiveCoefficients R ∧
        IsPositiveReal (T.FPdimC R) ∧
        T.IsRightRegularElement R ∧
        (∀ S : T.AC,
          T.IsLeftRegularElement S →
          ∃ c : ℂ, c ≠ 0 ∧ S = c • R)) ∧

      (∀ χ : A →+* ℂ,
        CharacterNonzero χ →
        T.CharacterNonnegativeOnBasis χ →
        χ = φ) ∧

      (∀ x : A,
        T.IsNonnegativeElement x →
        IsPerronRoot (T.leftMulMatrix x) (T.FPdim x)) := by
  sorry

end TransitiveZPlusRing

end Autoform_Tensor_Categories_tensor_cat_proposition_1_45_5
