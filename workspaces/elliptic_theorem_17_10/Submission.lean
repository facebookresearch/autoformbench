import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Algebra.Algebra.Rat
import Submission.Helpers
import ChallengeDeps








































open _root_.Autoform_Elliptic_Curves_elliptic_theorem_17_10
noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_theorem_17_10





variable {K : IntermediateField ℚ ℂ}





instance instModuleFreeOrderIn (𝓞 : OrderIn K) : Module.Free ℤ 𝓞 :=
  𝓞.free_z









instance instIsFractionRingOrderIn (𝓞 : OrderIn K) : IsFractionRing 𝓞 K := by
  
  
  
  sorry













theorem quadraticConj_mem
    (K : IntermediateField ℚ ℂ) (hK : IsImaginaryQuadraticField K)
    (z : K) :
    star (z : ℂ) ∈ K := by
  
  
  sorry





theorem quadraticConj_left_inv
    (K : IntermediateField ℚ ℂ) (hK : IsImaginaryQuadraticField K)
    (z : K) :
    star (star (z : ℂ)) = (z : ℂ) := by
  
  sorry





theorem quadraticConj_right_inv
    (K : IntermediateField ℚ ℂ) (hK : IsImaginaryQuadraticField K)
    (z : K) :
    star (star (z : ℂ)) = (z : ℂ) := by
  
  sorry





theorem quadraticConj_map_mul
    (K : IntermediateField ℚ ℂ) (hK : IsImaginaryQuadraticField K)
    (x y : K) :
    star ((x * y : K) : ℂ) = star (x : ℂ) * star (y : ℂ) := by
  
  sorry





theorem quadraticConj_map_add
    (K : IntermediateField ℚ ℂ) (hK : IsImaginaryQuadraticField K)
    (x y : K) :
    star ((x + y : K) : ℂ) = star (x : ℂ) + star (y : ℂ) := by
  
  sorry









noncomputable def quadraticConj
    (K : IntermediateField ℚ ℂ) (hK : IsImaginaryQuadraticField K) :
    K ≃+* K where
  toFun z := ⟨star (z : ℂ), quadraticConj_mem K hK z⟩
  invFun z := ⟨star (z : ℂ), quadraticConj_mem K hK z⟩
  left_inv := fun z => Subtype.ext (quadraticConj_left_inv K hK z)
  right_inv := fun z => Subtype.ext (quadraticConj_right_inv K hK z)
  map_mul' := fun x y => Subtype.ext (quadraticConj_map_mul K hK x y)
  map_add' := fun x y => Subtype.ext (quadraticConj_map_add K hK x y)






theorem orderConj_mem
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (x : 𝓞) :
    quadraticConj K hK (x : K) ∈ (𝓞 : Subalgebra ℤ K) := by
  
  
  
  sorry





theorem orderConj_left_inv
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (x : 𝓞) :
    quadraticConj K hK (quadraticConj K hK (x : K)) = (x : K) := by
  sorry





theorem orderConj_right_inv
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (x : 𝓞) :
    quadraticConj K hK (quadraticConj K hK (x : K)) = (x : K) := by
  sorry





theorem orderConj_map_mul
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (x y : 𝓞) :
    quadraticConj K hK ((x * y : 𝓞) : K)
      = quadraticConj K hK (x : K) * quadraticConj K hK (y : K) := by
  sorry





theorem orderConj_map_add
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (x y : 𝓞) :
    quadraticConj K hK ((x + y : 𝓞) : K)
      = quadraticConj K hK (x : K) + quadraticConj K hK (y : K) := by
  sorry









noncomputable def orderConj
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) :
    𝓞 ≃+* 𝓞 where
  toFun x := ⟨quadraticConj K hK (x : K), orderConj_mem hK 𝓞 x⟩
  invFun x := ⟨quadraticConj K hK (x : K), orderConj_mem hK 𝓞 x⟩
  left_inv := fun x => Subtype.ext (orderConj_left_inv hK 𝓞 x)
  right_inv := fun x => Subtype.ext (orderConj_right_inv hK 𝓞 x)
  map_mul' := fun x y => Subtype.ext (orderConj_map_mul hK 𝓞 x y)
  map_add' := fun x y => Subtype.ext (orderConj_map_add hK 𝓞 x y)





theorem conjugateSubmodule_smul
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (I : FracIdeal 𝓞) (r : 𝓞) (y : K) (hy : y ∈ I) :
    quadraticConj K hK (algebraMap 𝓞 K ((orderConj hK 𝓞).symm r) * y)
      = r • quadraticConj K hK y := by
  sorry









noncomputable def conjugateSubmodule
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (I : FracIdeal 𝓞) :
    Submodule 𝓞 K where
  carrier := { z : K | ∃ y : K, y ∈ I ∧ quadraticConj K hK y = z }
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩
    · exact I.1.zero_mem
    · simp
  add_mem' := by
    intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨y₁, hy₁, rfl⟩
    rcases hz₂ with ⟨y₂, hy₂, rfl⟩
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · exact I.1.add_mem hy₁ hy₂
    · simp
  smul_mem' := by
    intro r z hz
    rcases hz with ⟨y, hy, rfl⟩
    let r' : 𝓞 := (orderConj hK 𝓞).symm r
    refine ⟨algebraMap 𝓞 K r' * y, ?_, ?_⟩
    · simpa [Algebra.smul_def] using
        I.1.smul_mem r' hy
    · 
      exact conjugateSubmodule_smul hK 𝓞 I r y hy






theorem conjugateFractionalIdeal_isFractional
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (I : FracIdeal 𝓞) :
    IsFractional (nonZeroDivisors (𝓞 : Type _)) (conjugateSubmodule hK 𝓞 I) := by
  sorry









noncomputable def conjugateFractionalIdeal
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (I : FracIdeal 𝓞) :
    FracIdeal 𝓞 where
  val := conjugateSubmodule hK 𝓞 I
  property := conjugateFractionalIdeal_isFractional hK 𝓞 I








noncomputable def theorem17_10_explicitInverse
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K) (𝔞 : Ideal 𝓞) :
    FracIdeal 𝓞 :=
  FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 : Type _))
      ((algebraMap 𝓞 K ((idealAbsNorm 𝓞 𝔞 : ℕ) : 𝓞))⁻¹)
    * conjugateFractionalIdeal hK 𝓞 (𝔞 : FracIdeal 𝓞)














theorem theorem_17_10
    (hK : IsImaginaryQuadraticField K)
    (𝓞 : OrderIn K)
    (𝔞 : Ideal 𝓞) (h𝔞 : 𝔞 ≠ ⊥) :
    (IsProperFractionalIdeal 𝓞 (𝔞 : FracIdeal 𝓞) ↔
      IsUnit (𝔞 : FracIdeal 𝓞)) ∧
    (IsUnit (𝔞 : FracIdeal 𝓞) →
      (𝔞 : FracIdeal 𝓞) *
          conjugateFractionalIdeal hK 𝓞 (𝔞 : FracIdeal 𝓞)
        =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 : Type _))
            (algebraMap 𝓞 K ((idealAbsNorm 𝓞 𝔞 : ℕ) : 𝓞)) ∧
      (𝔞 : FracIdeal 𝓞)⁻¹ =
          theorem17_10_explicitInverse hK 𝓞 𝔞 ∧
      (𝔞 : FracIdeal 𝓞) *
          theorem17_10_explicitInverse hK 𝓞 𝔞 = 1 ∧
      theorem17_10_explicitInverse hK 𝓞 𝔞 *
          (𝔞 : FracIdeal 𝓞) = 1) := by
  sorry

end Autoform_Elliptic_Curves_elliptic_theorem_17_10


end