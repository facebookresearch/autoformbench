


import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.TensorProduct.Basic
import Submission
import ChallengeDeps

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField



















open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField

noncomputable section







namespace BrauerClass



end BrauerClass








theorem brauerGroupAdditiveLaw_exists
    (F : Type u) [Field F] :
    Nonempty (BrauerGroupAdditiveLaw F) := by apply Submission.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField.brauerGroupAdditiveLaw_exists <;> assumption





noncomputable def brauerGroupAdditiveLaw
    (F : Type u) [Field F] :
    BrauerGroupAdditiveLaw F :=
  Classical.choice (brauerGroupAdditiveLaw_exists F)




noncomputable instance brauerGroupAddCommGroup
    (F : Type u) [Field F] :
    AddCommGroup (BrauerGroup.{u, u} F) :=
  (brauerGroupAdditiveLaw F).addCommGroup















theorem theorem_17_10_brauerGroup_localField
    (F : Type u) [Field F]
    (hF : IsBookNonarchimedeanLocalField F) :
    Nonempty (BrauerGroup.{u, u} F ≃+ RatModInt) := by apply Submission.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField.theorem_17_10_brauerGroup_localField <;> assumption

end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField
