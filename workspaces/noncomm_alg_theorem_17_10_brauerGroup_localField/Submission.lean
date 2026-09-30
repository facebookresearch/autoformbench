/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.TensorProduct.Basic
import Submission.Helpers
import ChallengeDeps




















namespace Submission

open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField
open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField

noncomputable section







namespace BrauerClass



end BrauerClass








theorem brauerGroupAdditiveLaw_exists
    (F : Type u) [Field F] :
    Nonempty (BrauerGroupAdditiveLaw F) := by
  sorry





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
    Nonempty (BrauerGroup.{u, u} F ≃+ RatModInt) := by
  sorry

end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_17_10_brauerGroup_localField

end Submission
