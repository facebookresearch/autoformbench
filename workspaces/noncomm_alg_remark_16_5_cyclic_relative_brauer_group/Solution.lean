/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Data.Matrix.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Submission
import ChallengeDeps

open Autoform_Noncommutative_Algebra_noncomm_alg_remark_16_5_cyclic_relative_brauer_group




























open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_remark_16_5_cyclic_relative_brauer_group

noncomputable section





namespace BrauerClass





end BrauerClass











theorem relativeBrauerGroupLaw_exists
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Nonempty (RelativeBrauerGroupLaw F E) := by apply Submission.Autoform_Noncommutative_Algebra_noncomm_alg_remark_16_5_cyclic_relative_brauer_group.relativeBrauerGroupLaw_exists <;> assumption




noncomputable def relativeBrauerGroupLaw
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    RelativeBrauerGroupLaw F E :=
  Classical.choice (relativeBrauerGroupLaw_exists F E)





noncomputable instance relativeBrauerGroupCommGroup
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    CommGroup (RelativeBrauerGroup F E) :=
  (relativeBrauerGroupLaw F E).group



















theorem remark_16_5_cyclic_relative_brauer_group
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    [IsGalois F E]
    [IsCyclic Gal(E/F)] :
    Nonempty
      (RelativeBrauerGroup F E ≃*
        NormUnitsQuotient F E) := by apply Submission.Autoform_Noncommutative_Algebra_noncomm_alg_remark_16_5_cyclic_relative_brauer_group.remark_16_5_cyclic_relative_brauer_group <;> assumption

end

end Autoform_Noncommutative_Algebra_noncomm_alg_remark_16_5_cyclic_relative_brauer_group
