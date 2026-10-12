/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.Basic























open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_18_15_universal_splitting

noncomputable section









attribute [instance] UniversalMatrixSplittingAlgebra.commRing
attribute [instance] UniversalMatrixSplittingAlgebra.algebra
attribute [instance] UniversalMatrixSplittingAlgebra.finiteType

variable {R : Type u} [CommRing R]
variable {A : Type u} [Ring A] [Algebra R A]
variable {d : ℕ}











theorem theorem_18_15a_universal_splitting_exists
    [IsAzumaya R A]
    (hd : 0 < d)
    (h_rank : HasConstantRankDegreeSquared R A d) :
    Nonempty (UniversalMatrixSplittingAlgebra R A d) := by
  sorry






theorem theorem_18_15b_universal_splitting_formallySmooth
    [IsAzumaya R A]
    (hd : 0 < d)
    (h_rank : HasConstantRankDegreeSquared R A d)
    (U : UniversalMatrixSplittingAlgebra R A d) :
    Algebra.FormallySmooth R U.S_univ := by
  sorry







theorem theorem_18_15b_universal_splitting_faithfullyFlat
    [IsAzumaya R A]
    [IsNoetherianRing R]
    (hd : 0 < d)
    (h_rank : HasConstantRankDegreeSquared R A d)
    (U : UniversalMatrixSplittingAlgebra R A d) :
    RingHom.FaithfullyFlat (algebraMap R U.S_univ) := by
  sorry




theorem theorem_18_15_universal_splitting
    [IsAzumaya R A]
    (hd : 0 < d)
    (h_rank : HasConstantRankDegreeSquared R A d) :
    ∃ U : UniversalMatrixSplittingAlgebra R A d,
      Algebra.FormallySmooth R U.S_univ ∧
        (IsNoetherianRing R →
          RingHom.FaithfullyFlat (algebraMap R U.S_univ)) := by
  sorry

end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_18_15_universal_splitting
