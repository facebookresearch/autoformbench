/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Lie_groups_lie_algebras_lie_proposition_17_2
open scoped TensorProduct

universe u v

namespace Submission

theorem proposition_17_2 (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]
    (𝔤 : Type v) [LieRing 𝔤] [LieAlgebra 𝕜 𝔤]
    [FiniteDimensional 𝕜 𝔤] :
    TextSemisimple 𝕜 𝔤 ↔
      TextSemisimple (AlgebraicClosure 𝕜) ((AlgebraicClosure 𝕜) ⊗[𝕜] 𝔤) := by
  sorry

end Submission
