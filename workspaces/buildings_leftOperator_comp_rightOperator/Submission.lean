/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Buildings_and_Classical_Groups_buildings_leftOperator_comp_rightOperator

universe u v w a

variable {R : Type u} [CommRing R]
variable {ι : Type v} {M : CoxeterMatrix ι}
variable {W : Type w} [Group W]

namespace Submission

theorem leftOperator_comp_rightOperator (D : GenericData R ι M W)
    {A : Type a} [AddCommGroup A] [Module R A]
    (T : Module.Basis W R A) (s t : ι) :
    (leftOperator D T s).comp (rightOperator D T t) =
      (rightOperator D T t).comp (leftOperator D T s) := by
  sorry

end Submission
