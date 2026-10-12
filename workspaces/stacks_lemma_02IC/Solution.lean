/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Stacks_Project_stacks_lemma_02IC
open TopologicalSpace ENat

universe u

theorem lemma_02IC (X : Type u) [TopologicalSpace X]
    [QuasiSober X] [T0Space X]
    (h_noeth : IsLocallyNoetherianSpace X)
    (h_cat : IsCatenary X) :
    ∀ x : X, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ HasDimensionFunction {y : X // y ∈ U} := by
  exact Submission.lemma_02IC X h_noeth h_cat
