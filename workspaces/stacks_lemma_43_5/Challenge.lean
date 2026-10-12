/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Stacks_Project_stacks_lemma_43_5
open CategoryTheory
open CategoryTheory.Limits

universe v u w

theorem lemma_43_5 {C : Cat.{v, u}}
    (J : GrothendieckTopology C)
    (F : Sheaf J (Type (max u v w)))
    (hF : IsSubterminal F) :
    IsSubtopos J
      (fun G : Sheaf J (Type (max u v w)) =>
        IsIso (Limits.prod.fst : F ⨯ G ⟶ F)) := by
  sorry
