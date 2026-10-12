/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Buildings_and_Classical_Groups_buildings_exists_nondegenerate_complement_and_hyperbolic_completion
open EpsilonHermitianForm

universe uK uZ uD uV uI

variable {k : Type uK} {Z : Type uZ} {D : Type uD}
variable [Field k] [Field Z] [DivisionRing D] [Algebra k D] [Algebra Z D]
variable {S : FormedScalarData k Z D}
variable {V : Type uV} [AddCommGroup V] [Module D V]

theorem exists_nondegenerate_complement_and_hyperbolic_completion [FiniteDimensional D V]
    (F : EpsilonHermitianForm S V)
    (h_char_ne_two : (2 : k) ≠ 0)
    (hV : F.IsNondegenerate)
    (W : Submodule D V) :
    (∃ W₁ : Submodule D V,
      W₁ ≤ W ∧
        F.IsNondegenerateOn W₁ ∧
        IsInternalDirectSum₂ (F.subspaceKernel W) W₁ W) ∧
      ∀ W₁ : Submodule D V,
        W₁ ≤ W →
          F.IsNondegenerateOn W₁ →
            IsInternalDirectSum₂ (F.subspaceKernel W) W₁ W →
              ∀ {κ : Type uI} [Fintype κ],
                (x : Module.Basis κ D (F.subspaceKernel W)) →
                  ∃ y : κ → V,
                    (∀ k : κ, y k ∈ F.orthogonal W₁) ∧
                      (∀ k : κ,
                        F.IsHyperbolicPair ((x k : F.subspaceKernel W) : V) (y k)) ∧
                      (∀ k l : κ, k ≠ l →
                        F.AreOrthogonal
                          (F.plane ((x k : F.subspaceKernel W) : V) (y k))
                          (F.plane ((x l : F.subspaceKernel W) : V) (y l))) ∧
                      F.IsNondegenerateOn (W ⊔ F.spanFamily y) ∧
                      F.IsDirectSumOfSubmoduleAndLines W y ∧
                      F.IsOrthogonalHyperbolicDecomposition
                        (F.subspaceKernel W ⊔ F.spanFamily y)
                        (fun k : κ => ((x k : F.subspaceKernel W) : V)) y := by
  sorry
