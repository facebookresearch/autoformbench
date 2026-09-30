/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import ChallengeDeps

open Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_1_convex_relaxation_of_supports
open scoped BigOperators

noncomputable section

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_1_convex_relaxation_of_supports

variable {ι : Type*} [Fintype ι] [DecidableEq ι]












theorem exists_decreasingEnumeration (w : ι → ℝ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι,
      ∀ a b : Fin (Fintype.card ι), a ≤ b → w (e a) ≥ w (e b) := by
  classical
  sorry







noncomputable def decreasingEnumeration (w : ι → ℝ) :
    Fin (Fintype.card ι) ≃ ι :=
  Classical.choose (exists_decreasingEnumeration (ι := ι) w)




theorem decreasingEnumeration_spec (w : ι → ℝ) :
    ∀ a b : Fin (Fintype.card ι), a ≤ b →
      w ((decreasingEnumeration (ι := ι) w) a) ≥
        w ((decreasingEnumeration (ι := ι) w) b) :=
  Classical.choose_spec (exists_decreasingEnumeration (ι := ι) w)












noncomputable def lovaszExtension (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ := by
  classical
  let e := decreasingEnumeration (ι := ι) w
  exact
    ∑ k : Fin (Fintype.card ι),
      w (e k) *
        (F ((Finset.univ : Finset ι).filter
              (fun i : ι => e.symm i ≤ k)) -
         F ((Finset.univ : Finset ι).filter
              (fun i : ι => e.symm i < k)))





noncomputable def omegaInfinity (F : Finset ι → ℝ) (w : ι → ℝ) : ℝ :=
  lovaszExtension (ι := ι) F (fun i : ι => |w i|)























theorem proposition_5_1_convex_relaxation_of_supports
    (F : Finset ι → ℝ)
    (h_empty : F ∅ = 0)
    (h_submodular : Submodular F)
    (h_mono : Monotone F) :
    IsConvexEnvelopeOn (ι := ι)
      (unitLinftyBall (ι := ι))
      (omegaInfinity (ι := ι) F)
      (supportPenalty (ι := ι) F) := by
  sorry

end Autoform_Learning_with_Submodular_Functions_submodular_proposition_5_1_convex_relaxation_of_supports
