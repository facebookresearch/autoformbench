/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open MeasureTheory
open scoped BigOperators MeasureTheory

namespace Autoform_Learning_with_Submodular_Functions_submodular_prop_5_3_stable_sparsity_patterns









def SubmodularSetFunction {ι : Type*} (F : Set ι → ℝ) : Prop :=
  ∀ A B : Set ι, F (A ∪ B) + F (A ∩ B) ≤ F A + F B









def lovaszExtension {ι : Type*} [Fintype ι] (F : Set ι → ℝ) (w : ι → ℝ) : ℝ :=
  (∫ z in Set.Ioi (0 : ℝ), F {i : ι | z < w i} ∂(volume : Measure ℝ)) +
    (∫ z in Set.Iio (0 : ℝ),
        (F {i : ι | z < w i} - F Set.univ) ∂(volume : Measure ℝ))





def omegaInfinity {ι : Type*} [Fintype ι] (F : Set ι → ℝ) (w : ι → ℝ) : ℝ :=
  lovaszExtension F (fun i => |w i|)






def Stable {ι : Type*} (F : Set ι → ℝ) (A : Set ι) : Prop :=
  ∀ B : Set ι, A ⊂ B → F A < F B








def l2NormSq {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, (v i) ^ 2





def regularizedLeastSquaresObjective {n p : ℕ}
    (F : Set (Fin p) → ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ)
    (w : Fin p → ℝ) : ℝ :=
  ((2 : ℝ) * (n : ℝ))⁻¹ *
      l2NormSq (fun i : Fin n => y i - (X.mulVec w) i) +
    omegaInfinity F w



end Autoform_Learning_with_Submodular_Functions_submodular_prop_5_3_stable_sparsity_patterns
