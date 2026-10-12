/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
























open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

universe u

namespace Autoform_Theory_of_Probability_probability_lecture31_strongMarkovProperty



abbrev Path (S : Type u) := ℕ → S




def pathShift {S : Type u} (n : ℕ) (ω : Path S) : Path S :=
  fun k => ω (n + k)







def transitionFromLast {S : Type u} [MeasurableSpace S]
    (p : Kernel S S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S) S where
  toFun := fun (hist : (i : Finset.Iic n) → S) =>
    p (hist (⟨n, by simp⟩ : Finset.Iic n))
  measurable' := by
    exact p.measurable.comp
      (measurable_pi_apply (⟨n, by simp⟩ : Finset.Iic n))

instance transitionFromLast_isMarkovKernel {S : Type u} [MeasurableSpace S]
    (p : Kernel S S) [IsMarkovKernel p] (n : ℕ) :
    IsMarkovKernel (transitionFromLast p n) where
  isProbabilityMeasure hist := by
    change IsProbabilityMeasure
      (p (hist (⟨n, by simp⟩ : Finset.Iic n)))
    infer_instance




def initialSegment0 {S : Type u} (x : S) : (i : Finset.Iic 0) → S :=
  fun _ => x






def lawFrom {S : Type u} [MeasurableSpace S]
    (p : Kernel S S) [IsMarkovKernel p] (x : S) : Measure (Path S) :=
  (Kernel.traj (X := fun _ : ℕ => S) (transitionFromLast p) 0)
    (initialSegment0 x)






def law {S : Type u} [MeasurableSpace S]
    (p : Kernel S S) [IsMarkovKernel p] (mu0 : Measure S) : Measure (Path S) :=
  Kernel.trajMeasure (X := fun _ : ℕ => S) mu0 (transitionFromLast p)




def expectedFrom {S : Type u} [MeasurableSpace S]
    (p : Kernel S S) [IsMarkovKernel p] (x : S) (Y : Path S → ℝ) : ℝ :=
  ∫ ω, Y ω ∂ lawFrom p x






def postStopValue {S : Type u}
    (tau : Path S → WithTop ℕ) (Y : ℕ → Path S → ℝ) : Path S → ℝ :=
  MeasureTheory.stoppedValue
    (fun n ω => Y n (pathShift n ω))
    tau



def rhsStrongMarkov {S : Type u} [MeasurableSpace S]
    (p : Kernel S S) [IsMarkovKernel p]
    (tau : Path S → WithTop ℕ) (Y : ℕ → Path S → ℝ) : Path S → ℝ :=
  MeasureTheory.stoppedValue
    (fun n ω => expectedFrom p (ω n) (Y n))
    tau



end Autoform_Theory_of_Probability_probability_lecture31_strongMarkovProperty
