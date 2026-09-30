/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib




















noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_weak_approximation_11_7


abbrev FinitePrime : Type :=
  { p : ℕ // Nat.Prime p }


instance finitePrimeFact (p : FinitePrime) : Fact (Nat.Prime p.1) :=
  ⟨p.2⟩






abbrev PadicCompletionOfFinitePrime (p : FinitePrime) : Type :=
  Padic p.1







def WeakApproximationFinitePrimeCondition
    (Sfin : Finset FinitePrime)
    (xp : ∀ p : FinitePrime, p ∈ Sfin → PadicCompletionOfFinitePrime p)
    (ε : ℝ) (x : ℚ) : Prop :=
  ∀ p : FinitePrime, ∀ hpS : p ∈ Sfin,
    ‖(x : PadicCompletionOfFinitePrime p) - xp p hpS‖ < ε





def WeakApproximationInfinityCondition
    (includeInfinity : Bool) (xInf : ℝ) (ε : ℝ) (x : ℚ) : Prop :=
  includeInfinity = true → |(x : ℝ) - xInf| < ε





def WeakApproximationConclusion
    (Sfin : Finset FinitePrime)
    (includeInfinity : Bool)
    (xInf : ℝ)
    (xp : ∀ p : FinitePrime, p ∈ Sfin → PadicCompletionOfFinitePrime p)
    (ε : ℝ) : Prop :=
  ∃ x : ℚ,
    WeakApproximationInfinityCondition includeInfinity xInf ε x ∧
      WeakApproximationFinitePrimeCondition Sfin xp ε x



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_weak_approximation_11_7
