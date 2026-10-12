/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
















noncomputable section

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_strong_approximation_11_8


abbrev FinitePrime : Type :=
  { p : ℕ // Nat.Prime p }


instance finitePrimeFact (p : FinitePrime) : Fact (Nat.Prime p.1) :=
  ⟨p.2⟩


abbrev PadicCompletionOfFinitePrime (p : FinitePrime) : Type :=
  Padic p.1





abbrev PadicIntegersOfFinitePrime (p : FinitePrime) : Type :=
  { x : PadicCompletionOfFinitePrime p // ‖x‖ ≤ 1 }


abbrev toPadic {p : FinitePrime}
    (x : PadicIntegersOfFinitePrime p) : PadicCompletionOfFinitePrime p :=
  x.1







def StrongApproximationFinitePrimeCondition
    (Sfin : Finset FinitePrime)
    (xp : ∀ p : FinitePrime, p ∈ Sfin → PadicIntegersOfFinitePrime p)
    (ε : ℝ) (x : ℤ) : Prop :=
  ∀ p : FinitePrime, ∀ hpS : p ∈ Sfin,
    ‖(x : PadicCompletionOfFinitePrime p) - toPadic (xp p hpS)‖ < ε




def StrongApproximationConclusion
    (Sfin : Finset FinitePrime)
    (xp : ∀ p : FinitePrime, p ∈ Sfin → PadicIntegersOfFinitePrime p)
    (ε : ℝ) : Prop :=
  ∃ x : ℤ, StrongApproximationFinitePrimeCondition Sfin xp ε x



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_strong_approximation_11_8
