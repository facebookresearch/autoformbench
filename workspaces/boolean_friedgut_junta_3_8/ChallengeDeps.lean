/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace Autoform_Analysis_of_Boolean_Functions_boolean_friedgut_junta_3_8








abbrev Cube (n : ℕ) := Fin n → Bool






abbrev BooleanFunction (n : ℕ) := Cube n → Bool






def signValue : Bool → ℝ
  | false => 1
  | true => -1






def flipCoordinate {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (Bool.not (x i))







def uniformExpectation {n : ℕ} (u : Cube n → ℝ) : ℝ :=
  ((Finset.univ : Finset (Cube n)).sum u) /
    (Fintype.card (Cube n) : ℝ)






def mean {n : ℕ} (f : BooleanFunction n) : ℝ :=
  uniformExpectation (fun x => signValue (f x))






def variance {n : ℕ} (f : BooleanFunction n) : ℝ :=
  uniformExpectation (fun x => (signValue (f x) - mean f) ^ 2)










def coordinateInfluence {n : ℕ} (f : BooleanFunction n) (i : Fin n) : ℝ :=
  uniformExpectation (fun x =>
    if f x ≠ f (flipCoordinate i x) then (1 : ℝ) else 0)






def totalInfluence {n : ℕ} (f : BooleanFunction n) : ℝ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => coordinateInfluence f i)








def restrictTo {n : ℕ} (J : Finset (Fin n)) (x : Cube n) :
    ({i : Fin n // i ∈ J} → Bool) :=
  fun i => x i.1







def IsJuntaOn {n : ℕ} (J : Finset (Fin n)) (g : BooleanFunction n) : Prop :=
  ∃ h : ({i : Fin n // i ∈ J} → Bool) → Bool,
    ∀ x : Cube n, g x = h (restrictTo J x)








def l2DistanceSq {n : ℕ} (f g : BooleanFunction n) : ℝ :=
  uniformExpectation (fun x =>
    (signValue (f x) - signValue (g x)) ^ 2)



end Autoform_Analysis_of_Boolean_Functions_boolean_friedgut_junta_3_8
