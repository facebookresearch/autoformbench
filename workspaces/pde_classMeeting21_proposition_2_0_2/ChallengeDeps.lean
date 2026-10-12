/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_PDEs_pde_classMeeting21_proposition_2_0_2



abbrev Idx (n : ℕ) := Fin (n + 1)


abbrev Spacetime (n : ℕ) := Idx n → ℝ



def coordPartial {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Spacetime n → V) (μ : Idx n) (x : Spacetime n) : V :=
  (fderiv ℝ f x) (Pi.single μ (1 : ℝ))


def coordGradient {n : ℕ} (φ : Spacetime n → ℝ) (x : Spacetime n) :
    Spacetime n :=
  fun μ => coordPartial φ μ x







structure LocalAutonomousFlow (n : ℕ) where
  ε₀ : ℝ
  ε₀_pos : 0 < ε₀
  F : ℝ → (Spacetime n ≃ Spacetime n)
  Y : Spacetime n → Spacetime n
  smooth_F : ContDiff ℝ ⊤ (fun p : ℝ × Spacetime n => F p.1 p.2)
  smooth_Y : ContDiff ℝ ⊤ Y
  F_zero : ∀ x, F 0 x = x
  F_neg : ∀ {ε : ℝ}, |ε| ≤ ε₀ → F (-ε) = (F ε).symm
  F_add : ∀ {ε₁ ε₂ : ℝ}, |ε₁| + |ε₂| ≤ ε₀ →
    ∀ x, F ε₁ (F ε₂ x) = F (ε₁ + ε₂) x
  F_ode : ∀ {ε : ℝ}, |ε| ≤ ε₀ →
    ∀ x, HasDerivAt (fun s => F s x) (Y (F ε x)) ε






def jacobian {n : ℕ}
    (f : Spacetime n → Spacetime n) (x : Spacetime n) :
    Matrix (Idx n) (Idx n) ℝ :=
  LinearMap.toMatrix' ((fderiv ℝ f x).toLinearMap)



def oldCoordinate {n : ℕ} (flow : LocalAutonomousFlow n)
    (ε : ℝ) (xNew : Spacetime n) : Spacetime n :=
  flow.F (-ε) xNew



def forwardJacobianAtOld {n : ℕ} (flow : LocalAutonomousFlow n)
    (ε : ℝ) (xNew : Spacetime n) : Matrix (Idx n) (Idx n) ℝ :=
  jacobian (flow.F ε) (oldCoordinate flow ε xNew)




def inverseJacobianAtNew {n : ℕ} (flow : LocalAutonomousFlow n)
    (ε : ℝ) (xNew : Spacetime n) : Matrix (Idx n) (Idx n) ℝ :=
  jacobian (flow.F (-ε)) xNew


def transformedScalar {n : ℕ} (flow : LocalAutonomousFlow n)
    (φ : Spacetime n → ℝ) (ε : ℝ) (xNew : Spacetime n) : ℝ :=
  φ (oldCoordinate flow ε xNew)


def transformedGradient {n : ℕ} (flow : LocalAutonomousFlow n)
    (φ : Spacetime n → ℝ) (ε : ℝ) (xNew : Spacetime n) :
    Spacetime n :=
  (inverseJacobianAtNew flow ε xNew).transpose.mulVec
    (coordGradient φ (oldCoordinate flow ε xNew))


def transformedMetric {n : ℕ} (flow : LocalAutonomousFlow n)
    (m : Spacetime n → Matrix (Idx n) (Idx n) ℝ)
    (ε : ℝ) (xNew : Spacetime n) : Matrix (Idx n) (Idx n) ℝ :=
  let K := inverseJacobianAtNew flow ε xNew
  K.transpose * m (oldCoordinate flow ε xNew) * K


def transformedInverseMetric {n : ℕ} (flow : LocalAutonomousFlow n)
    (m : Spacetime n → Matrix (Idx n) (Idx n) ℝ)
    (ε : ℝ) (xNew : Spacetime n) : Matrix (Idx n) (Idx n) ℝ :=
  let J := forwardJacobianAtOld flow ε xNew
  J * (m (oldCoordinate flow ε xNew))⁻¹ * J.transpose



end Autoform_Introduction_to_PDEs_pde_classMeeting21_proposition_2_0_2
