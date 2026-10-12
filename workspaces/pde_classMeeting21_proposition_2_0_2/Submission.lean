/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission.Helpers

open Autoform_Introduction_to_PDEs_pde_classMeeting21_proposition_2_0_2
open scoped BigOperators

namespace Submission

theorem classMeeting21_proposition_2_0_2 {n : ℕ}
    (flow : LocalAutonomousFlow n)
    (φ : Spacetime n → ℝ)
    (m : Spacetime n → Matrix (Idx n) (Idx n) ℝ)
    (hφ : ContDiff ℝ 2 φ)
    (hm : ∀ μ ν : Idx n, ContDiff ℝ 1 (fun x => m x μ ν))
    (hm_symm : ∀ x, (m x).IsSymm)
    (hm_invertible : ∀ x, IsUnit (m x)) :

    
    (∀ x : Spacetime n,
      HasDerivAt
        (fun ε : ℝ => transformedScalar flow φ ε x)
        (-(∑ α : Idx n, flow.Y x α * coordPartial φ α x))
        0) ∧

    
    (∀ (x : Spacetime n) (μ : Idx n),
      let rhs : ℝ :=
        -(∑ α : Idx n,
            coordPartial (fun z => flow.Y z α) μ x *
              coordPartial φ α x)
        - (∑ α : Idx n,
            flow.Y x α *
              coordPartial (fun z => coordPartial φ μ z) α x)
      HasDerivAt
          (fun ε : ℝ => transformedGradient flow φ ε x μ)
          rhs
          0 ∧
        rhs =
          -coordPartial
            (fun z =>
              ∑ α : Idx n, flow.Y z α * coordPartial φ α z)
            μ x) ∧

    
    (∀ (x : Spacetime n) (μ ν : Idx n),
      HasDerivAt
        (fun ε : ℝ => transformedMetric flow m ε x μ ν)
        (-(∑ α : Idx n,
              m x ν α *
                coordPartial (fun z => flow.Y z α) μ x)
         - (∑ α : Idx n,
              m x μ α *
                coordPartial (fun z => flow.Y z α) ν x)
         - (∑ α : Idx n,
              flow.Y x α *
                coordPartial (fun z => m z μ ν) α x))
        0) ∧

    
    (∀ (x : Spacetime n) (μ ν : Idx n),
      HasDerivAt
        (fun ε : ℝ => transformedInverseMetric flow m ε x μ ν)
        ((∑ α : Idx n,
              ((m x)⁻¹) α ν *
                coordPartial (fun z => flow.Y z μ) α x)
         + (∑ α : Idx n,
              ((m x)⁻¹) μ α *
                coordPartial (fun z => flow.Y z ν) α x)
         - (∑ α : Idx n,
              flow.Y x α *
                coordPartial (fun z => ((m z)⁻¹) μ ν) α x))
        0) ∧

    
    (∀ x : Spacetime n,
      HasDerivAt
        (fun ε : ℝ => (inverseJacobianAtNew flow ε x).det)
        (-(∑ α : Idx n,
            coordPartial (fun z => flow.Y z α) α x))
        0) := by
  sorry

end Submission
