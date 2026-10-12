/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Algebraic_Geometry_I_alg_geom_projective_intersection_dimension_theorem
open Set
open MvPolynomial

universe u

theorem projective_intersection_dimension_theorem {k : Type u} [Field k] [IsAlgClosed k]
    {n : ℕ}
    (X Y : ProjectiveSubvariety k n) :
    (∀ Z : Set (ProjectiveSpace k n),
      IsIrreducibleComponentOf k n
        (ProjectiveSubvariety.intersection X Y) Z →
        ProjectiveSubvariety.dim X + ProjectiveSubvariety.dim Y
          ≤ ((n : ℕ∞) : WithBot ℕ∞) + projectiveSetDim k n Z)
    ∧
    (((n : ℕ∞) : WithBot ℕ∞)
        < ProjectiveSubvariety.dim X + ProjectiveSubvariety.dim Y →
      (ProjectiveSubvariety.intersection X Y).Nonempty) := by
  sorry
