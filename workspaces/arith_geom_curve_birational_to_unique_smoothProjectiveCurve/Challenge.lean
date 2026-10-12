/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_curve_birational_to_unique_smoothProjectiveCurve
open CategoryTheory
open AlgebraicGeometry

universe u

theorem curve_birational_to_unique_smoothProjectiveCurve (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (π : C ⟶ SpecOf k)
    (hC : IsCurveOver k C π) :
    ∃ (Csp : Scheme.{u}) (πsp : Csp ⟶ SpecOf k),
      IsSmoothProjectiveCurveOver k Csp πsp ∧
        BirationalEquivalentOver k C π Csp πsp ∧
          ∀ (D : Scheme.{u}) (πD : D ⟶ SpecOf k),
            IsSmoothProjectiveCurveOver k D πD →
              BirationalEquivalentOver k C π D πD →
                IsomorphicOver k Csp πsp D πD := by
  sorry
