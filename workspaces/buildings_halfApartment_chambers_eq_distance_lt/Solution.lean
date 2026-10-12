/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps
import Submission

open Autoform_Buildings_and_Classical_Groups_buildings_halfApartment_chambers_eq_distance_lt

universe u v

variable {V : Type u} (K : SimplicialComplex V)
variable {K : SimplicialComplex V} {C D : Set V}
variable {V : Type u} (X : ChamberComplex V)
variable {V : Type u} {W : Type v} {K : SimplicialComplex V} {L : SimplicialComplex W}
variable {V : Type u} {W : Type v} {X : ChamberComplex V} {Y : ChamberComplex W}
variable {V : Type u} {X : ThinChamberComplex V}
variable {V : Type u} {X : ThinChamberComplex V}

theorem halfApartment_chambers_eq_distance_lt (f : Folding X) (_hf : Reversible f) {C C₀ : Set V}
    (_hC_chamber : IsChamber X.toChamberComplex.K C)
    (_hC₀_chamber : IsChamber X.toChamberComplex.K C₀)
    (_h_adj : AdjacentChambers X.toChamberComplex.K C C₀)
    (_hC_mem : C ∈ halfApartment f)
    (_hC₀_not_mem : C₀ ∉ halfApartment f) :
    {D : Set V | IsChamber X.toChamberComplex.K D ∧ D ∈ halfApartment f} =
      {D : Set V | IsChamber X.toChamberComplex.K D ∧
        X.toChamberComplex.chamberDistance C D <
          X.toChamberComplex.chamberDistance C₀ D} := by
  exact Submission.halfApartment_chambers_eq_distance_lt f _hf _hC_chamber _hC₀_chamber _h_adj _hC_mem _hC₀_not_mem
