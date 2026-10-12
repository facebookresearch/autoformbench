/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps

open Autoform_Buildings_and_Classical_Groups_buildings_affineSlice_inter_titsCone_eq_univ

universe uι uW uV

variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]

theorem affineSlice_inter_titsCone_eq_univ (D : TitsConeData ι M W)
    (_h_affine : D.IsAffine)
    {v₀ : D.V} (_hv₀ : D.IsPositiveNullRoot v₀) :
    D.affineSlice v₀ ∩ D.titsCone = D.affineSliceFaceUnion v₀ ∧
      D.SliceTranslatedFacesDisjointOrEqual v₀ ∧
        D.affineSliceFaceUnion v₀ = D.affineSlice v₀ := by
  sorry
