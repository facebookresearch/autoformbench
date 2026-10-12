/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option warningAsError false























universe uι uW uV

namespace Autoform_Buildings_and_Classical_Groups_buildings_affineSlice_inter_titsCone_eq_univ





noncomputable def coxeterFormCoefficient (m : ℕ) : ℝ :=
  if m = 0 then -1 else -Real.cos (Real.pi / (m : ℝ))



def CoxeterDiagramAdjacent {ι : Type uι} (M : CoxeterMatrix ι) (s t : ι) : Prop :=
  s ≠ t ∧ M.M s t ≠ 2


inductive CoxeterDiagramWalk {ι : Type uι} (M : CoxeterMatrix ι) : ι → ι → Prop
  | refl (s : ι) : CoxeterDiagramWalk M s s
  | step {s t r : ι} :
      CoxeterDiagramAdjacent M s t → CoxeterDiagramWalk M t r →
        CoxeterDiagramWalk M s r


def CoxeterDiagramConnected {ι : Type uι} (M : CoxeterMatrix ι) : Prop :=
  ∀ s t : ι, CoxeterDiagramWalk M s t








structure TitsConeData (ι : Type uι) [Fintype ι]
    (M : CoxeterMatrix ι) (W : Type uW) [Group W] where
  coxeter : CoxeterSystem M W
  V : Type uV
  [addCommGroup : AddCommGroup V]
  [module : Module ℝ V]
  simpleRootBasis : Module.Basis ι ℝ V
  coxeterForm : V → V → ℝ
  coxeterForm_zero_left : ∀ y : V, coxeterForm 0 y = 0
  coxeterForm_add_left : ∀ x y z : V,
    coxeterForm (x + y) z = coxeterForm x z + coxeterForm y z
  coxeterForm_smul_left : ∀ (a : ℝ) (x y : V),
    coxeterForm (a • x) y = a * coxeterForm x y
  coxeterForm_zero_right : ∀ x : V, coxeterForm x 0 = 0
  coxeterForm_add_right : ∀ x y z : V,
    coxeterForm x (y + z) = coxeterForm x y + coxeterForm x z
  coxeterForm_smul_right : ∀ (a : ℝ) (x y : V),
    coxeterForm x (a • y) = a * coxeterForm x y
  coxeterForm_symmetric : ∀ x y : V, coxeterForm x y = coxeterForm y x
  coxeterForm_on_basis : ∀ s t : ι,
    coxeterForm (simpleRootBasis s) (simpleRootBasis t) =
      coxeterFormCoefficient (M.M s t)
  representation : W →* (V ≃ₗ[ℝ] V)
  tits_simple_reflection_formula : ∀ (s : ι) (v : V),
    representation (coxeter.simple s) v =
      v - (((2 : ℝ) * coxeterForm v (simpleRootBasis s)) • simpleRootBasis s)
  dualAction : W →* (Module.Dual ℝ V ≃ₗ[ℝ] Module.Dual ℝ V)
  dualAction_apply : ∀ (w : W) (x : Module.Dual ℝ V) (v : V),
    (dualAction w x) v = x ((representation w⁻¹) v)

attribute [instance] TitsConeData.addCommGroup TitsConeData.module

namespace TitsConeData


variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]


abbrev DualSpace (D : TitsConeData ι M W) : Type uV :=
  Module.Dual ℝ D.V


noncomputable def simpleRoot (D : TitsConeData ι M W) (s : ι) : D.V :=
  D.simpleRootBasis s


def pair (D : TitsConeData ι M W) (v : D.V) (x : D.DualSpace) : ℝ :=
  x v


def closedFundamentalChamber (D : TitsConeData ι M W) : Set D.DualSpace :=
  {x : D.DualSpace | ∀ s : ι, 0 ≤ D.pair (D.simpleRoot s) x}



def face (D : TitsConeData ι M W) (I : Set ι) : Set D.DualSpace :=
  {x : D.DualSpace |
    (∀ s : ι, s ∈ I → D.pair (D.simpleRoot s) x = 0) ∧
      ∀ s : ι, s ∉ I → 0 < D.pair (D.simpleRoot s) x}


def translateSet (D : TitsConeData ι M W) (w : W) (A : Set D.DualSpace) :
    Set D.DualSpace :=
  D.dualAction w '' A


def translatedFace (D : TitsConeData ι M W) (w : W) (I : Set ι) :
    Set D.DualSpace :=
  D.translateSet w (D.face I)


def titsCone (D : TitsConeData ι M W) : Set D.DualSpace :=
  {x : D.DualSpace | ∃ w : W, x ∈ D.translateSet w D.closedFundamentalChamber}


def CoxeterFormPositiveSemidefinite (D : TitsConeData ι M W) : Prop :=
  ∀ v : D.V, 0 ≤ D.coxeterForm v v


def CoxeterFormPositiveDefinite (D : TitsConeData ι M W) : Prop :=
  D.CoxeterFormPositiveSemidefinite ∧
    ∀ v : D.V, v ≠ 0 → 0 < D.coxeterForm v v




def IsAffine (D : TitsConeData ι M W) : Prop :=
  CoxeterDiagramConnected M ∧
    D.CoxeterFormPositiveSemidefinite ∧
      ¬ D.CoxeterFormPositiveDefinite


def IsInCoxeterRadical (D : TitsConeData ι M W) (v : D.V) : Prop :=
  ∀ y : D.V, D.coxeterForm v y = 0




def IsPositiveNullRoot (D : TitsConeData ι M W) (v₀ : D.V) : Prop :=
  D.IsInCoxeterRadical v₀ ∧
    (∀ s : ι, 0 < D.simpleRootBasis.repr v₀ s) ∧
      ∀ v : D.V, D.IsInCoxeterRadical v → ∃ a : ℝ, v = a • v₀


def affineSlice (D : TitsConeData ι M W) (v₀ : D.V) : Set D.DualSpace :=
  {x : D.DualSpace | D.pair v₀ x = 1}



def affineSliceFaceUnion (D : TitsConeData ι M W) (v₀ : D.V) :
    Set D.DualSpace :=
  {x : D.DualSpace |
    x ∈ D.affineSlice v₀ ∧ ∃ w : W, ∃ I : Set ι, x ∈ D.translatedFace w I}




def SliceTranslatedFacesDisjointOrEqual
    (D : TitsConeData ι M W) (v₀ : D.V) : Prop :=
  ∀ (w₁ w₂ : W) (I J : Set ι),
    ((D.translatedFace w₁ I ∩ D.affineSlice v₀) ∩
        (D.translatedFace w₂ J ∩ D.affineSlice v₀)).Nonempty →
      D.translatedFace w₁ I ∩ D.affineSlice v₀ =
        D.translatedFace w₂ J ∩ D.affineSlice v₀


end TitsConeData

variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]



end Autoform_Buildings_and_Classical_Groups_buildings_affineSlice_inter_titsCone_eq_univ
