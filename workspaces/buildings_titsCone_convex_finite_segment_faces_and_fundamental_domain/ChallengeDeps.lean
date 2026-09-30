import Mathlib

set_option warningAsError false
















universe uι uW uV

namespace Autoform_Buildings_and_Classical_Groups_buildings_titsCone_convex_finite_segment_faces_and_fundamental_domain





noncomputable def coxeterFormCoefficient (m : ℕ) : ℝ :=
  if m = 0 then -1 else -Real.cos (Real.pi / (m : ℝ))








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



def specialSubgroup (D : TitsConeData ι M W) (I : Set ι) : Subgroup W :=
  Subgroup.closure (D.coxeter.simple '' I)


def translateSet (D : TitsConeData ι M W) (w : W) (A : Set D.DualSpace) :
    Set D.DualSpace :=
  D.dualAction w '' A


def translatedFace (D : TitsConeData ι M W) (w : W) (I : Set ι) :
    Set D.DualSpace :=
  D.translateSet w (D.face I)



def titsCone (D : TitsConeData ι M W) : Set D.DualSpace :=
  {x : D.DualSpace | ∃ w : W, x ∈ D.translateSet w D.closedFundamentalChamber}


def closedSegment (D : TitsConeData ι M W) (x y : D.DualSpace) :
    Set D.DualSpace :=
  {z : D.DualSpace | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = (1 - t) • x + t • y}



def IsConvexCone (D : TitsConeData ι M W) (U : Set D.DualSpace) : Prop :=
  (0 : D.DualSpace) ∈ U ∧
    ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
      ∀ x : D.DualSpace, x ∈ U →
        ∀ y : D.DualSpace, y ∈ U → a • x + b • y ∈ U



def SegmentMeetsOnlyFinitelyManyFaces (D : TitsConeData ι M W) : Prop :=
  ∀ x y : D.DualSpace, x ∈ D.titsCone → y ∈ D.titsCone →
    {A : Set D.DualSpace |
      ∃ w : W, ∃ I : Set ι,
        A = D.translatedFace w I ∧ (D.closedSegment x y ∩ A).Nonempty}.Finite



def IsFundamentalDomainForTitsCone (D : TitsConeData ι M W) : Prop :=
  ∀ u : D.DualSpace, u ∈ D.titsCone →
    ∃! c : D.DualSpace,
      c ∈ D.closedFundamentalChamber ∧ ∃ w : W, D.dualAction w u = c


end TitsConeData

section

variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]



end

end Autoform_Buildings_and_Classical_Groups_buildings_titsCone_convex_finite_segment_faces_and_fundamental_domain
