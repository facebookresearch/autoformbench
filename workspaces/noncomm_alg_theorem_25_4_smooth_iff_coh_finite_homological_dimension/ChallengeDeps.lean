import Mathlib


































universe u

open CategoryTheory

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_25_4_smooth_iff_coh_finite_homological_dimension

noncomputable section








structure AlgebraicVarietyOver
    (k : Type u) [Field k] where
  X : AlgebraicGeometry.Scheme.{u}
  structureMap : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)
  locallyOfFiniteType :
    AlgebraicGeometry.LocallyOfFiniteType structureMap
  quasiCompact :
    AlgebraicGeometry.QuasiCompact structureMap
  separated :
    AlgebraicGeometry.IsSeparated structureMap








abbrev CoherentSheafOn
    {k : Type u} [Field k]
    (X : AlgebraicVarietyOver k) :
    Type (u + 1) :=
  (SheafOfModules.isFinitePresentation X.X.ringCatSheaf).FullSubcategory











structure CoherentSheafExtData
    {k : Type u} [Field k]
    (X : AlgebraicVarietyOver k) where
  [abelian : Abelian (CoherentSheafOn X)]
  [hasExt : HasExt.{u} (CoherentSheafOn X)]











def AbelianCategoryHasFiniteHomologicalDimension
    (C : Type (u + 1)) [Category.{u} C] [Abelian C] [HasExt.{u} C] :
    Prop :=
  ∃ d : ℕ,
    ∀ n : ℕ, d < n →
      ∀ F G : C,
        ∀ e : Abelian.Ext F G n, e = 0







def CoherentSheavesHaveFiniteHomologicalDimension
    {k : Type u} [Field k]
    {X : AlgebraicVarietyOver k}
    (D : CoherentSheafExtData X) :
    Prop :=
  letI := D.abelian
  letI := D.hasExt
  AbelianCategoryHasFiniteHomologicalDimension (CoherentSheafOn X)



end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_25_4_smooth_iff_coh_finite_homological_dimension
