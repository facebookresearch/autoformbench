


import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Submission.Helpers
import ChallengeDeps


































namespace Submission

open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_theorem_25_4_smooth_iff_coh_finite_homological_dimension
universe u

open CategoryTheory

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_25_4_smooth_iff_coh_finite_homological_dimension

noncomputable section













theorem coherentSheafExtData_exists
    {k : Type u} [Field k]
    (X : AlgebraicVarietyOver k) :
    Nonempty (CoherentSheafExtData X) := by
  sorry




noncomputable def coherentSheafExtData
    {k : Type u} [Field k]
    (X : AlgebraicVarietyOver k) :
    CoherentSheafExtData X :=
  Classical.choice (coherentSheafExtData_exists X)

















theorem theorem_25_4_smooth_iff_coh_finite_homological_dimension
    (k : Type u) [Field k] [PerfectField k]
    (X : AlgebraicVarietyOver k) :
    AlgebraicGeometry.Smooth X.structureMap ↔
      CoherentSheavesHaveFiniteHomologicalDimension
        (coherentSheafExtData X) := by
  sorry

end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_25_4_smooth_iff_coh_finite_homological_dimension

end Submission
