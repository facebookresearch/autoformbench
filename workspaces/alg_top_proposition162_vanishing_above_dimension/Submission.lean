


import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Submission.Helpers
import ChallengeDeps














namespace Submission

open _root_.Autoform_Algebraic_Topology_I_alg_top_proposition162_vanishing_above_dimension
noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_proposition162_vanishing_above_dimension

































theorem proposition162
    {X : TopCat} (c : X.CWComplex) (k q : ℕ) :
    (k < q → IsZero (CWSkeletonHomology c k q)) ∧
      (k > q → IsIso (CWSkeletonHomologyToSpace c k q)) := by
  sorry









theorem proposition162_vanishing
    {X : TopCat} (c : X.CWComplex) (k q : ℕ)
    (hkq : k < q) :
    IsZero (CWSkeletonHomology c k q) :=
  (proposition162 c k q).1 hkq









theorem proposition162_stability
    {X : TopCat} (c : X.CWComplex) (k q : ℕ)
    (hqk : q < k) :
    IsIso (CWSkeletonHomologyToSpace c k q) :=
  (proposition162 c k q).2 hqk











theorem proposition162_vanishing_above_dimension
    {X : TopCat} (c : X.CWComplex) (d q : ℕ)
    (hdim : HasDimensionAtMost c d)
    (hdq : d < q) :
    IsZero (SingHomology X q) := by
  sorry

end Autoform_Algebraic_Topology_I_alg_top_proposition162_vanishing_above_dimension

end

end Submission
