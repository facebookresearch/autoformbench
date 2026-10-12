/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib














noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace Autoform_Algebraic_Topology_I_alg_top_proposition162_vanishing_above_dimension

abbrev ZModCat := ModuleCat.{0} ℤ







abbrev SingCC (X : TopCat) : ChainComplex ZModCat ℕ :=
  ((singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).obj X







abbrev SingCCMap {X Y : TopCat} (f : X ⟶ Y) : SingCC X ⟶ SingCC Y :=
  (((singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).map f)







abbrev SingHomology (X : TopCat) (q : ℕ) : ZModCat :=
  (SingCC X).homology q







abbrev SingHomologyMap {X Y : TopCat} (f : X ⟶ Y) (q : ℕ) :
    SingHomology X q ⟶ SingHomology Y q :=
  HomologicalComplex.homologyMap (SingCCMap f) q












abbrev CWSkeleton {X : TopCat} (c : X.CWComplex) (k : ℕ) : TopCat :=
  c.F.obj (k + 1)








abbrev CWSkeletonToSpace {X : TopCat} (c : X.CWComplex) (k : ℕ) :
    CWSkeleton c k ⟶ X :=
  c.incl.app (k + 1)









abbrev CWSkeletonHomology {X : TopCat} (c : X.CWComplex) (k q : ℕ) :
    ZModCat :=
  SingHomology (CWSkeleton c k) q










abbrev CWSkeletonHomologyToSpace {X : TopCat} (c : X.CWComplex) (k q : ℕ) :
    CWSkeletonHomology c k q ⟶ SingHomology X q :=
  SingHomologyMap (CWSkeletonToSpace c k) q












def HasDimensionAtMost {X : TopCat} (c : X.CWComplex) (d : ℕ) : Prop :=
  IsIso (CWSkeletonToSpace c d)





end Autoform_Algebraic_Topology_I_alg_top_proposition162_vanishing_above_dimension

end
