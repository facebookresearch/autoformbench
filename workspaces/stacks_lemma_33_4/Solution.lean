import Mathlib
import Submission

open CategoryTheory
open CategoryTheory.Pseudofunctor
open TopologicalSpace

universe u v w

theorem lemma_33_4 {X : TopCat.{w}} {ι : Type v}
    (U : ι → Opens X)
    (hU : (⨆ i, U i) = ⊤) :
    let J := Opens.grothendieckTopology X
    let f : (i : ι) → U i ⟶ (⊤ : Opens X) :=
      fun i => homOfLE le_top
    ((J.overPullback (Type (max u v w)) (⊤ : Opens X) ⋙
    (J.pseudofunctorOver (Type (max u v w))).toDescentData f :
      TopCat.Sheaf (Type (max u v w)) X ⥤
        (J.pseudofunctorOver (Type (max u v w))).DescentData f)).IsEquivalence := by
  exact Submission.lemma_33_4.{u, v, w} U hU
